import json
import pprint
import threading
import time
from copy import copy
from enum import Enum
from functools import lru_cache
from threading import Lock
from datetime import timezone, datetime, timedelta
from urllib.parse import urlencode

import pytz
from typing import Any, Dict, List, Set

from vnpy.event.engine import EventEngine
from vnpy.trader.database import BaseDatabase, get_database
from vnpy.trader.gateway import BaseGateway
from vnpy.trader.constant import (
    Interval,
    Status,
    Direction,
    Exchange, Offset, OptionType
)
from vnpy.trader.object import (
    AccountData,
    CancelRequest,
    OrderRequest,
    PositionData,
    SubscribeRequest,
    OrderType,
    OrderData,
    ContractData,
    Product,
    TickData,
    TradeData,
    HistoryRequest,
    BarData, AtmData
)
from vnpy.trader.event import EVENT_TIMER, EVENT_ATM

from vnpy_websocket import WebsocketClient
from vnpy_rest import Request, RestClient

# 中国时区
CHINA_TZ = pytz.timezone("Asia/Shanghai")
JAPAN_TZ = pytz.timezone("Asia/Tokyo")

KBS_PutOptions  = 1
KBS_CallOptions = 2

RKT_PutOptions  = "P"
RKT_CallOptions = "C"

# 限月指定
NK225_CODE                = "NK225mini"  # 日经225mini
NK225_MONTH               = 2601  # future
NK225_MONTH2               = 2602  # future
SYMBOL_NK225_MONTH         = f"nk-{NK225_MONTH}"
SYMBOL_NK225_MONTH2        = f"nk-{NK225_MONTH2}"


NK225_OP_CODE             = "NK225op"  # 日経225オプション
NK225_OP_MONTH            = 2601  # option
NK225_OP_MONTH2            = 2602  # option

NK225_WEEKLY_OP_CODE      = "NK225weeklyop"  # 日经225weekly
NK225_WEEKLY_OP_MONTH     = 2601  # option weekly
NK225_WEEKLY_OP_WEEK      = 1       # option weekly

NK225_OP_STRIKE_SCOPE = 9000
NK225_OP_STRIKE_SCOPE2 = 9000

# REST API地址
REST_HOST: str = "http://localhost:18080"

# Websocket API地址
WEBSOCKET_HOST: str = "ws://localhost:18080/kabusapi/websocket"

RAKUTEN_RSS_REST_HOST: str = "http://localhost:8766"

RAKUTEN_RSS_WEBSOCKET_HOST: str = "ws://localhost:8765/ws/"

# 委托类型映射
ORDERTYPE_VT2KBS = {
    OrderType.LIMIT: "20",   # 指値
    OrderType.MARKET: "120"  # 成行
}

ORDERTYPE_KBS2VT = {v: k for k, v in ORDERTYPE_VT2KBS.items()}

# 买卖方向映射
DIRECTION_VT2KBS = {
    Direction.LONG: "2",
    Direction.SHORT: "1"
}

DIRECTION_KBS2VT = {v: k for k, v in DIRECTION_VT2KBS.items()}

# 新規返済映射(sendorder)
OFFSET_VT2KBS = {
    Offset.OPEN: "1",  # 1: 新規
    Offset.CLOSE: "2"  # 2: 返済
}

OFFSET_KBS2VT = {v: k for k, v in OFFSET_VT2KBS.items()}

# 新規返済映射(query_order)
CASHMARGIN_VT2KBS = {
    Offset.OPEN: 2,  # 2: 新規
    Offset.CLOSE: 3  # 3: 返済
}

CASHMARGIN_KBS2VT = {v: k for k, v in CASHMARGIN_VT2KBS.items()}

# 商品类型映射

# 期权类型映射
OPTIONTYPE_KBS2VT: dict[int, OptionType] = {
    KBS_CallOptions: OptionType.CALL,
    KBS_PutOptions: OptionType.PUT
}

OPTIONTYPE_RKT2VT: dict[str, OptionType] = {
    RKT_CallOptions: OptionType.CALL,
    RKT_PutOptions: OptionType.PUT
}

# 窗口长度映射
WINDOW_VT2KBS = {
    Interval.MINUTE: 60,
    Interval.HOUR: 3600,
    Interval.DAILY: 86400,
    Interval.WEEKLY: 604800
}

WINDOW_FTX2VT = {v: k for k, v in WINDOW_VT2KBS.items()}

# 历史数据长度限制映射
LMIMIT_VT2KBS = {
    Interval.MINUTE: 950,
    Interval.HOUR: 1400,
    Interval.DAILY: 1400,
    Interval.WEEKLY: 1400
}


# 鉴权类型
class Security(Enum):
    NONE: int = 0
    SIGNED: int = 1

# 合约数据全局缓存字典
symbol_contract_map: dict[str, ContractData] = {}

# 銘柄コード数据全局缓存字典
SYMBOL_VT2KBS: dict[str, str] = {}

def symbol_kbs2vt(d, symbol_kbs):
    keys = [k for k, v in d.items() if v == symbol_kbs]
    if keys:
        return keys[0]
    return None


class KabusGateway(BaseGateway):
    """vn.py用于对接Kabu Station的交易接口"""

    default_name: str = "KBS"

    default_setting: Dict[str, Any] = {
        "API Key": ""
    }

    exchanges: Exchange = [Exchange.JPX]

    def __init__(self, event_engine: EventEngine, gateway_name: str = "KBS") -> None:
        """构造函数"""
        super().__init__(event_engine, gateway_name)

        self.ws_rakuten_api: "RakutenWebsocketApi" = RakutenWebsocketApi(self)
        self.rest_rakuten_api: "RakutenRestApi" = RakutenRestApi(self)
        self.ws_api: "KabusWebsocketApi" = KabusWebsocketApi(self)
        self.rest_api: "KabusRestApi" = KabusRestApi(self)

        self.orders: Dict[str, OrderData] = {}
        self.order_id: Dict[str, str] = {}
        self.orderid_kbs_orderid_map: Dict[str, str] = {}
        self.kbs_orderid_orderid_map: Dict[str, str] = {}
        self.trade_ids: Set = set()
        self.order_query_time = (datetime.now(JAPAN_TZ) + timedelta(minutes=-1)).strftime("%Y%m%d%H%M%S")
        # self.order_query_time = None

    def connect(self, setting: dict) -> None:
        """连接交易接口"""
        key: str = setting["API Key"]

        self.rest_rakuten_api.connect(key)
        self.ws_rakuten_api.connect(key)
        self.rest_api.connect(key)
        self.ws_api.connect(key)

        self.init_ping()

    def subscribe(self, req: SubscribeRequest) -> None:
        """订阅行情"""
        self.ws_api.subscribe(req)

    def unsubscribe(self, req: SubscribeRequest) -> None:
        """取消行情订阅"""
        self.ws_api.unsubscribe(req)

    def send_order(self, req: OrderRequest) -> None:
        """委托下单"""
        return self.rest_api.send_order(req)

    def cancel_order(self, req: CancelRequest) -> None:
        """委托撤单"""
        self.rest_api.cancel_order(req)

    def query_account(self) -> None:
        """查询资金"""
        self.rest_api.query_account()

    def query_position(self) -> None:
        """查询持仓"""
        self.rest_api.query_position()

    def query_orders(self) -> None:
        """查询未成交委托"""
        self.rest_api.query_order()

    def on_order(self, order: OrderData) -> None:
        """推送委托数据"""
        self.orders[order.orderid] = copy(order)
        super().on_order(order)

    def get_order(self, orderid: str) -> OrderData:
        """查询委托数据"""
        return self.orders.get(orderid, None)

    def query_history(self, req: HistoryRequest) -> List[BarData]:
        """查询历史数据"""
        return self.rest_api.query_history(req)

    def close(self) -> None:
        """关闭连接"""
        self.rest_api.stop()
        self.ws_api.stop()
        self.rest_rakuten_api.stop()
        self.ws_rakuten_api.stop()
        self.rest_rakuten_api.stop_query_order()
        self.rest_rakuten_api.join_query_order()
        self.rest_api.stop_query_order()
        self.rest_api.join_query_order()

        # self.ws_api.stop_tickdata_thread()
        # self.ws_api.join_tickdata_thread()

    def process_timer_event(self, event) -> None:
        """定时事件处理"""
        self.count += 1
        if self.count < 15:
            return
        self.count = 0
        self.ws_api.ping()
        # self.ws_rakuten_api.ping()

    def init_ping(self) -> None:
        """初始化心跳"""
        self.count: int = 0
        self.event_engine.register(EVENT_TIMER, self.process_timer_event)


class KabusRestApi(RestClient):
    """FTX的REST API"""

    def __init__(self, gateway: KabusGateway) -> None:
        """构造函数"""
        super().__init__()

        self.gateway: KabusGateway = gateway
        self.gateway_name: str = gateway.gateway_name

        self.ws_api: KabusWebsocketApi = self.gateway.ws_api
        self.ws_rakuten_api: RakutenWebsocketApi = self.gateway.ws_rakuten_api

        # 保存用户登陆信息
        self.key: str = ""
        self.token: str = ""

        # 确保生成的orderid不发生冲突
        self.order_count: int = 1_000_000
        self.order_count_lock: Lock = Lock()
        self.connect_time: int = 0

        self.contract_inited: bool = False

        self.active: bool = False
        self.thread_order: threading.Thread = None
        self.lock: threading.Lock = threading.Lock()

        self.trading_future_symbol: str = "nk-YYMM"
        self.atm_price: int = 0
        self.atm_price2: int = 0
        self.option_board_data: dict = {}
        self.eris_call_match: dict = {'symbol': None, 'strike': None, 'delta': None, 'diff': float('inf'), 'impv': None}
        self.eris_put_match: dict = {'symbol': None, 'strike': None, 'delta': None, 'diff': float('inf'), 'impv': None}
        # 日経225先物・オプション取得リスト
        self.symbol_settings: list = [
            f"{NK225_CODE}-{NK225_MONTH}",
            f"{NK225_CODE}-{NK225_MONTH2}"
        ]
        self.queried_symbol_settings: list = []
        self.thread_symbol: threading.Thread = None
        self.gateway.event_engine.register(EVENT_ATM, self.process_atm_event)

    def process_atm_event(self, event) -> None:
        """ATM价格变动事件处理"""
        atm: AtmData = event.data
        print(f"[OK] process_atm_event: {atm}")
        atm_price: int = atm.atm_strike
        chain_symbol: str = atm.chain_symbol
        self.gateway.write_log(f"[OK] {chain_symbol} ATM価格: {atm_price}")
        if self.atm_price != atm_price:
            self.gateway.write_log(f"[OK] {chain_symbol} ATM価格変更: {self.atm_price} -> {atm_price}")
            self.atm_price = atm_price
            self.create_option_symbol_settings(
                NK225_OP_CODE,
                NK225_OP_MONTH,
                self.atm_price,
                NK225_OP_STRIKE_SCOPE
            )
            self.create_option_symbol_settings(
                NK225_OP_CODE,
                NK225_OP_MONTH2,
                self.atm_price,
                NK225_OP_STRIKE_SCOPE2
            )


    def create_option_symbol_settings(self, symbol_code: str, month: int, atm_price: int, strike_scope: int) -> None:
        """生成option symbol settings"""
        # 生成 call option symbol strike_price in range [atm_price, atm_price + strike_scope] with interval 500
        for strike_price in range(atm_price - 1000, atm_price + strike_scope + 1, 1000):
            symbol_setting = f"{symbol_code}-{month}-C-{strike_price}"
            if symbol_setting not in self.queried_symbol_settings:
                self.symbol_settings.append(symbol_setting)
            # strike_price with interval 500
            strike_price += 500
            symbol_setting = f"{symbol_code}-{month}-C-{strike_price}"
            if symbol_setting not in self.queried_symbol_settings:
                self.gateway.rest_rakuten_api.symbol_settings.append(symbol_setting)

        # 生成 put option symbol strike_price in range [atm_price, atm_price - strike_scope] with interval -500
        for strike_price in range(atm_price + 1000, atm_price - strike_scope -1, -1000):
            symbol_setting = f"{symbol_code}-{month}-P-{strike_price}"
            if symbol_setting not in self.queried_symbol_settings:
                self.symbol_settings.append(symbol_setting)
            # strike_price with interval 500
            strike_price -= 500
            symbol_setting = f"{symbol_code}-{month}-P-{strike_price}"
            if symbol_setting not in self.queried_symbol_settings:
                self.gateway.rest_rakuten_api.symbol_settings.append(symbol_setting)


    def sign(self, request: Request) -> Request:
        """生成FTX签名"""
        if request.data:
            request.data = json.dumps(request.data).encode('utf8')
        if request.headers is None:
            request.headers = {'Content-Type': 'application/json'}
        if self.token:
            request.headers['X-API-KEY'] = self.token

        return request

    def connect(
        self,
        key: str
    ) -> None:
        """连接REST服务器"""
        self.key = key

        # 生成本地委托号
        self.connect_time = (
            int(datetime.now().strftime("%y%m%d%H%M%S")) * self.order_count
        )

        self.init(REST_HOST)
        self.start()

        print("[__] REST API启动")
        self.gateway.write_log("[__] REST API启动")

        self.query_token()

    def query_token(self) -> None:
        """トークン発行"""
        data: dict = {"APIPassword": self.key}

        path: str = "/kabusapi/token"

        self.add_request(
            method="POST",
            path=path,
            callback=self.on_query_token,
            data=data,
            on_failed = self.on_query_token_failed
        )
        print("[__] query_token")

    def on_query_token(self, data: dict, request: Request) -> None:
        """トークン発行"""
        print(f"[OK] on_query_token: {data}")
        if data["ResultCode"] == 0:
            self.token = data["Token"]
            self.gateway.write_log("[OK] トークン取得")

            self.unregister_all()

            self.query_account()

            self.query_position()

            # Start the thread to process incoming data
            self.active: bool = True
            self.thread_symbol = threading.Thread(target=self.run_query_symbol_thread)
            self.thread_symbol.start()
            self.thread_order = threading.Thread(target=self.run_query_order_position_thread)
            self.thread_order.start()
        else:
            self.gateway.write_log("[NG] トークン取得")

    def unregister_all(self):
        """全銘柄登録解除"""
        path: str = "/kabusapi/unregister/all"

        self.add_request(
            method="PUT",
            path=path,
            callback=self.on_unregister_all,
            on_failed=self.on_unregister_all_failed
        )
        print("[__] unregister_all")

    def on_query_token_failed(self, status_code: int, request: Request):
        """トークン発行失敗"""
        msg = f"[NG] トークン発行, 状态码：{status_code}，信息：{request.response.text}"
        print(msg)
        self.gateway.write_log(msg)

    def query_symbol(self, symbol_setting: str) -> None:
    # def query_symbol(self, code: str, month: int, op_weekly: int=None, op_type: str=None, op_strike_price: int=None) -> None:
        """銘柄コード取得"""
        # 'http://localhost:18080/kabusapi/symbolname/{future|option|minioptionweekly}'
        # OptionCode - NK225op:日経225オプション、NK225miniop:日経225ミニオプション
        # PutOrCall - P: PUT, C: CALL
        # Result
        # 200 OK
        # {'Symbol': '130195526', 'SymbolName': '日経平均ミニオプション 25/05 2週限 プット 35500'}
        # HTTP Error 400: Bad Request
        # {'Code': 4002001, 'Message': '銘柄が見つからない'}
        # split the string into parts
        parts = symbol_setting.split("-")
        code = parts[0]  # NK225mini, NK225op
        month = int(parts[1])  # 2506

        # DerivMonth: 限月はyyyyMM形式で指定します。0を指定した場合、直近限月となります。
        params = {'DerivMonth': 200000 + month} # 202506
        if code in ['NK225', 'NK225mini', 'NK225micro']:
            params['FutureCode']  = code
            cmd = 'future'
            symbol = f"nk-{month}"
            self.trading_future_symbol = symbol
        elif code in ['NK225op', 'NK225miniop']:
            op_type               = parts[2]   # P, C
            op_strike_price       = int(parts[3])
            params['OptionCode']  = code
            params['PutOrCall']   = op_type
            params['StrikePrice'] = op_strike_price
            cmd = 'option'
            # symbol = f"nk-{month}-{op_type}-{op_strike_price}"
        elif code == 'NK225weeklyop':
            op_weekly       = int(parts[2])  # 3: 3週限
            op_type         = parts[3]       # P
            op_strike_price = int(parts[4])
            params['DerivWeekly'] = op_weekly
            params['PutOrCall']   = op_type
            params['StrikePrice'] = op_strike_price
            cmd = 'minioptionweekly'
            # symbol = f"nk-{month}-{op_weekly}-{op_type}-{op_strike_price}"

        path: str = f"/kabusapi/symbolname/{cmd}?{urlencode(params)}"

        self.add_request(
            method="GET",
            path=path,
            callback=self.on_query_symbol,
            on_failed=self.on_query_symbol_failed,
            extra=symbol_setting
        )
        print(f"[__] symbol: {symbol_setting}")
        self.gateway.write_log("[__] symbol: " + symbol_setting)

    def run_query_symbol_thread(self) -> None:
        """Function run in the thread"""
        self.gateway.write_log("[__] Symbol取得スレッド起動")
        symbol_setting = self.symbol_settings.pop(0)
        self.query_symbol(symbol_setting)
        while self.active:
            time.sleep(0.2)
            if self.symbol_settings:
                symbol_setting = self.symbol_settings.pop(0)
                self.query_symbol(symbol_setting)
        self.gateway.write_log("[OK] Symbol取得スレッド終了")


    def run_query_order_position_thread(self) -> None:
        """Function run in the thread"""
        self.gateway.write_log("[OK] 注文・ポジション照会スレッド起動")
        start = datetime.now()
        while self.active:
            time.sleep(0.2) # 0.2s  5件/秒
            # 銘柄リスト取得成功まで待機（sleep繰り返し）
            if not self.contract_inited:
                continue
            self.query_order()      # 未成交委托查询のレスポンスは、5回/秒
            # self.query_account()      # 取引余力（先物）のレスポンスは、5回/秒
            # 発注APIは5件/秒、取引余力APIや情報API、銘柄登録APIは10件/秒, PUSH間引き間隔は400ms
            end = datetime.now()
            if (end - start).seconds >= 1.6:
                self.query_position() # 持仓查询のレスポンスは、1回/秒
                start = end
        self.gateway.write_log("[OK] 注文・ポジション照会スレッド終了")

    def stop_query_order(self) -> None:
        """Stop query_order"""
        if not self.active:
            return
        self.active = False

    def join_query_order(self) -> None:
        """Join to wait the thread exit loop"""
        if self.thread_symbol and self.thread_symbol.is_alive():
            self.thread_symbol.join()
        self.thread_symbol = None
        if self.thread_order and self.thread_order.is_alive():
            self.thread_order.join()
        self.thread_order = None


    def query_account(self) -> None:
        """口座の取引余力（先物）取得"""
        # path: str = "/kabusapi/wallet/future"
        """口座の取引余力（オプション）取得"""
        path: str = "/kabusapi/wallet/option"

        self.add_request(
            method="GET",
            path=path,
            callback=self.on_query_account,
            on_failed = self.on_failed
        )
        print(f"[__] account")

    def query_position(self) -> None:
        """ポジション照会"""
        path: str = "/kabusapi/positions"

        self.add_request(
            method="GET",
            path=path,
            callback=self.on_query_position,
            on_failed=self.on_position_failed
        )

    def query_order(self) -> None:
        """注文約定照会"""
        # 'http://localhost:18080/kabusapi/orders?product=3&state=5'
        # product - 0:すべて、1:現物、2:信用、3:先物、4:OP
        # details - true:追加情報を出力する、false:追加情報を出力しない
        # state - 1:待機（発注待機）、2:処理中（発注送信中）、3:処理済（発注済・訂正済）、4:訂正取消送信中、5:終了（発注エラー・取消済・全約定・失効・期限切れ）
        # updtime yyyyMMddHHmmss （例：20250207010000）指定された更新日時以降（指定日時含む）に更新された注文のみレスポンスします。
        # symbol - 銘柄コード（例：160060023）日経225マイクロ先物 25/06
        symbol_ksb = SYMBOL_VT2KBS.get(self.trading_future_symbol, None)
        if symbol_ksb is None:
            self.gateway.write_log(f"[NG] 注文約定照会 銘柄コード変換：{self.trading_future_symbol}")
            return

        params = {'product': 3, 'details': 'false', 'symbol': symbol_ksb}
        if self.gateway.order_query_time is not None:
            params['updtime'] = self.gateway.order_query_time
        # 3秒前の時間を取得, 作为下一次查询的时间起点
        query_time = (datetime.now(JAPAN_TZ) + timedelta(seconds=-3)).strftime("%Y%m%d%H%M%S")

        path: str = f"/kabusapi/orders?{urlencode(params)}"

        self.add_request(
            method="GET",
            path=path,
            callback=self.on_query_order,
            on_failed=self.on_query_order_failed,
            extra=query_time
        )

    def query_contract(self, symbol: str) -> None:
        """銘柄情報取得"""
        # 'http://localhost:18080/kabusapi/symbol/160060023@2?addinfo=false'
        symbol_ksb = SYMBOL_VT2KBS.get(symbol, None)
        if symbol_ksb is None:
            self.gateway.write_log(f"[NG] 銘柄情報取得 銘柄コード変換：{symbol}")
            return

        params = {'addinfo': 'false'}
        market = '2' # 1: 東証、3: 名証、5: 福証、6: 札証、2: 日通し、23: 日中、24: 夜間

        path: str = f"/kabusapi/symbol/{symbol_ksb}@{market}?{urlencode(params)}"

        self.add_request(
            method="GET",
            path=path,
            callback=self.on_query_contract,
            on_failed=self.on_query_contract_failed,
            extra=symbol
        )
        print(f"[__] contract: {symbol}")
        self.gateway.write_log("[__] contract: " + symbol)

    def register_symbol(self, symbol: str):
        """Tickデータ受信登録"""
        symbol_ksb = SYMBOL_VT2KBS.get(symbol, None)
        if symbol_ksb is None:
            self.gateway.write_log(f"[NG] Tickデータ受信登録 銘柄コード変換：{symbol}")
            return

        # symbol = '160060023'
        market = '2' # 1: 東証、3: 名証、5: 福証、6: 札証、2: 日通し、23: 日中、24: 夜間
        data = {'Symbols':
            [
                {'Symbol': symbol_ksb, 'Exchange': market}
            ]}

        path: str = "/kabusapi/register"

        self.add_request(
            method="PUT",
            path=path,
            callback=self.on_register_symbol,
            data=data,
            on_failed=self.on_register_failed,
            extra=symbol
        )
        print(f"[__] register: {symbol}")
        self.gateway.write_log("[__] register: " + symbol)

    def _new_order_id(self) -> int:
        """生成本地委托号"""
        with self.order_count_lock:
            self.order_count += 1
            return self.order_count

    def send_order(self, req: OrderRequest) -> str:
        """委托下单"""
        # ①スクリプト→②kabuｽﾃｰｼｮﾝAPI→③kabuｽﾃｰｼｮﾝ→④カブコム取引システム→⑤取引所
        # ①～⑤、⑤～①の完了でVNPYにResponseを返す
        # 秒間リクエスト上限: 発注系リクエスト=5件/秒、情報系リクエスト=10件/秒
        # リクエストをかけリスポンスを受けるまで100～150msec程度かかる
        # 取引システム一件当たりの処理時間は、約１０ｍｓ～５０ｍｓ程度
        symbol_ksb = SYMBOL_VT2KBS.get(req.symbol, None)
        if symbol_ksb is None:
            self.gateway.write_log(f"[NG] 委托下单 銘柄コード変換：{req.symbo}")
            return

        # 生成本地委托号
        orderid: str = str(self.connect_time + self._new_order_id())

        # 推送提交中事件
        order: OrderData = req.create_order_data(
            orderid,
            self.gateway_name
        )
        self.gateway.on_order(order)

        data: dict = {
            "Symbol": symbol_ksb,
            "Exchange": 2, # 2: 日通し、23: 日中、24: 夜間、32: SOR日通し、33: SOR日中、34: SOR夜間
            "TradeType": OFFSET_VT2KBS[req.offset], # 1: 新規、2: 返済
            "TimeInForce": 1, # 1: FAS(（Fill and Store）)、2: FAK(Fill and Kill)、3: FOK(Fill or Kill). FASは、部分約定
            "side": DIRECTION_VT2KBS[req.direction], # (str型) 売買区分（1:売、2:買）.
            "Qty": req.volume, # 発注数量
            "FrontOrderType": 20, # 18: 引成（派生）、20: 指値、28: 引指（派生）、30: 逆指値、120: 成行 # ORDERTYPE_VT2KBS[req.type]
            "Price": req.price, # 値段
            "ExpireDay": 0, # 注文有効期限 yyyyMMdd形式. 0: 当日中有効
            # 'ReverseLimitOrder': { # 逆指値注文情報
            #                        'TriggerPrice': 26010,
            #                        'UnderOver': 2, #1.以下 2.以上
            #                        'AfterHitOrderType': 1, #1.成行 2.指値
            #                        'AfterHitPrice': 0
            #                     }
        }

        # 返済建玉指定
        # "ClosePositionOrder": 2, # 決済順序 2: 日付（新しい順）、損益（高い順）
        # 0: 日付（古い順）、損益（高い順）
        # 1: 日付（古い順）、損益（低い順）
        # 2: 日付（新しい順）、損益（高い順）
        # 3: 日付（新しい順）、損益（低い順）
        # 4: 損益（高い順）、日付（古い順）
        # 5: 損益（高い順）、日付（新しい順）
        # 6: 損益（低い順）、日付（古い順）
        # 7: 損益（低い順）、日付（新しい順）
        # "ClosePositions": [{
        #                     "HoldID": "1234", # 返済建玉ID
        #                     "Qty": 1          # 返済建玉数量
        #                   }],
        if req.offset == Offset.CLOSE:
            data["ClosePositionOrder"] = 2

        path: str = "/kabusapi/sendorder/future"

        self.add_request(
            method="POST",
            path=path,
            callback=self.on_send_order,
            data=data,
            extra=order,
            on_error=self.on_send_order_error,
            on_failed=self.on_send_order_failed
        )

        # gateway_name.orderid
        return order.vt_orderid

    def cancel_order(self, req: CancelRequest) -> None:
        """委托撤单"""
        # 取得委托号对应的KBS订单号
        kbs_orderid = self.gateway.orderid_kbs_orderid_map.get(req.orderid, None)
        if kbs_orderid is None:
            self.gateway.write_log(f"[NG] 找不到委托号对应的KBS订单号：{req.orderid}")
            return

        data: dict = {"OrderID": kbs_orderid}
        path: str = "/kabusapi/cancelorder"

        order: OrderData = self.gateway.get_order(req.orderid)

        self.add_request(
            method="PUT",
            path=path,
            callback=self.on_cancel_order,
            data=data,
            on_failed=self.on_cancel_failed,
            extra=order
        )

    def on_unregister_all(self, data: dict, request: Request) -> None:
        """全銘柄登録解除成功"""
        self.gateway.write_log("[OK] 全銘柄登録解除")

    def on_unregister_all_failed(self, status_code: int, request: Request) -> None:
        """全銘柄登録解除失敗"""
        msg = f"[NG] 全銘柄登録解除，状态码：{status_code}，信息：{request.response.text}"
        self.gateway.write_log(msg)


    def get_symbol_from_setting(self, symbol_setting: str) -> str:
        """从symbol_command中获取symbol"""
        parts = symbol_setting.split("-")
        parts[0] = "nk"
        # partsを結合してsymbolを作成
        symbol = "-".join(parts)
        return symbol

    def on_query_symbol(self, data: dict, request: Request) -> None:
        """銘柄コード取得成功"""
        symbol_setting = request.extra # ex. NK225op-2512-P-47000
        self.queried_symbol_settings.append(symbol_setting)

        symbol_kbs = data["Symbol"] # ex. 180247018
        symbol = self.get_symbol_from_setting(symbol_setting) # ex. nk-2512-P-47000
        SYMBOL_VT2KBS[symbol] = symbol_kbs
        msg = f"[OK] symbol: {symbol_setting} -> {symbol_kbs}"
        self.gateway.write_log(msg)
        print(f"on_query_symbol: {symbol_setting} {data}")
        # 銘柄情報取得
        self.query_contract(symbol)
        self.register_symbol(symbol)


    def on_query_symbol_failed(self, status_code: int, request: Request):
        """銘柄コード取得失敗"""
        symbol_setting = request.extra
        msg = f"[NG] symbol: {symbol_setting}，状态码：{status_code}，信息：{request.response.text}"
        print(msg)
        self.gateway.write_log(msg)
        # "Code":4002001 "Message":"銘柄が見つからない"
        # strike_price with interval 500 is not found, exit without retry
        if request.response.text.find("4002001") != -1:
            return
        # retry query symbol
        time.sleep(0.2)
        self.query_symbol(symbol_setting)


    def on_query_account(self, data: dict, request: Request) -> None:
        """资金查询回报"""
        print(f"on_query_account: {data}")
        account: AccountData = AccountData(
            accountid=self.gateway_name,
            # balance=data["FutureTradeLimit"],
            balance=data["OptionBuyTradeLimit"],
            gateway_name=self.gateway_name
        )
        # account.available = data["FutureTradeLimit"]
        account.available = data["OptionBuyTradeLimit"]
        account.frozen = account.balance - account.available

        if account.balance:
            self.gateway.on_account(account)
        self.gateway.write_log("[OK] 口座の取引余力取得")

    def on_query_position(self, data: dict, request: Request) -> None:
        """ポジション照会成功"""
        print(f"on_query_position: {data}")
        for d in data:
            pnl = d['ProfitLoss'] if d['ProfitLoss'] is not None else 0
            symbol_kbs = d["Symbol"]
            symbol = symbol_kbs2vt(SYMBOL_VT2KBS, symbol_kbs)
            if symbol is None:
                self.gateway.write_log(f"[NG] ポジション照会 銘柄コード変換：{symbol_kbs}")
                continue

            position: PositionData = PositionData(
                symbol=symbol,
                exchange=Exchange.JPX,
                direction=DIRECTION_KBS2VT[d["Side"]],  # 売買区分（1:売、2:買）
                volume=d['LeavesQty'],  # 残数量（保有数量）
                frozen=d['HoldQty'],  # 拘束数量（返済のために拘束されている数量）
                price=d['Price'],  # 値段
                pnl=pnl,  # 評価損益額
                gateway_name=self.gateway_name
            )
            self.gateway.on_position(position)

        # self.gateway.write_log("持仓信息查询成功")

    def on_position_failed(self, status_code: int, request: Request) -> None:
        """ポジション照会"""
        msg = f"[NG] ポジション照会，状态码：{status_code}，信息：{request.response.text}"
        print(msg)
        self.gateway.write_log(msg)

    def on_query_order(self, data: dict, request: Request) -> None:
        """注文約定照会"""
        print(f"on_query_order: {data}")
        self.gateway.order_query_time = request.extra
        for d in data:
            # print(f"order: {d}")
            # 先判断订单状态
            # state - 1: 待機（発注待機）、2: 処理中（発注送信中）、3: 処理済（発注済・訂正済）、4: 訂正取消送信中、5: 終了（発注エラー・取消済・全約定・失効・期限切れ）
            current_status = d["OrderState"]
            size = d["OrderQty"]                             # 発注数量
            filled_size = d["CumQty"]                        # 約定数量
            if current_status == 1:                          # Pending Order in KBS (逆指値注文), 待機（発注待機）
                status = Status.SUBMITTING
            elif current_status == 2:                        # Sending Order (KBS -> JPX), 処理中（発注送信中）
                status = Status.NOTTRADED
            elif (current_status == 3) & (filled_size == 0): # Processed Order by JPX (指値注文), 処理済（発注済・訂正済）
                status = Status.NOTTRADED
            elif (current_status == 4) & (filled_size == 0):  # Sending Cancel Order (KBS -> JPX), 訂正取消送信中
                status = Status.NOTTRADED
            elif (current_status == 3) & (size != filled_size):
                status = Status.PARTTRADED
            elif (current_status == 5) & (filled_size == 0):  # 終了（発注エラー・取消済・全約定・失効・期限切れ）
                status = Status.CANCELLED
            elif (current_status == 5) & (filled_size > 0):   # 終了（発注エラー・取消済・全約定・失効・期限切れ）
                status = Status.ALLTRADED
            else:
                status = "other status"

            kbs_orderid = d["ID"]
            orderid = self.gateway.kbs_orderid_orderid_map.get(kbs_orderid, None)
            if orderid is None:
                # KSB注文番号作为orderid使用
                orderid = kbs_orderid
                self.gateway.orderid_kbs_orderid_map[orderid] = kbs_orderid
                self.gateway.kbs_orderid_orderid_map[kbs_orderid] = orderid

            symbol_kbs = d["Symbol"]
            symbol = symbol_kbs2vt(SYMBOL_VT2KBS, symbol_kbs)
            if symbol is None:
                self.gateway.write_log(f"[NG] 注文約定照会 銘柄コード変換：{symbol_kbs}")
                continue

            order: OrderData = OrderData(
                orderid=orderid,
                symbol=symbol,
                exchange=Exchange.JPX,
                price=float(d["Price"]),
                volume=float(d["OrderQty"]),
                type=OrderType.LIMIT,                   # 指値注文 (limit order)に固定
                direction=DIRECTION_KBS2VT[d["Side"]],
                offset=CASHMARGIN_KBS2VT[d["CashMargin"]], # 2: 新規(OPEN) 3: 返済(CLOSE)
                traded=d["CumQty"],
                status=status,
                datetime=change_datetime(d["RecvTime"]),
                gateway_name=self.gateway_name
            )
            self.gateway.on_order(order)

            # kbs_orderid作为tradeid使用
            if status == Status.ALLTRADED:
                if kbs_orderid in self.gateway.trade_ids:
                    continue
                self.gateway.trade_ids.add(kbs_orderid)

                trade: TradeData = TradeData(
                    symbol=order.symbol,
                    exchange=order.exchange,
                    direction=order.direction,
                    orderid=orderid,
                    tradeid=kbs_orderid,
                    offset=order.offset,
                    price=order.price,
                    volume=order.volume,
                    datetime=order.datetime,
                    gateway_name=order.gateway_name
                )
                self.gateway.on_trade(trade)

        # self.gateway.write_log("委托信息查询成功")

    def on_query_order_failed(self, status_code: int, request: Request):
        """注文約定照会"""
        msg = f"[NG] 注文約定照会，状态码：{status_code}，信息：{request.response.text}"
        print(msg)
        self.gateway.write_log(msg)

    def on_query_contract(self, data: dict, request: Request):
        """銘柄情報取得成功"""
        print(f"on_query_contract: {data}")
        symbol = request.extra
        contract: ContractData = ContractData(
            symbol=symbol,
            exchange=Exchange.JPX,
            name=data["SymbolName"],
            pricetick=5.0,
            size=1,
            min_volume=data["TradingUnit"],
            product=Product.FUTURES,  # 先物に固定
            net_position=False,
            history_data=False,
            gateway_name=self.gateway_name,
        )

        # 期权相关
        if data.get("StrikePrice", None) is not None:
            product_id   = "nk_o"              # 'nk_o'
            deriv_month  = data["DerivMonth"]  # '2025/06'
            deriv_month  = deriv_month[2:4] + deriv_month[5:7]   # '2506'
            deriv_weekly = data.get("DerivWeekly", None)
            # 获取期权标的
            underlyer    = f"nk-{deriv_month}"                   # nk-2506
            # 期权周限月
            # if deriv_weekly is not None:
            #     underlyer = f"{underlyer}-{deriv_weekly}"        # nk-2505-3
            contract.product = Product.OPTION                    # 期权
            contract.option_portfolio = product_id               # ProductID:         nk_o            # (portfolio)
            contract.option_underlying = underlyer               # UnderlyingInstrID: nk-2506         # (chain)
            contract.option_type = OPTIONTYPE_KBS2VT.get(data["PutOrCall"], None)
            contract.option_strike = data["StrikePrice"]
            contract.option_index = str(data["StrikePrice"])
            contract.option_listed = datetime.strptime(str(data["TradeStart"]), "%Y%m%d")
            contract.option_expiry = datetime.strptime(str(data["TradeEnd"]), "%Y%m%d")
        else:
            contract.product = Product.FUTURES
            deriv_month  = data["DerivMonth"]  # '2025/06'
            deriv_month  = deriv_month[2:4] + deriv_month[5:7]   # '2506'
            underlyer    = f"nk-{deriv_month}"                   # nk-2506
            contract.option_underlying = underlyer               # UnderlyingInstrID: nk-2506  # (chain)


        self.gateway.on_contract(contract)

        symbol_contract_map[contract.symbol] = contract

        self.gateway.write_log("[OK] contract: " + contract.symbol)
        # Tickデータ受信登録
        # time.sleep(0.2)
        # self.register_symbol(symbol)

    def on_query_contract_failed(self, status_code: int, request: Request):
        """銘柄情報取得失敗"""
        symbol = request.extra
        msg = f"[NG] contract: {symbol}，状态码：{status_code}，信息：{request.response.text}"
        print(msg)
        self.gateway.write_log(msg)
        # retry query contract
        time.sleep(0.2)
        self.query_contract(symbol)

    def on_register_symbol(self, data: dict, request: Request) -> None:
        """Tickデータ受信登録成功"""
        print(f"on_register_symbol: count={len(data['RegistList'])}")
        # for s in data["RegistList"]:
        #     pprint.pprint(s)

        symbol = request.extra
        msg = f"[OK] register: {symbol} (count={len(data['RegistList'])})"
        print(msg)
        self.gateway.write_log(msg)

    def on_register_failed(self, status_code: int, request: Request) -> None:
        """Tickデータ受信登録失敗"""
        symbol = request.extra
        msg = f"[NG] register: {symbol}，状态码：{status_code}，信息：{request.response.text}"
        print(msg)
        self.gateway.write_log(msg)
        # retry register symbol
        time.sleep(0.2)
        self.register_symbol(symbol)

    def on_send_order(self, data: dict, request: Request) -> None:
        """委托下单回报"""
        if data["Result"] == 0:
            order: OrderData = request.extra
            self.gateway.orderid_kbs_orderid_map[order.orderid] = data["OrderId"]
            self.gateway.kbs_orderid_orderid_map[data["OrderId"]] = order.orderid
            order.status = Status.NOTTRADED
            self.gateway.on_order(order)

    def on_send_order_error(
        self, exception_type: type, exception_value: Exception, tb, request: Request
    ) -> None:
        """委托下单回报函数报错回报"""
        order: OrderData = request.extra
        order.status = Status.REJECTED
        self.gateway.on_order(order)

        if not issubclass(exception_type, ConnectionError):
            self.on_error(exception_type, exception_value, tb, request)

    def on_send_order_failed(self, status_code: str, request: Request) -> None:
        """委托下单失败服务器报错回报"""
        order: OrderData = request.extra
        order.status = Status.REJECTED
        self.gateway.on_order(order)

        msg: str = f"[NG] 委托，orderid: {order.orderid}, 状态码：{status_code}，信息：{request.response.text}"
        self.gateway.write_log(msg)

    def on_cancel_order(self, data: dict, request: Request) -> None:
        """委托撤单回报"""
        if data["Result"] == 0:
            order: OrderData = request.extra
            order.status = Status.CANCELLED
            self.gateway.on_order(order)

    def on_cancel_failed(self, status_code: str, request: Request):
        """撤单回报函数报错回报"""
        if request.extra:
            order = request.extra

        kbs_orderid = self.gateway.orderid_kbs_orderid_map.get(order.orderid, None)
        msg = f"[NG] 撤单，orderid: {order.orderid}, kbs: {kbs_orderid}, 状态码：{status_code}，信息：{request.response.text}"
        self.gateway.write_log(msg)

    def on_failed(self, status_code: int, request: Request) -> None:
        """失败回报"""
        msg = f"[NG] 状态码：{status_code}，信息：{request.response.text}"
        print(msg)
        self.gateway.write_log(msg)

    def query_history(self, req: HistoryRequest) -> List[BarData]:
        """查询历史数据"""
        self.gateway.write_log("[NG] KBS不支持历史数据查询")
        history: List[BarData] = []
        return history



class KabusWebsocketApi(WebsocketClient):
    """FTX交易Websocket API"""

    def __init__(self, gateway: KabusGateway) -> None:
        """构造函数"""
        super().__init__()

        self.gateway: KabusGateway = gateway
        self.gateway_name: str = gateway.gateway_name

        self.subscribed: Dict[str, SubscribeRequest] = {}

        self.start_time = datetime.utcnow().date()
        self.count = 0

        # Database历史Tick数据模拟实盘行情
        self.history_data: list = []
        self.active: bool = False
        self.thread: threading.Thread = None
        self.lock: threading.Lock = threading.Lock()

    def connect(
        self,
        api_key: str
    ) -> None:
        """连接Websocket交易频道"""
        self.api_key = api_key
        self.init(WEBSOCKET_HOST)
        self.start()

        self.gateway.write_log("[__] 時価Websocket 接続")

        # Database历史Tick数据模拟实盘行情
        # self.load_data()
        # self.active: bool = True
        # self.thread = threading.Thread(target=self.run_tickdata_thread)
        # self.thread.start()

    def on_connected(self) -> None:
        """连接成功回报"""
        self.gateway.write_log("[OK] 時価Websocket 接続")

        self.ping()

        for req in list(self.subscribed.values()):
            self.resubscribe(req)


    def on_disconnected(self) -> None:
        """"""
        self.gateway.write_log("[OK] 時価Websocket 切断")


    def subscribe(self, req: SubscribeRequest) -> None:
        """订阅行情"""
        if req.symbol not in symbol_contract_map:
            self.gateway.write_log(f"[NG] 找不到该合约代码{req.symbol}")
            return

        if req.vt_symbol in self.subscribed:
            return

        self.subscribed[req.vt_symbol] = req


    def unsubscribe(self, req: SubscribeRequest) -> None:
        """取消订阅行情"""
        if req.symbol not in symbol_contract_map:
            self.gateway.write_log(f"[NG] 找不到该合约代码{req.symbol}")
            return

        if req.vt_symbol in self.subscribed:
            self.subscribed.pop(req.vt_symbol)

    def resubscribe(self, req: SubscribeRequest) -> None:
        """重连后订阅行情"""
        if req.symbol not in symbol_contract_map:
            self.gateway.write_log(f"[NG] 找不到该合约代码{req.symbol}")
            return

        self.subscribed[req.vt_symbol] = req


    def ping(self) -> None:
        """发送心跳"""
        self.send_packet({'op': 'ping'})


    def on_packet(self, packet: Any) -> None:
        """推送数据回报"""
        # print(f"on_packet: {packet}")
        if not packet or not isinstance(packet, dict):
            return

        symbol_kbs = packet.get('Symbol')
        if not symbol_kbs:
            return

        symbol = symbol_kbs2vt(SYMBOL_VT2KBS, symbol_kbs)
        if symbol is None:
            self.gateway.write_log(f"[NG] 推送数据 銘柄コード変換：{symbol_kbs}")
            return

        # if symbol != self.gateway.rest_api.trading_future_symbol:
        #     print(f"on_packet: {packet}")
        last_price = None
        bid_price_1 = packet.get("Buy1", {}).get("Price")
        bid_volume_1 = packet.get("Buy1", {}).get("Qty")
        ask_price_1 = packet.get("Sell1", {}).get("Price")
        ask_volume_1 = packet.get("Sell1", {}).get("Qty")
        if bid_price_1 and ask_price_1 and bid_volume_1 and ask_volume_1:
            total_volume = bid_volume_1 + ask_volume_1
            if total_volume:
                last_price = bid_price_1 + (ask_price_1 - bid_price_1) * bid_volume_1 / total_volume
        if last_price is None:
            last_price = packet.get("CurrentPrice")

        volume = packet.get("TradingVolume")
        if volume is None:
            volume = 0
        turnover = packet.get("TradingValue")
        if turnover is None:
            turnover = 0

        open_price = packet.get("OpeningPrice")
        if open_price is None:
            open_price = last_price
        high_price = packet.get("HighPrice")
        if high_price is None:
            high_price = last_price
        low_price = packet.get("LowPrice")
        if low_price is None:
            low_price = last_price

        tick: TickData = TickData(
            gateway_name=self.gateway_name,
            symbol=symbol,
            exchange=Exchange.JPX,
            datetime=datetime.now(JAPAN_TZ),

            name=packet.get("SymbolName"),
            volume=volume,
            turnover=turnover,
            open_price=open_price,
            high_price=high_price,
            low_price=low_price,
            pre_close=packet.get("PreviousClose"),
            last_price=last_price,
            last_volume=volume,

            ask_price_1=packet.get("Sell1", {}).get("Price"),
            ask_volume_1=packet.get("Sell1", {}).get("Qty"),
            ask_price_2=packet.get("Sell2", {}).get("Price"),
            ask_volume_2=packet.get("Sell2", {}).get("Qty"),
            ask_price_3=packet.get("Sell3", {}).get("Price"),
            ask_volume_3=packet.get("Sell3", {}).get("Qty"),
            ask_price_4=packet.get("Sell4", {}).get("Price"),
            ask_volume_4=packet.get("Sell4", {}).get("Qty"),
            ask_price_5=packet.get("Sell5", {}).get("Price"),
            ask_volume_5=packet.get("Sell5", {}).get("Qty"),

            bid_price_1=packet.get("Buy1", {}).get("Price"),
            bid_volume_1=packet.get("Buy1", {}).get("Qty"),
            bid_price_2=packet.get("Buy2", {}).get("Price"),
            bid_volume_2=packet.get("Buy2", {}).get("Qty"),
            bid_price_3=packet.get("Buy3", {}).get("Price"),
            bid_volume_3=packet.get("Buy3", {}).get("Qty"),
            bid_price_4=packet.get("Buy4", {}).get("Price"),
            bid_volume_4=packet.get("Buy4", {}).get("Qty"),
            bid_price_5=packet.get("Buy5", {}).get("Price"),
            bid_volume_5=packet.get("Buy5", {}).get("Qty"),
        )

        # Handle future to update ATM price
        if symbol == SYMBOL_NK225_MONTH and not self.gateway.rest_api.atm_price:
            if tick.last_price:
                atm_price = round(tick.last_price / 1000) * 1000
                self.gateway.rest_api.atm_price = atm_price
                self.gateway.write_log(f"[OK] 1限月 ATM {symbol}: {tick.last_price} -> {atm_price}")
                self.gateway.rest_api.create_option_symbol_settings(
                    NK225_OP_CODE,
                    NK225_OP_MONTH,
                    atm_price,
                    NK225_OP_STRIKE_SCOPE
                )

        if symbol == SYMBOL_NK225_MONTH2 and not self.gateway.rest_api.atm_price2:
            if tick.last_price:
                atm_price = round(tick.last_price / 1000) * 1000
                self.gateway.rest_api.atm_price2 = atm_price
                self.gateway.write_log(f"[OK] 2限月 ATM {symbol}: {tick.last_price} -> {atm_price}")
                self.gateway.rest_api.create_option_symbol_settings(
                    NK225_OP_CODE,
                    NK225_OP_MONTH2,
                    atm_price,
                    NK225_OP_STRIKE_SCOPE2
                )

        # 过滤还没有收到合约数据前的行情推送
        contract: ContractData = symbol_contract_map.get(tick.symbol, None)
        if not contract:
            return

        if tick.last_price:
            self.gateway.on_tick(copy(tick))

    # Database历史Tick数据模拟实盘行情
    def load_data(self) -> None:
        data: List[TickData] = self.load_tick_data(
            symbol='160060023',
            exchange=Exchange.JPX,
            start=datetime(2025, 2, 6),
            end=datetime(2025, 2, 7)
        )
        self.history_data.extend(data)

    @lru_cache(maxsize=999)
    def load_tick_data(
            self,
            symbol: str,
            exchange: Exchange,
            start: datetime,
            end: datetime
    ) -> List[TickData]:
        """"""
        database: BaseDatabase = get_database()

        return database.load_tick_data(
            symbol, exchange, start, end
        )

    def run_tickdata_thread(self) -> None:
        """Function run in the thread"""
        self.gateway.write_log("[OK] Database历史Tick数据模拟实盘行情线程启动")
        total_size: int = len(self.history_data)
        batch_size: int = max(int(total_size / 10), 1)
        for ix, i in enumerate(range(0, total_size, batch_size)):
            batch_data: list = self.history_data[i: i + batch_size]
            for data in batch_data:
                if self.active:
                    data.datetime = datetime.now(JAPAN_TZ)
                    data.gateway_name = self.gateway_name
                    if data.last_price:
                        self.gateway.on_tick(copy(data))
                    time.sleep(0.2) # 0.2s  5件/秒
                else:
                    break
            if not self.active:
                break

        self.gateway.write_log("[OK] Database历史Tick数据模拟实盘行情线程结束")

    def stop_tickdata_thread(self) -> None:
        """Stop tickdata_thread"""
        if not self.active:
            return
        self.active = False

    def join_tickdata_thread(self) -> None:
        """Join to wait the thread exit loop"""
        if self.thread and self.thread.is_alive():
            self.thread.join()
        self.thread = None


class RakutenRestApi(RestClient):
    """Rakuten的REST API"""

    def __init__(self, gateway: KabusGateway) -> None:
        """构造函数"""
        super().__init__()

        self.gateway: KabusGateway = gateway
        self.gateway_name: str = gateway.gateway_name

        self.ws_rakuten_api: RakutenWebsocketApi = self.gateway.ws_rakuten_api

        # 保存用户登陆信息
        self.key: str = ""
        self.token: str = ""

        # 确保生成的orderid不发生冲突
        self.order_count: int = 2_000_000
        self.order_count_lock: Lock = Lock()
        self.connect_time: int = 0

        self.active: bool = False
        self.thread_order: threading.Thread = None
        self.lock: threading.Lock = threading.Lock()

        self.trading_future_symbol: str = "nk-YYMM"
        self.atm_price: int = 0
        self.atm_price2: int = 0
        self.option_board_data: dict = {}

        # 日経225先物・オプション取得リスト
        self.symbol_settings: list = [
            f"{NK225_CODE}-{NK225_MONTH}",
            f"{NK225_CODE}-{NK225_MONTH2}"
        ]
        self.queried_symbol_settings: list = []
        self.thread_symbol: threading.Thread = None
        self.gateway.event_engine.register(EVENT_ATM, self.process_atm_event)

    def process_atm_event(self, event) -> None:
        """ATM价格变动事件处理"""
        atm: AtmData = event.data
        print(f"[OK] rakuten process_atm_event: {atm}")
        atm_price: int = atm.atm_strike
        chain_symbol: str = atm.chain_symbol
        self.gateway.write_log(f"[OK] rakuten {chain_symbol} ATM価格: {atm_price}")
        if self.atm_price != atm_price:
            self.gateway.write_log(f"[OK] rakuten {chain_symbol} ATM価格変更: {self.atm_price} -> {atm_price}")
            self.atm_price = atm_price
            self.create_option_symbol_settings(
                NK225_OP_CODE,
                NK225_OP_MONTH,
                self.atm_price,
                NK225_OP_STRIKE_SCOPE
            )
            self.create_option_symbol_settings(
                NK225_OP_CODE,
                NK225_OP_MONTH2,
                self.atm_price,
                NK225_OP_STRIKE_SCOPE2
            )


    def create_option_symbol_settings(self, symbol_code: str, month: int, atm_price: int, strike_scope: int) -> None:
        """生成option symbol settings"""
        # 生成 call option symbol strike_price in range [atm_price, atm_price + strike_scope] with interval 500
        for strike_price in range(atm_price - 1000, atm_price + strike_scope + 1, 1000):
            symbol_setting = f"{symbol_code}-{month}-C-{strike_price}"
            if symbol_setting not in self.queried_symbol_settings:
                self.symbol_settings.append(symbol_setting)
            # strike_price with interval 500
            strike_price += 500
            symbol_setting = f"{symbol_code}-{month}-C-{strike_price}"
            if symbol_setting not in self.queried_symbol_settings:
                self.symbol_settings.append(symbol_setting)

        # 生成 put option symbol strike_price in range [atm_price, atm_price - strike_scope] with interval -500
        for strike_price in range(atm_price + 1000, atm_price - strike_scope -1, -1000):
            symbol_setting = f"{symbol_code}-{month}-P-{strike_price}"
            if symbol_setting not in self.queried_symbol_settings:
                self.symbol_settings.append(symbol_setting)
            # strike_price with interval 500
            strike_price -= 500
            symbol_setting = f"{symbol_code}-{month}-P-{strike_price}"
            if symbol_setting not in self.queried_symbol_settings:
                self.symbol_settings.append(symbol_setting)



    def sign(self, request: Request) -> Request:
        """生成FTX签名"""
        if request.data:
            request.data = json.dumps(request.data).encode('utf8')
        if request.headers is None:
            request.headers = {'Content-Type': 'application/json'}
        if self.token:
            request.headers['X-API-KEY'] = self.token

        return request

    def connect(
        self,
        key: str
    ) -> None:
        """连接REST服务器"""
        self.key = key

        # 生成本地委托号
        self.connect_time = (
            int(datetime.now().strftime("%y%m%d%H%M%S")) * self.order_count
        )

        self.init(RAKUTEN_RSS_REST_HOST)
        self.start()

        self.gateway.write_log("[__] rakuten REST API启动")
        print("[__] rakuten REST API启动")

        self.query_token()

    def query_token(self) -> None:
        """トークン発行"""
        data: dict = {"APIPassword": self.key}

        path: str = "/rakutenapi/token"

        self.add_request(
            method="POST",
            path=path,
            callback=self.on_query_token,
            data=data,
            on_failed = self.on_query_token_failed
        )
        print("[__] rakuten query_token")

    def on_query_token(self, data: dict, request: Request) -> None:
        """トークン発行"""
        print(f"rakuten on_query_token: {data}")
        if data["ResultCode"] == 0:
            self.token = data["Token"]
            self.gateway.write_log("[OK] rakuten トークン取得: {self.token}")

            self.unregister_all()

            # Start the thread to process incoming data
            self.active: bool = True
            self.thread_symbol = threading.Thread(target=self.run_query_symbol_thread)
            self.thread_symbol.start()
        else:
            self.gateway.write_log("[NG] rakuten トークン取得")

    def on_query_token_failed(self, status_code: int, request: Request):
        """トークン発行失敗"""
        msg = f"[NG] rakuten トークン発行, 状态码：{status_code}，信息：{request.response.text}"
        print(msg)
        self.gateway.write_log(msg)


    def unregister_all(self):
        """全銘柄登録解除"""
        path: str = "/rakutenapi/unregister/all"

        self.add_request(
            method="PUT",
            path=path,
            callback=self.on_unregister_all,
            on_failed=self.on_unregister_all_failed
        )
        print("[__] rakuten unregister_all")


    def on_unregister_all(self, data: dict, request: Request) -> None:
        """全銘柄登録解除成功"""
        print(f"rakuten on_unregister_all: {data}")
        self.gateway.write_log("[OK] rakuten 全銘柄登録解除")

    def on_unregister_all_failed(self, status_code: int, request: Request) -> None:
        """全銘柄登録解除失敗"""
        msg = f"[NG] rakuten 全銘柄登録解除，状态码：{status_code}，信息：{request.response.text}"
        print(msg)
        self.gateway.write_log(msg)

    def query_symbol(self, symbol_setting: str) -> None:
    # def query_symbol(self, code: str, month: int, op_weekly: int=None, op_type: str=None, op_strike_price: int=None) -> None:
        """銘柄コード取得"""
        # 'http://localhost:18080/kabusapi/symbolname/{future|option|minioptionweekly}'
        # OptionCode - NK225op:日経225オプション、NK225miniop:日経225ミニオプション
        # PutOrCall - P: PUT, C: CALL
        # Result
        # 200 OK
        # {'Symbol': '130195526', 'SymbolName': '日経平均ミニオプション 25/05 2週限 プット 35500'}
        # HTTP Error 400: Bad Request
        # {'Code': 4002001, 'Message': '銘柄が見つからない'}
        # split the string into parts
        parts = symbol_setting.split("-")
        code = parts[0]  # NK225mini, NK225op
        month = parts[1]  # 2506

        # DerivMonth: 限月はyyyyMM形式で指定します。0を指定した場合、直近限月となります。
        deriv_month = month[0:2] + "-" + month[2:4]  # '26-01'
        if code in ['NK225', 'NK225mini', 'NK225micro']:
            op_type               = "F"        # Future
            op_strike_price       = "0"
        elif code in ['NK225op', 'NK225miniop']:
            op_type               = parts[2]   # P, C
            op_strike_price       = parts[3]

        name = deriv_month + "-" + op_type + "-" + op_strike_price
        path: str = f"/rakutenapi/symbolname/{name}"

        self.add_request(
            method="GET",
            path=path,
            callback=self.on_query_symbol,
            on_failed=self.on_query_symbol_failed,
            extra=symbol_setting
        )
        print(f"[__] symbol: {symbol_setting}")
        self.gateway.write_log("[__] symbol: " + symbol_setting)

    def run_query_symbol_thread(self) -> None:
        """Function run in the thread"""
        self.gateway.write_log("[__] rakuten Symbol取得スレッド起動")
        # symbol_setting = self.symbol_settings.pop(0)
        # self.query_symbol(symbol_setting)
        while self.active:
            time.sleep(0.2)
            if self.symbol_settings:
                symbol_setting = self.symbol_settings.pop(0)
                self.query_symbol(symbol_setting)
        self.gateway.write_log("[OK] rakuten Symbol取得スレッド終了")

    def stop_query_order(self) -> None:
        """Stop query_order"""
        if not self.active:
            return
        self.active = False

    def join_query_order(self) -> None:
        """Join to wait the thread exit loop"""
        if self.thread_symbol and self.thread_symbol.is_alive():
            self.thread_symbol.join()
        self.thread_symbol = None


    def get_symbol_from_setting(self, symbol_setting: str) -> str:
        """从symbol_command中获取symbol"""
        parts = symbol_setting.split("-")
        parts[0] = "nk"
        # partsを結合してsymbolを作成
        symbol = "-".join(parts)
        return symbol

    def on_query_symbol(self, data: dict, request: Request) -> None:
        """銘柄コード取得成功"""
        symbol_setting = request.extra # ex. NK225op-2512-P-47000
        self.queried_symbol_settings.append(symbol_setting)

        symbol_kbs = data["Symbol"] # ex. 180247018
        symbol = self.get_symbol_from_setting(symbol_setting) # ex. nk-2512-P-47000
        SYMBOL_VT2KBS[symbol] = symbol_kbs
        msg = f"[OK] rakuten symbol: {symbol_setting} -> {symbol_kbs}"
        self.gateway.write_log(msg)
        print(f"rakuten on_query_symbol: {symbol_setting} {data}")
        # 銘柄情報取得
        self.query_contract(symbol)
        self.register_symbol(symbol)


    def on_query_symbol_failed(self, status_code: int, request: Request):
        """銘柄コード取得失敗"""
        symbol_setting = request.extra
        msg = f"[NG] rakuten symbol: {symbol_setting}，状态码：{status_code}，信息：{request.response.text}"
        print(msg)
        self.gateway.write_log(msg)
        # "Code":4002001 "Message":"銘柄が見つからない"
        # strike_price with interval 500 is not found, exit without retry
        if request.response.text.find("4002001") != -1:
            return
        # retry query symbol
        time.sleep(0.2)
        self.query_symbol(symbol_setting)


    def query_contract(self, symbol: str) -> None:
        """銘柄情報取得"""
        # 'http://localhost:18080/kabusapi/symbol/160060023@2?addinfo=false'
        symbol_ksb = SYMBOL_VT2KBS.get(symbol, None)
        if symbol_ksb is None:
            self.gateway.write_log(f"[NG] rakuten 銘柄情報取得 銘柄コード変換：{symbol}")
            return

        path: str = f"/rakutenapi/symbol/{symbol_ksb}"

        self.add_request(
            method="GET",
            path=path,
            callback=self.on_query_contract,
            on_failed=self.on_query_contract_failed,
            extra=symbol
        )
        print(f"[__] rakuten query_contract: {symbol}")
        self.gateway.write_log("[__] rakuten contract: " + symbol)

    def on_query_contract(self, data: dict, request: Request):
        """銘柄情報取得成功"""
        print(f"rakuten on_query_contract: {data}")
        symbol = request.extra
        contract: ContractData = ContractData(
            symbol=symbol,
            exchange=Exchange.JPX,
            name=data["SymbolName"],
            pricetick=5.0,
            size=1,
            min_volume=float(data["TradingUnit"]),
            product=Product.FUTURES,  # 先物に固定
            net_position=False,
            history_data=False,
            gateway_name=self.gateway_name,
        )

        # 期权相关
        strike_price = float(data.get("StrikePrice", 0))
        if strike_price:
            product_id   = "nk_o"              # 'nk_o'
            deriv_month  = data["DerivMonth"]  # '26-01'
            deriv_month  = deriv_month[0:2] + deriv_month[3:5]   # '2601'
            deriv_weekly = data.get("DerivWeekly", None) # No Data
            # 获取期权标的
            underlyer    = f"nk-{deriv_month}"                   # nk-2601
            # 期权周限月
            # if deriv_weekly is not None:
            #     underlyer = f"{underlyer}-{deriv_weekly}"        # nk-2505-3
            contract.product = Product.OPTION                    # 期权
            contract.option_portfolio = product_id               # ProductID:         nk_o            # (portfolio)
            contract.option_underlying = underlyer               # UnderlyingInstrID: nk-2506         # (chain)
            contract.option_type = OPTIONTYPE_RKT2VT.get(data["PutOrCall"], None)
            contract.option_strike = float(data["StrikePrice"])
            contract.option_index = str(data["StrikePrice"])
            contract.option_expiry = datetime.strptime(str(data["TradeEnd"]), "%Y/%m/%d")
            contract.option_listed = contract.option_expiry - timedelta(days=60)  # 60日前に設定
        else:
            contract.product = Product.FUTURES
            deriv_month  = data["DerivMonth"]  # '26-01'
            deriv_month  = deriv_month[0:2] + deriv_month[3:5]   # '2601'
            underlyer    = f"nk-{deriv_month}"                   # nk-2601
            contract.option_underlying = underlyer               # UnderlyingInstrID: nk-2601  # (chain)


        self.gateway.on_contract(contract)

        symbol_contract_map[contract.symbol] = contract

        self.gateway.write_log("[OK] rakuten contract: " + contract.symbol)
        # Tickデータ受信登録
        # time.sleep(0.2)
        # self.register_symbol(symbol)

    def on_query_contract_failed(self, status_code: int, request: Request):
        """銘柄情報取得失敗"""
        symbol = request.extra
        msg = f"[NG] rakuten contract: {symbol}，状态码：{status_code}，信息：{request.response.text}"
        print(msg)
        self.gateway.write_log(msg)
        # "Code":4002001 "Message":"銘柄が見つからない"
        # strike_price with interval 500 is not found, exit without retry
        if request.response.text.find("4002001") != -1:
            return
        # retry query contract
        time.sleep(0.2)
        self.query_contract(symbol)


    def register_symbol(self, symbol: str):
        """Tickデータ受信登録"""
        symbol_ksb = SYMBOL_VT2KBS.get(symbol, None)
        if symbol_ksb is None:
            self.gateway.write_log(f"[NG] rakuten Tickデータ受信登録 銘柄コード変換：{symbol}")
            return

        # symbol = '160060023'
        market = '2' # 1: 東証、3: 名証、5: 福証、6: 札証、2: 日通し、23: 日中、24: 夜間
        data = {'Symbols':
            [
                {'Symbol': symbol_ksb, 'Exchange': market}
            ]}

        path: str = "/rakutenapi/register"

        self.add_request(
            method="PUT",
            path=path,
            callback=self.on_register_symbol,
            data=data,
            on_failed=self.on_register_failed,
            extra=symbol
        )
        print(f"[__] rakuten register_symbol: {symbol}")
        self.gateway.write_log("[__] rakuten register: " + symbol)


    def on_register_symbol(self, data: dict, request: Request) -> None:
        """Tickデータ受信登録成功"""
        print(f"rakuten on_register_symbol: count={len(data['RegistList'])}")
        # for s in data["RegistList"]:
        #     pprint.pprint(s)

        symbol = request.extra
        self.gateway.write_log("[OK] rakuten register " + symbol + f" (count={len(data['RegistList'])})")


    def on_register_failed(self, status_code: int, request: Request) -> None:
        """Tickデータ受信登録失敗"""
        symbol = request.extra
        msg = f"[NG] rakuten register: {symbol}，状态码：{status_code}，信息：{request.response.text}"
        print(msg)
        self.gateway.write_log(msg)
        # retry register symbol
        time.sleep(0.2)
        self.register_symbol(symbol)

    def on_failed(self, status_code: int, request: Request) -> None:
        """失败回报"""
        msg = f"[NG] rakuten 状态码：{status_code}，信息：{request.response.text}"
        print(msg)
        self.gateway.write_log(msg)



class RakutenWebsocketApi(WebsocketClient):
    """Rakuten RSS交易Websocket API"""

    def __init__(self, gateway: KabusGateway) -> None:
        """构造函数"""
        super().__init__()

        self.gateway: KabusGateway = gateway
        self.gateway_name: str = gateway.gateway_name

        self.subscribed: Dict[str, SubscribeRequest] = {}

        self.start_time = datetime.utcnow().date()
        self.count = 0

        # Database历史Tick数据模拟实盘行情
        self.history_data: list = []
        self.active: bool = False
        self.thread: threading.Thread = None
        self.lock: threading.Lock = threading.Lock()

    def connect(
        self,
        api_key: str
    ) -> None:
        """连接Websocket交易频道"""
        self.api_key = api_key
        self.init(RAKUTEN_RSS_WEBSOCKET_HOST)
        self.start()

        self.gateway.write_log("[__] rakuten 時価Websocket 接続")

        # Database历史Tick数据模拟实盘行情
        # self.load_data()
        # self.active: bool = True
        # self.thread = threading.Thread(target=self.run_tickdata_thread)
        # self.thread.start()

    def on_connected(self) -> None:
        """连接成功回报"""
        self.gateway.write_log("[OK] rakuten 時価Websocket 接続")

        # self.ping()

        for req in list(self.subscribed.values()):
            self.resubscribe(req)


    def on_disconnected(self) -> None:
        """"""
        self.gateway.write_log("[OK] rakuten 時価Websocket 切断")


    def subscribe(self, req: SubscribeRequest) -> None:
        """订阅行情"""
        if req.symbol not in symbol_contract_map:
            self.gateway.write_log(f"[NG] rakuten 找不到该合约代码{req.symbol}")
            return

        if req.vt_symbol in self.subscribed:
            return

        self.subscribed[req.vt_symbol] = req


    def unsubscribe(self, req: SubscribeRequest) -> None:
        """取消订阅行情"""
        if req.symbol not in symbol_contract_map:
            self.gateway.write_log(f"[NG] rakuten 找不到该合约代码{req.symbol}")
            return

        if req.vt_symbol in self.subscribed:
            self.subscribed.pop(req.vt_symbol)

    def resubscribe(self, req: SubscribeRequest) -> None:
        """重连后订阅行情"""
        if req.symbol not in symbol_contract_map:
            self.gateway.write_log(f"[NG] rakuten 找不到该合约代码{req.symbol}")
            return

        self.subscribed[req.vt_symbol] = req


    def ping(self) -> None:
        """发送心跳"""
        self.send_packet({'op': 'ping'})


    def on_packet(self, packet: Any) -> None:
        """推送数据回报"""
        # print(f"rakuten on_packet: {packet}")

        if not packet or not isinstance(packet, dict):
            return

        symbol_kbs = packet.get('Symbol')
        if not symbol_kbs:
            return

        symbol = symbol_kbs2vt(SYMBOL_VT2KBS, symbol_kbs)
        if symbol is None:
            self.gateway.write_log(f"[NG] rakuten 推送数据 銘柄コード変換：{symbol_kbs}")
            return

        # if symbol != self.gateway.rest_api.trading_future_symbol:
        #     print(f"on_packet: {packet}")
        last_price = None
        bid_price_1  = float(packet.get("Buy1_Price"))
        bid_volume_1 = float(packet.get("Buy1_Qty"))
        ask_price_1  = float(packet.get("Sell1_Price"))
        ask_volume_1 = float(packet.get("Sell1_Qty"))
        if bid_price_1 and ask_price_1 and bid_volume_1 and ask_volume_1:
            total_volume = bid_volume_1 + ask_volume_1
            if total_volume:
                last_price = bid_price_1 + (ask_price_1 - bid_price_1) * bid_volume_1 / total_volume
        if last_price is None:
            last_price = float(packet.get("CurrentPrice"))

        volume = float(packet.get("TradingVolume"))
        turnover = float(packet.get("TradingValue"))

        open_price = float(packet.get("OpeningPrice"))
        if not open_price:
            open_price = last_price
        high_price = float(packet.get("HighPrice"))
        if not high_price:
            high_price = last_price
        low_price = float(packet.get("LowPrice"))
        if not low_price:
            low_price = last_price

        tick: TickData = TickData(
            gateway_name=self.gateway_name,
            symbol=symbol,
            exchange=Exchange.JPX,
            datetime=datetime.now(JAPAN_TZ),

            name=packet.get("SymbolName"),
            volume=volume,
            turnover=turnover,
            open_price=open_price,
            high_price=high_price,
            low_price=low_price,
            pre_close=float(packet.get("PreviousClose")),
            last_price=last_price,
            last_volume=volume,

            ask_price_1=ask_price_1,
            ask_volume_1=ask_volume_1,

            bid_price_1=bid_price_1,
            bid_volume_1=bid_volume_1,

        )

        # Handle future to update ATM price
        if symbol == SYMBOL_NK225_MONTH and not self.gateway.rest_rakuten_api.atm_price:
            if tick.last_price:
                atm_price = round(tick.last_price / 1000) * 1000
                self.gateway.rest_rakuten_api.atm_price = atm_price
                self.gateway.write_log(f"[OK] rakuten 1限月 ATM {symbol}: {tick.last_price} -> {atm_price}")
                self.gateway.rest_rakuten_api.create_option_symbol_settings(
                    NK225_OP_CODE,
                    NK225_OP_MONTH,
                    atm_price,
                    NK225_OP_STRIKE_SCOPE
                )

        if symbol == SYMBOL_NK225_MONTH2 and not self.gateway.rest_rakuten_api.atm_price2:
            if tick.last_price:
                atm_price = round(tick.last_price / 1000) * 1000
                self.gateway.rest_rakuten_api.atm_price2 = atm_price
                self.gateway.write_log(f"[OK] rakuten 2限月 ATM {symbol}: {tick.last_price} -> {atm_price}")
                self.gateway.rest_rakuten_api.create_option_symbol_settings(
                    NK225_OP_CODE,
                    NK225_OP_MONTH2,
                    atm_price,
                    NK225_OP_STRIKE_SCOPE2
                )

        # 过滤还没有收到合约数据前的行情推送
        contract: ContractData = symbol_contract_map.get(tick.symbol, None)
        if not contract:
            return

        if tick.last_price:
            self.gateway.on_tick(copy(tick))



def change_datetime(created_time: str) -> datetime:
    """更改时区"""
    # "RecvTime":"2025-02-05T03:55:01.0588722+09:00"
    # %fでは6桁までしか対応
    dt = datetime.strptime(created_time[:-7], "%Y-%m-%dT%H:%M:%S.%f")
    dt: datetime = JAPAN_TZ.localize(dt)
    return dt
    # created_time = created_time.replace(tzinfo=timezone.utc)
    # created_time = created_time.astimezone(pytz.timezone(str(CHINA_TZ)))
    # return created_time


def generate_datetime(timestamp: str) -> datetime:
    """生成时间"""
    # "CurrentPriceTime": "2025-02-05T03:09:43+09:00"
    dt = datetime.strptime(timestamp[:-6], "%Y-%m-%dT%H:%M:%S")
    # dt: datetime = datetime.strptime(str(timestamp), "%Y-%m-%dT%H:%M:%S%z")
    dt: datetime = JAPAN_TZ.localize(dt)
    return dt
