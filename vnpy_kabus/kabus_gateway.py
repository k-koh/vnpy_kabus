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
    Exchange, Offset
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
    BarData
)
from vnpy.trader.event import EVENT_TIMER

from vnpy_websocket import WebsocketClient
from vnpy_rest import Request, RestClient



# 中国时区
CHINA_TZ = pytz.timezone("Asia/Shanghai")
JAPAN_TZ = pytz.timezone("Asia/Tokyo")

# REST API地址
REST_HOST: str = "http://localhost:18080"

# Websocket API地址
WEBSOCKET_HOST: str = "ws://localhost:18080/kabusapi/websocket"

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

# 合约数据全局缓存字典
symbol_contract_map: Dict[str, ContractData] = {}


# 鉴权类型
class Security(Enum):
    NONE: int = 0
    SIGNED: int = 1


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

        # 保存用户登陆信息
        self.key: str = ""
        self.token: str = ""

        # 确保生成的orderid不发生冲突
        self.order_count: int = 1_000_000
        self.order_count_lock: Lock = Lock()
        self.connect_time: int = 0

        self.active: bool = False
        self.thread: threading.Thread = None
        self.lock: threading.Lock = threading.Lock()

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

        self.gateway.write_log("REST API启动成功")

        self.query_token()

    def query_token(self) -> None:
        """Token查询"""
        data: dict = {"APIPassword": self.key}

        path: str = "/kabusapi/token"

        self.add_request(
            method="POST",
            path=path,
            callback=self.on_query_token,
            data=data,
            on_failed = self.on_failed
        )

    def on_query_token(self, data: dict, request: Request) -> None:
        """Token查询回报"""
        print(f"on_query_token: {data}")
        if data["ResultCode"] == 0:
            self.token = data["Token"]
            self.gateway.write_log("Token查询成功")

            self.query_account()
            self.query_position()
            self.query_contract()
            self.register_symbol()

            # Start the thread to process incoming data
            self.active: bool = True
            self.thread = threading.Thread(target=self.run_query_thread)
            self.thread.start()
        else:
            self.gateway.write_log("Token查询失败")


    def run_query_thread(self) -> None:
        """Function run in the thread"""
        self.gateway.write_log("未成交委托查询线程启动")
        start = datetime.now()
        while self.active:
            self.query_order()      # 未成交委托查询のレスポンスは、5回/秒
            # self.query_account()      # 取引余力（先物）のレスポンスは、5回/秒
            # 発注APIは5件/秒、取引余力APIや情報API、銘柄登録APIは10件/秒, PUSH間引き間隔は400ms
            end = datetime.now()
            if (end - start).seconds >= 1.6:
                self.query_position() # 持仓查询のレスポンスは、1回/秒
                start = end
            time.sleep(0.2) # 0.2s  5件/秒
        self.gateway.write_log("未成交委托查询线程结束")

    def stop_query_order(self) -> None:
        """Stop query_order"""
        if not self.active:
            return
        self.active = False

    def join_query_order(self) -> None:
        """Join to wait the thread exit loop"""
        if self.thread and self.thread.is_alive():
            self.thread.join()
        self.thread = None


    def query_account(self) -> None:
        """口座の取引余力（先物）取得"""
        path: str = "/kabusapi/wallet/future"

        self.add_request(
            method="GET",
            path=path,
            callback=self.on_query_account,
            on_failed = self.on_failed
        )

    def query_position(self) -> None:
        """查询持仓"""
        path: str = "/kabusapi/positions"

        self.add_request(
            method="GET",
            path=path,
            callback=self.on_query_position,
            on_failed=self.on_position_failed
        )

    def query_order(self) -> None:
        """查询未成交委托"""
        # 'http://localhost:18080/kabusapi/orders?product=3&state=5'
        # product - 0:すべて、1:現物、2:信用、3:先物、4:OP
        # details - true:追加情報を出力する、false:追加情報を出力しない
        # state - 1:待機（発注待機）、2:処理中（発注送信中）、3:処理済（発注済・訂正済）、4:訂正取消送信中、5:終了（発注エラー・取消済・全約定・失効・期限切れ）
        # updtime yyyyMMddHHmmss （例：20250207010000）指定された更新日時以降（指定日時含む）に更新された注文のみレスポンスします。
        # symbol - 銘柄コード（例：160030023）日経225マイクロ先物 25/03
        params = {'product': 3, 'details': 'false', 'symbol': '160030023'}
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

    def query_contract(self) -> None:
        """查询合约信息"""
        # 'http://localhost:18080/kabusapi/symbol/160030023@2?addinfo=false'
        params = {'addinfo': 'false'}
        symbol = '160030023'
        market = '2' # 1: 東証、3: 名証、5: 福証、6: 札証、2: 日通し、23: 日中、24: 夜間

        path: str = f"/kabusapi/symbol/{symbol}@{market}?{urlencode(params)}"

        self.add_request(
            method="GET",
            path=path,
            callback=self.on_query_contract,
            on_failed=self.on_failed
        )

    def register_symbol(self):
        """订阅行情"""
        symbol = '160030023'
        market = '2' # 1: 東証、3: 名証、5: 福証、6: 札証、2: 日通し、23: 日中、24: 夜間
        data = {'Symbols':
            [
                {'Symbol': symbol, 'Exchange': market}
            ]}

        path: str = "/kabusapi/register"

        self.add_request(
            method="PUT",
            path=path,
            callback=self.on_register_symbol,
            data=data,
            on_failed=self.on_register_failed
        )

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

        # 生成本地委托号
        orderid: str = str(self.connect_time + self._new_order_id())

        # 推送提交中事件
        order: OrderData = req.create_order_data(
            orderid,
            self.gateway_name
        )
        self.gateway.on_order(order)

        data: dict = {
            "Symbol": req.symbol,
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
            self.gateway.write_log(f"找不到委托号对应的KBS订单号：{req.orderid}")
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

    def on_query_account(self, data: dict, request: Request) -> None:
        """资金查询回报"""
        print(f"on_query_account: {data}")
        account: AccountData = AccountData(
            accountid=self.gateway_name,
            balance=data["FutureTradeLimit"],
            gateway_name=self.gateway_name
        )
        account.available = data["FutureTradeLimit"]
        account.frozen = account.balance - account.available

        if account.balance:
            self.gateway.on_account(account)
        self.gateway.write_log("账户资金查询成功")

    def on_query_position(self, data: dict, request: Request) -> None:
        """持仓查询回报"""
        # print(f"on_query_position: {data}")
        for d in data:
            pnl = d['ProfitLoss'] if d['ProfitLoss'] is not None else 0
            position: PositionData = PositionData(
                symbol=d["Symbol"],
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

    def on_position_failed(self, status_code: str, request: Request) -> None:
        """持仓查询失败回报"""
        msg = f"持仓查询失败，状态码：{status_code}，信息：{request.response.text}"
        self.gateway.write_log(msg)

    def on_query_order(self, data: dict, request: Request) -> None:
        """未成交委托查询回报"""
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

            order: OrderData = OrderData(
                orderid=orderid,
                symbol=d["Symbol"],
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

    def on_query_order_failed(self, status_code: str, request: Request):
        """委托信息查询报错回报"""
        msg = f"委托信息查询失败，状态码：{status_code}，信息：{request.response.text}"
        self.gateway.write_log(msg)

    def on_query_contract(self, data: dict, request: Request):
        """合约信息查询回报"""
        print(f"on_query_contract: {data}")
        contract: ContractData = ContractData(
            symbol=data["Symbol"],
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
        self.gateway.on_contract(contract)

        symbol_contract_map[contract.symbol] = contract

        self.gateway.write_log("合约信息查询成功")

    def on_register_symbol(self, data: dict, request: Request) -> None:
        """订阅行情回报"""
        print(f"on_register_symbol: {data}")
        for s in data["RegistList"]:
            pprint.pprint(s)

        self.gateway.write_log("订阅行情成功")

    def on_register_failed(self, status_code: str, request: Request) -> None:
        """订阅行情失败回报"""
        msg = f"订阅行情失败，状态码：{status_code}，信息：{request.response.text}"
        self.gateway.write_log(msg)

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

        msg: str = f"委托失败，orderid: {order.orderid}, 状态码：{status_code}，信息：{request.response.text}"
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
        msg = f"撤单失败，orderid: {order.orderid}, kbs: {kbs_orderid}, 状态码：{status_code}，信息：{request.response.text}"
        self.gateway.write_log(msg)

    def on_failed(self, status_code: str, request: Request) -> None:
        """失败回报"""
        msg = f"失败，状态码：{status_code}，信息：{request.response.text}"
        self.gateway.write_log(msg)

    def query_history(self, req: HistoryRequest) -> List[BarData]:
        """查询历史数据"""
        self.gateway.write_log("KBS不支持历史数据查询")
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

        self.gateway.write_log("行情Websocket API启动成功")

        # Database历史Tick数据模拟实盘行情
        # self.load_data()
        # self.active: bool = True
        # self.thread = threading.Thread(target=self.run_tickdata_thread)
        # self.thread.start()

    def on_connected(self) -> None:
        """连接成功回报"""
        self.gateway.write_log("行情Websocket API连接刷新")

        self.ping()

        for req in list(self.subscribed.values()):
            self.resubscribe(req)


    def on_disconnected(self) -> None:
        """"""
        self.gateway.write_log("行情Websocket 连接断开")


    def subscribe(self, req: SubscribeRequest) -> None:
        """订阅行情"""
        if req.symbol not in symbol_contract_map:
            self.gateway.write_log(f"找不到该合约代码{req.symbol}")
            return

        if req.vt_symbol in self.subscribed:
            return

        self.subscribed[req.vt_symbol] = req


    def unsubscribe(self, req: SubscribeRequest) -> None:
        """取消订阅行情"""
        if req.symbol not in symbol_contract_map:
            self.gateway.write_log(f"找不到该合约代码{req.symbol}")
            return

        if req.vt_symbol in self.subscribed:
            self.subscribed.pop(req.vt_symbol)

    def resubscribe(self, req: SubscribeRequest) -> None:
        """重连后订阅行情"""
        if req.symbol not in symbol_contract_map:
            self.gateway.write_log(f"找不到该合约代码{req.symbol}")
            return

        self.subscribed[req.vt_symbol] = req


    def ping(self) -> None:
        """发送心跳"""
        self.send_packet({'op': 'ping'})


    def on_packet(self, packet: Any) -> None:
        """推送数据回报"""
        tick: TickData = TickData(
            gateway_name=self.gateway_name,
            symbol=packet['Symbol'],
            exchange=Exchange.JPX,
            datetime=generate_datetime(packet["CurrentPriceTime"]),

            name=packet["SymbolName"],
            volume=packet["TradingVolume"],
            turnover=packet["TradingValue"],
            open_price=packet["OpeningPrice"],
            high_price=packet["HighPrice"],
            low_price=packet["LowPrice"],
            pre_close=packet["PreviousClose"],
            last_price=packet["CurrentPrice"],
            last_volume=packet["TradingVolume"],

            ask_price_1 =packet["Sell1"]["Price"],
            ask_volume_1=packet["Sell1"]["Qty"],
            ask_price_2 =packet["Sell2"]["Price"],
            ask_volume_2=packet["Sell2"]["Qty"],
            ask_price_3 =packet["Sell3"]["Price"],
            ask_volume_3=packet["Sell3"]["Qty"],
            ask_price_4 =packet["Sell4"]["Price"],
            ask_volume_4=packet["Sell4"]["Qty"],
            ask_price_5 =packet["Sell5"]["Price"],
            ask_volume_5=packet["Sell5"]["Qty"],

            bid_price_1 =packet["Buy1"]["Price"],
            bid_volume_1=packet["Buy1"]["Qty"],
            bid_price_2 =packet["Buy2"]["Price"],
            bid_volume_2=packet["Buy2"]["Qty"],
            bid_price_3 =packet["Buy3"]["Price"],
            bid_volume_3=packet["Buy3"]["Qty"],
            bid_price_4 =packet["Buy4"]["Price"],
            bid_volume_4=packet["Buy4"]["Qty"],
            bid_price_5 =packet["Buy5"]["Price"],
            bid_volume_5=packet["Buy5"]["Qty"],
        )
        if tick.last_price:
            self.gateway.on_tick(copy(tick))

    # Database历史Tick数据模拟实盘行情
    def load_data(self) -> None:
        data: List[TickData] = self.load_tick_data(
            symbol='160030023',
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
        self.gateway.write_log("Database历史Tick数据模拟实盘行情线程启动")
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

        self.gateway.write_log("Database历史Tick数据模拟实盘行情线程结束")

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
