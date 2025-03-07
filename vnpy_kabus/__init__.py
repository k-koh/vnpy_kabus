import importlib_metadata

from .kabus_gateway import KabusGateway


try:
    __version__ = importlib_metadata.version("vnpy_kabus")
except importlib_metadata.PackageNotFoundError:
    __version__ = "2025.1.28"
