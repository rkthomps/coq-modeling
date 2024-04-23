import requests
import socket
import pprint
from pathlib import Path

from urllib3.connection import HTTPConnection
from urllib3.connectionpool import HTTPConnectionPool
from requests.adapters import HTTPAdapter


class ServerConnection(HTTPConnection):
    def __init__(self, server_loc: Path):
        super().__init__("localhost")
        self.server_loc = server_loc

    def connect(self):
        self.sock = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        self.sock.connect(str(self.server_loc.resolve()))


class ServerConnectionPool(HTTPConnectionPool):
    def __init__(self, server_loc: Path):
        super().__init__("localhost")
        self.server_loc = server_loc

    def _new_conn(self):
        return ServerConnection(self.server_loc)


class ServerAdapter(HTTPAdapter):
    def __init__(self, server_loc: Path):
        super().__init__()
        self.server_loc = server_loc

    def get_connection(self, url, proxies=None):
        return ServerConnectionPool(self.server_loc)
