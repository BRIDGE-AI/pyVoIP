from typing import TYPE_CHECKING, List, Optional, Tuple, Union
from pyVoIP.types import KEY_PASSWORD, SOCKETS
from pyVoIP.SIP.message.message import SIPMessage, SIPMethod, SIPRequest
from pyVoIP.SIP.error import SIPParseError
from pyVoIP.networking.nat import NAT, AddressType
from pyVoIP.networking.transport import TransportMode
import json
import math
import pprint
import pyVoIP
import socket
import sqlite3
import ssl
import threading
import time


if TYPE_CHECKING:
    from pyVoIP.SIP.client import SIPClient


debug = pyVoIP.debug



class VoIPConnection:
    def __init__(
        self,
        voip_sock: "VoIPSocket",
        conn: Optional[SOCKETS],
        message: SIPMessage,
    ):
        """
        Mimics a TCP connection when using UDP, and wraps a socket when
        using TCP or TLS.
        """
        self.conn_id = 0

        self.sock = voip_sock
        self.conn = conn
        self.mode = self.sock.mode
        self.message = message
        self.call_id = message.headers["Call-ID"]
        self.local_tag, self.remote_tag = self.sock.determine_tags(
            self.message
        )
        self._peak_buffer: Optional[bytes] = None
        if conn and type(message) is SIPRequest:
            if self.sock.mode.tls_mode:
                client_context = ssl.create_default_context()
                client_context.check_hostname = pyVoIP.TLS_CHECK_HOSTNAME
                client_context.verify_mode = pyVoIP.TLS_VERIFY_MODE
                self.conn = client_context.wrap_socket(
                    self.conn, server_hostname=message.destination["host"]
                )
            addr = (message.destination["host"], message.destination["port"])
            self.conn.connect(addr)

        self.recv_lock = threading.Lock()

        self._stop = False

    def send(self, data: Union[bytes, str]) -> None:
        if type(data) is str:
            data = data.encode("utf8")
        try:
            msg = SIPMessage.from_bytes(data)
        except SIPParseError:
            return
        if not self.conn:  # If UDP
            if type(msg) is SIPRequest:
                addr = (msg.destination["host"], msg.destination["port"])
            else:
                addr = msg.headers["Via"][0]["address"]
            try:
                self.sock.s.sendto(data, addr)
            except Exception as error:
                debug(f"data:{data}")
                debug(f"addr:{addr}")
                debug(f"ERROR:{error}", trace=True)
                return False
        else:
            self.conn.send(data)
        debug(f"SENT:\n{msg.summary()}", trace=False)
        return True

    def update_tags(self, local_tag: str, remote_tag: str) -> None:
        self.local_tag = local_tag
        self.remote_tag = remote_tag

    def peak(self) -> bytes:
        return self.recv(8192, timeout=60, peak=True)

    def recv(self, nbytes: int = 8192, timeout=0, peak=False, **kwargs) -> bytes:
        if self._peak_buffer:
            data = self._peak_buffer
            if not peak:
                self._peak_buffer = None
            return data
        if self.conn:
            return self._tcp_tls_recv(nbytes, timeout, peak, **kwargs)
        else:
            return self._udp_recv(nbytes, timeout, peak, **kwargs)

    def _tcp_tls_recv(self, nbytes: int, timeout=0, peak=False) -> bytes:
        timeout = time.monotonic() + timeout if timeout else math.inf
        # TODO: Timeout
        msg = None
        while not msg and not self.sock.SD:
            data = self.conn.recv(nbytes)
            try:
                msg = SIPMessage.from_bytes(data)
            except SIPParseError as e:
                br = self.sock.gen_bad_request(
                    connection=self, error=e, received=data
                )
                self.send(br)
        if time.monotonic() >= timeout:
            raise TimeoutError()
        if peak:
            self._peak_buffer = data
        debug(f"RECEIVED:\n{msg.summary()}")
        return data

    def _udp_recv(self, nbytes: int, timeout=0, peak=False, **kwargs) -> bytes:
        type_ = kwargs.pop("type", None)
        ignore = kwargs.pop("ignore", None)

        timeout = time.monotonic() + timeout if timeout else math.inf
        while time.monotonic() <= timeout and not self.sock.SD:
            time.sleep(0) # yield

            if self._stop:
                #debug("<<" + "-" * 20 + "STOP" + "-" * 20 + ">>")
                return None

            # print("Trying to receive")
            # print(self.sock.get_database_dump())
            conn = self.sock.buffer.cursor()
            conn.row_factory = sqlite3.Row

            with self.recv_lock:
                sql = (
                    'SELECT * FROM "msgs" WHERE "call_id"=? AND '
                    + '"local_tag" IS ? AND "remote_tag" IS ?'
                )
                bindings = [
                    self.call_id,
                    self.local_tag,
                    self.remote_tag,
                ]

                #TODO: TRY
                #https://github.com/BRIDGE-AI/bridge/issues/199#issuecomment-2646368741
                # bot에 의해 bye할 때 등 send하는 conn과 recv하는 conn이 다른 경우가 있고 다를 수 있는 것으로 보임 - 일단 보류
                #sql += ' AND connection IS ?'
                #bindings.append(self.conn_id)

                if type_:
                    sql += " AND " + f'"type" IS ?'
                    bindings.append(type_)

                if ignore:
                    sql += " AND " + f'"type" IS NOT ?'
                    bindings.append(ignore)

                #20250-02-10: uses only very recent message
                #https://github.com/BRIDGE-AI/bridge/issues/199#issuecomment-2646368741
                sql += " ORDER BY id DESC"

                #debug(f"sql:{sql}, peak:{peak}")
                result = conn.execute(sql, bindings)
                row = result.fetchone()

                if not row:
                    conn.close()
                    continue

                #debug(f"peak: {peak}, row:\n{row['msg']}", trace=True)
                if peak:
                    # If peaking, return before deleting from the database
                    conn.close()
                    return row["msg"].encode("utf8")

                try:
                    conn.execute('DELETE FROM "msgs" WHERE "id" = ?', (row["id"],))
                except sqlite3.OperationalError:
                    pass
                conn.close()
            return row["msg"].encode("utf8")
        if time.monotonic() >= timeout:
            raise TimeoutError()

    def close(self):
        self.sock.deregister_connection(self)
        if self.conn:
            self.conn.close()

    def stop(self):
        self._stop = True


class VoIPSocket(threading.Thread):
    def __init__(
        self,
        mode: TransportMode,
        bind_ip: str,
        bind_port: int,
        sip: "SIPClient",
        cert_file: Optional[str] = None,
        key_file: Optional[str] = None,
        key_password: KEY_PASSWORD = None,
    ):
        """
        This is the main phone SIP socket.  It should receive all new dialogs.
        """
        super().__init__(name="VoIPSocket Thread")
        self.SD = False
        self.mode = mode
        self.s = socket.socket(socket.AF_INET, mode.socket_type)
        self.bind_ip: str = bind_ip
        self.bind_port: int = bind_port
        self.sip = sip
        self.nat: NAT = sip.nat
        self.server_context: Optional[ssl.SSLContext] = None
        if mode.tls_mode:
            self.server_context = ssl.SSLContext(
                protocol=ssl.PROTOCOL_TLS_SERVER
            )
            self.server_context.load_default_certs()
            if cert_file:
                self.server_context.load_cert_chain(
                    cert_file, key_file, key_password
                )
            self.s = self.server_context.wrap_socket(self.s, server_side=True)

        self.buffer = sqlite3.connect(
            pyVoIP.SIP_STATE_DB_LOCATION,
            isolation_level=None,
            check_same_thread=False,
        )
        """
        RFC 3261 Section 12, Paragraph 2 states:
        "A dialog is identified at each UA with a dialog ID, which consists
        of a Call-ID value, a local tag and remote tag."

        This in memory database is designed to check if a VoIPConnection
        already exists for a dialog. The dialog is detected from the incoming
        message over UDP. If a VoIPConnection does not exist for the dialog,
        we will create one. This database also stores messages in the msgs
        table. This table stores new SIPMessages received by VoIPSocket
        over UDP for VoIPConnections to receive pull them.
        """
        conn = self.buffer.cursor()
        conn.execute(
            """CREATE TABLE "msgs" (
                "id" INTEGER PRIMARY KEY AUTOINCREMENT,
                "call_id" TEXT,
                "local_tag" TEXT,
                "remote_tag" TEXT,
                "type" TEXT,
                "connection" INTEGER NOT NULL,
                "msg" TEXT
            );"""
        )
        conn.execute(
            """CREATE INDEX "msg_index" ON msgs """
            + """("call_id", "local_tag", "remote_tag");"""
        )
        conn.execute(
            """CREATE INDEX "msg_index_2" ON msgs """
            + """("call_id", "remote_tag", "local_tag");"""
        )
        conn.execute(
            """CREATE TABLE "listening" (
                "call_id" TEXT NOT NULL,
                "local_tag" TEXT,
                "remote_tag" TEXT,
                "connection" INTEGER NOT NULL UNIQUE,
                PRIMARY KEY("call_id", "local_tag", "remote_tag")
            );"""
        )
        conn.close()
        self.conns_lock = threading.Lock()
        self.conns: Dict[int, VoIPConnection] = {}
        self.recent_conn_id = 0

    def gen_bad_request(
        self, connection=None, message=None, error=None, received=None
    ) -> bytes:
        body = f"<error><message>{error}</message>"
        body += f"<received>{received}</received></error>"
        bad_request = "SIP/2.0 400 Malformed Request\r\n"
        bad_request += (
            f"Via: SIP/2.0/{self.mode} {self.bind_ip}:{self.bind_port}\r\n"
        )
        bad_request += "Content-Type: application/xml\r\n"
        bad_request += f"Content-Length: {len(body)}\r\n\r\n"
        bad_request += body
        return bad_request.encode("utf8")

    def __connection_exists(self, message: SIPMessage) -> bool:
        return bool(self.__get_connection(message))

    def __get_connection(
        self, message: SIPMessage
    ) -> Optional[VoIPConnection]:
        local_tag, remote_tag = self.determine_tags(message)
        call_id = message.headers["Call-ID"]
        conn = self.buffer.cursor()
        sql = 'SELECT "connection" FROM "listening" WHERE "call_id" IS ?'
        sql += ' AND "local_tag" IS ? AND "remote_tag" IS ?'
        result = conn.execute(sql, (call_id, local_tag, remote_tag))
        rows = result.fetchall()
        if rows:
            conn.close()
            return self.conns.get(rows[0][0], None)
        debug("New Connection Started")
        # If we didn't find one lets look for something that doesn't have
        # one of the tags
        sql = 'SELECT "connection" FROM "listening" WHERE "call_id" = ?'
        sql += ' AND ("local_tag" IS NULL OR "local_tag" = ?)'
        sql += ' AND ("remote_tag" IS NULL OR "remote_tag" = ?)'
        result = conn.execute(sql, (call_id, local_tag, remote_tag))
        rows = result.fetchall()
        if rows:
            if local_tag and remote_tag:
                sql = 'UPDATE "listening" SET "remote_tag" = ?, '
                sql += '"local_tag" = ? WHERE "connection" = ?'
                conn.execute(sql, (remote_tag, local_tag, rows[0][0]))
                self.conns.get(rows[0][0], None).update_tags(local_tag, remote_tag)
            conn.close()
            return self.conns.get(rows[0][0], None)
        debug("No Connection in sqlite buffer")
        conn.close()
        return None

    def __register_connection(self, connection: VoIPConnection) -> int:
        self.conns_lock.acquire()
        self.recent_conn_id += 1
        self.conns[self.recent_conn_id] = connection
        connection.conn_id = self.recent_conn_id
        try:
            conn = self.buffer.cursor()
            conn.execute(
                """INSERT INTO "listening"
                    ("call_id", "local_tag", "remote_tag", "connection")
                    VALUES
                    (?, ?, ?, ?)""",
                (
                    connection.call_id,
                    connection.local_tag,
                    connection.remote_tag,
                    connection.conn_id,
                ),
            )
        except sqlite3.IntegrityError as e:
            e.add_note(
                "Error is from registering connection for message: "
                + f"{connection.message.summary()}"
            )
            e.add_note("Internal Database Dump:\n" + self.get_database_dump())
            e.add_note(
                f"({connection.call_id=}, {connection.local_tag=}, "
                + f"{connection.remote_tag=}, {connection.conn_id=})"
            )
            raise
        except sqlite3.OperationalError:
            pass
        finally:
            conn.close()
            self.conns_lock.release()
            return connection.conn_id

    def deregister_connection(self, connection: VoIPConnection) -> None:
        if self.mode is not TransportMode.UDP:
            return
        self.conns_lock.acquire()
        debug(f"Deregistering {connection}")
        debug(f"{self.conns=}")
        debug(self.get_database_dump())
        try:
            conn = self.buffer.cursor()
            sql = 'SELECT "connection" FROM "listening" WHERE "call_id" = ?'
            sql += ' AND ("local_tag" IS NULL OR "local_tag" = ?)'
            sql += ' AND ("remote_tag" IS NULL OR "remote_tag" = ?)'
            result = conn.execute(
                sql,
                (
                    connection.call_id,
                    connection.local_tag,
                    connection.remote_tag,
                ),
            )
            row = result.fetchone()
            conn_id = row[0]
            """
            Need to set to None to not change the indexes of any other conn
            """
            self.conns.pop(conn_id, None)
            conn.execute(
                'DELETE FROM "listening" WHERE "connection" = ?', (conn_id,)
            )
            conn.execute(
                'DELETE FROM "msgs" WHERE "call_id" = ?', (connection.call_id,)
            )
        except sqlite3.OperationalError:
            pass
        finally:
            conn.close()
            self.conns_lock.release()

    def get_database_dump(self, pretty=False) -> str:
        conn = self.buffer.cursor()
        lines = ["<<database_dump>>"]
        try:
            result = conn.execute('SELECT * FROM "listening";')
            result1 = result.fetchall()
            result = conn.execute('SELECT * FROM "msgs";')
            result2 = result.fetchall()
        finally:
            conn.close()
        if pretty:
            lines.append("listening: " + pprint.pformat(result1))
            lines.append("")
            lines.append("msgs: " + pprint.pformat(result2))
        else:
            lines.append(f"listening[{len(result1)}]:")
            lines.extend(["  " + json.dumps(item) for item in result1])
            lines.append("")
            lines.append(f"msgs[{len(result2)}]:")
            lines.extend(["  " + json.dumps(item) for item in result2])
        return "\n".join(lines)

    def determine_tags(self, message: SIPMessage) -> Tuple[str, str]:
        """
        Return local_tag, remote_tag
        """

        to_header = message.headers["To"]
        from_header = message.headers["From"]
        to_tag = to_header["tag"] if to_header["tag"] else None
        from_tag = from_header["tag"] if from_header["tag"] else None

        from_host = from_header["host"]
        if self.nat.check_host(from_host) is AddressType.LOCAL:
            return from_tag, to_tag
        return to_tag, from_tag

    def bind(self, addr: Tuple[str, int]) -> None:
        self.s.bind(addr)
        self.bind_ip = addr[0]
        self.bind_port = addr[1]
        return None

    def _listen(self, backlog=0) -> None:
        return self.s.listen(backlog)

    def _tcp_tls_run(self) -> None:
        self._listen()
        while not self.SD:
            try:
                conn, addr = self.s.accept()
            except OSError:
                continue
            debug(f"Received new {self.mode} connection from {addr}.")
            data = conn.recv(8192)
            if data is None:
                continue
            try:
                message = SIPMessage.from_bytes(data)
            except SIPParseError:
                continue
            debug("\n\nRECEIVED SIP Message:")
            debug(message.summary())
            self._handle_incoming_message(conn, message)

    def _udp_run(self) -> None:
        while not self.SD:
            try:
                data, addr = self.s.recvfrom(8192)
            except OSError:
                continue
            if data is None:
                continue
            try:
                message = SIPMessage.from_bytes(data)
            except SIPParseError:
                continue
            debug(f"RECEIVED UDP Message:\n{message.summary()}", trace=False)
            self._handle_incoming_message(None, message, source_addr=addr)

    def _handle_incoming_message(
        self, conn: Optional[SOCKETS], message: SIPMessage, source_addr=None
    ):
        call_id = message.headers["Call-ID"]

        conn_created = False
        voip_conn = self.__get_connection(message)

        if voip_conn is None and type(message) is SIPRequest and message.method in (SIPMethod.BYE, SIPMethod.OPTIONS):
            ok = self.sip.gen_ok(message)
            addr = message.headers["Via"][0]["address"]
            self.s.sendto(ok.encode("utf8"), addr)
            return

        if voip_conn is None:
            voip_conn = VoIPConnection(self, conn, message)
            conn_created = True

        if type(message) is SIPRequest:
            #TODO: DEBUG
            #data = b'INVITE sip:100@43.202.127.199 SIP/2.0\r\nVia: SIP/2.0/UDP 162.217.96.20:0;branch=z9hG4bK-1366198931;rport\r\nMax-Forwards: 70\r\nTo: "PBX"<sip:100@1.1.1.1>\r\nFrom: "PBX"<sip:100@1.1.1.1>;tag=3262636137666337313363340133383939323732353135\r\nUser-Agent: friendly-scanner\r\nCall-ID: 1004141963740939812350326\r\nContact: sip:100@162.217.96.20:0\r\nCSeq: 1 INVITE\r\nAccept: application/sdp\r\nContent-Length: 0\r\n\r\n'
            #message = SIPMessage.from_bytes(data)
            #debug(f"message:{message.summary()}")

            cnd = self.sip.phone.ignorable(message)
            if cnd is not None:
                method = message.method if hasattr(message, 'method') else 'UNKNOWN'
                via = message.headers.get("Via", [{}])[0].get("address", ("?", "?"))
                ua = message.headers.get("User-Agent", "?")
                src = f"{source_addr[0]}:{source_addr[1]}" if source_addr else "?"
                print(f"\033[93m[BLOCKED] {method} from {src} (UA: {ua}) - condition: {cnd}\033[0m")
                on_ignored = self.sip.phone.voip_phone_parameter.on_ignored
                if on_ignored:
                    on_ignored(message, cnd, source_addr=source_addr)
                return

        # 조건에 맞아 ignore한다면 register하지 않음
        conn_created and self.__register_connection(voip_conn)

        type_ = message.start_line[0].split(" ")[0]
        local_tag, remote_tag = self.determine_tags(message)
        raw_message = message.raw.decode("utf8")

        cursor = self.buffer.cursor()
        cursor.execute(
            "INSERT INTO msgs (call_id, local_tag, remote_tag, type, connection, msg) "
            + "VALUES (?, ?, ?, ?, ?, ?)",
            (call_id, local_tag, remote_tag, type_, voip_conn.conn_id, raw_message),
        )
        cursor.close()

        conn_created and self.sip.handle_new_connection(voip_conn)

    def start(self) -> None:
        self.bind((self.bind_ip, self.bind_port))
        super().start()

    def run(self) -> None:
        if self.mode == TransportMode.UDP:
            self._udp_run()
        else:
            self._tcp_tls_run()

    def close(self) -> None:
        self.SD = True
        if hasattr(self, "s"):
            if self.s:
                try:
                    self.s.shutdown(socket.SHUT_RDWR)
                except OSError:
                    pass
                self.s.close()
        return

    def send(self, data: bytes) -> VoIPConnection:
        """
        Creates a new connection, sends the data, then returns the socket
        """
        if self.mode == TransportMode.UDP:
            conn = VoIPConnection(self, None, SIPMessage.from_bytes(data))
            self.__register_connection(conn)
            conn.send(data)
            return conn
        s = socket.socket(socket.AF_INET, self.mode.socket_type)
        conn = VoIPConnection(self, s, SIPMessage.from_bytes(data))
        conn.send(data)
        return conn

    #TODO: deprecated
    def delete_msg(self, call_id, conn=None):
        _conn = conn

        if _conn is None:
            conn = self.buffer.cursor()
            conn.row_factory = sqlite3.Row

        result = conn.execute('SELECT * FROM "msgs" WHERE "call_id" = ?;', (call_id,))
        result2 = result.fetchall()

        ret = "msgs: " + pprint.pformat(result2)

        try:
            conn.execute('DELETE FROM "listening" WHERE "call_id" = ?', (call_id,))
        except sqlite3.OperationalError as error:
            pass

        try:
            conn.execute('DELETE FROM "msgs" WHERE "call_id" = ?', (call_id,))
        except sqlite3.OperationalError as error:
            pass

        if _conn is None:
            conn.close()

