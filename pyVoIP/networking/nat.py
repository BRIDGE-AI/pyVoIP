from enum import Enum
from typing import Optional
import ipaddress
import socket


class NATError(Exception):
    pass


class AddressType(Enum):
    """Used for determining remote or local tags in SIP messages"""

    REMOTE = 0
    LOCAL = 1


# RFC 1918 - Private Address Space
# https://datatracker.ietf.org/doc/html/rfc1918#section-3
PRIVATE_NETWORKS = [
    ipaddress.ip_network("10.0.0.0/8"),
    ipaddress.ip_network("172.16.0.0/12"),
    ipaddress.ip_network("192.168.0.0/16"),
]


class NAT:
    def __init__(
        self,
        bind_ip: str,
        network: str,
        hostname: Optional[str] = None,
        remote_hostname: Optional[str] = None,
    ):
        self.bind_ip = ipaddress.ip_address(bind_ip)
        self.network = ipaddress.ip_network(network)
        self.hostname = bind_ip if hostname is None else hostname
        self.remote_hostname = remote_hostname

    def get_host(self, host: str):
        """Return the hostname another client needs to connect to us."""
        try:
            ip = ipaddress.ip_address(host)
        except ValueError:
            try:
                ip = ipaddress.ip_address(socket.gethostbyname(host))
            except socket.gaierror:
                raise NATError(f"Unable to resolve hostname {host}")

        # trial
        #if self.remote_hostname is not None:
        #    return self.remote_hostname

        if ip in self.network:
            return self.hostname
        else:
            if self.remote_hostname is not None:
                return self.remote_hostname
            raise NATError(
                "No remote hostname specified, "
                + "cannot provide a return path for remote hosts."
            )

    def _is_local_ip(self, ip: ipaddress.IPv4Address) -> bool:
        """Check if IP is in local network. For 0.0.0.0/0, use RFC 1918 private ranges."""
        if self.network == ipaddress.ip_network("0.0.0.0/0"):
            return any(ip in net for net in PRIVATE_NETWORKS)
        return ip in self.network

    def check_host(self, host: str) -> AddressType:
        """Determine if a host is a remote computer or not."""
        if host in [self.remote_hostname, self.hostname]:
            return AddressType.LOCAL
        try:
            ip = ipaddress.ip_address(host)
            if ip == self.bind_ip:
                return AddressType.LOCAL
            if self.bind_ip == ipaddress.ip_address("0.0.0.0") and self._is_local_ip(ip):
                return AddressType.LOCAL
            return AddressType.REMOTE
        except ValueError:
            try:
                ip = ipaddress.ip_address(socket.gethostbyname(host))
                if ip == self.bind_ip:
                    return AddressType.LOCAL
                if self.bind_ip == ipaddress.ip_address("0.0.0.0") and self._is_local_ip(ip):
                    return AddressType.LOCAL
                return AddressType.REMOTE
            except socket.gaierror:
                return AddressType.REMOTE
