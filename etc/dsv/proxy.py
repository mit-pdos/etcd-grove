#!/usr/bin/env python3
"""Allowlisting HTTPS proxy for the dsverify sandbox.

serve SOCK LOG   (outside the sandbox) accept HTTP CONNECT on a Unix socket; tunnel only to
                 hosts in ALLOW on port 443; log every request (allowed or denied) to LOG.
bridge SOCK PORT (inside the sandbox, which has no network) listen on 127.0.0.1:PORT and
                 forward each connection to the Unix socket SOCK.
"""
import os, socket, sys, threading, time

# platform.claude.com: Claude Code's startup connectivity check (and OAuth) goes there too.
ALLOW = {"api.anthropic.com", "platform.claude.com"}


def pump(a, b):
    try:
        while True:
            d = a.recv(65536)
            if not d:
                break
            b.sendall(d)
    except OSError:
        pass
    finally:
        for s in (a, b):
            try:
                s.shutdown(socket.SHUT_RDWR)
            except OSError:
                pass


def splice(a, b):
    threading.Thread(target=pump, args=(a, b), daemon=True).start()
    pump(b, a)
    a.close(); b.close()


def log(path, msg):
    with open(path, "a") as f:
        f.write(time.strftime("%Y-%m-%dT%H:%M:%S ") + msg + "\n")


def handle(c, logpath):
    buf = b""
    while b"\r\n\r\n" not in buf:
        d = c.recv(4096)
        if not d:
            c.close(); return
        buf += d
        if len(buf) > 65536:
            c.close(); return
    head, rest = buf.split(b"\r\n\r\n", 1)
    line = head.split(b"\r\n")[0].decode("latin-1")
    parts = line.split()
    if len(parts) < 2 or parts[0] != "CONNECT":
        log(logpath, "DENY non-CONNECT " + line)
        c.sendall(b"HTTP/1.1 403 Forbidden\r\n\r\n"); c.close(); return
    host, _, port = parts[1].rpartition(":")
    if host not in ALLOW or port != "443":
        log(logpath, "DENY " + parts[1])
        c.sendall(b"HTTP/1.1 403 Forbidden\r\n\r\n"); c.close(); return
    try:
        u = socket.create_connection((host, 443), timeout=30)
        u.settimeout(None)
    except OSError as e:
        log(logpath, f"FAIL {parts[1]} {e}")
        c.sendall(b"HTTP/1.1 502 Bad Gateway\r\n\r\n"); c.close(); return
    log(logpath, "ALLOW " + parts[1])
    c.sendall(b"HTTP/1.1 200 Connection established\r\n\r\n")
    if rest:
        u.sendall(rest)
    splice(c, u)


def serve(sock, logpath):
    if os.path.exists(sock):
        os.unlink(sock)
    s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    s.bind(sock); os.chmod(sock, 0o666); s.listen(64)
    while True:
        c, _ = s.accept()
        threading.Thread(target=handle, args=(c, logpath), daemon=True).start()


def bridge(sock, port):
    s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    s.bind(("127.0.0.1", int(port))); s.listen(64)
    while True:
        c, _ = s.accept()
        u = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        try:
            u.connect(sock)
        except OSError:
            c.close(); continue
        threading.Thread(target=splice, args=(c, u), daemon=True).start()


if __name__ == "__main__":
    {"serve": serve, "bridge": bridge}[sys.argv[1]](*sys.argv[2:])
