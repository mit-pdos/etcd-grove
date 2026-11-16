"""Hand-made traces in the tracer's format (examples/net/conform/README.md), for the tests and
the mutation check: one file per process, an optional driver file."""

import json
import os
import shutil
import tempfile

import mapping as G
import trace as T

TA = {"type": "*net.TCPAddr", "net": "tcp", "s": "127.0.0.1:1"}


def addr(s):
    return {"type": "*net.TCPAddr", "net": "tcp", "s": s}


def err_closed(op):
    return {"type": "*net.OpError", "msg": "use of closed network connection", "eof": False, "isEOF": False,
            "isClosed": True, "isDeadline": False, "timeout": False, "temporary": False,
            "op": G.GO_OP[op], "net": "tcp", "source": None if op in G.SOURCE_NIL else TA, "addr": TA,
            "inner": "poll.errNetClosing"}


def err_timeout(op):
    return {"type": "*net.OpError", "msg": "i/o timeout", "eof": False, "isEOF": False, "isClosed": False,
            "isDeadline": True, "timeout": True, "temporary": True, "op": G.GO_OP[op], "net": "tcp",
            "source": None if op in G.SOURCE_NIL else TA, "addr": TA, "inner": "*poll.DeadlineExceededError"}


def err_errtimeout():
    return {"type": "*net.OpError", "msg": "i/o timeout", "eof": False, "isEOF": False, "isClosed": False,
            "isDeadline": False, "timeout": True, "temporary": True, "op": "dial", "net": "tcp",
            "source": None, "addr": TA, "inner": "*net.timeoutError"}


def err_sys(op, errno=104, syscall=None):
    return {"type": "*net.OpError", "msg": "x", "eof": False, "isEOF": False, "isClosed": False,
            "isDeadline": False, "timeout": False, "temporary": False, "op": G.GO_OP[op], "net": "tcp",
            "source": None if op in G.SOURCE_NIL else TA, "addr": TA, "inner": "*os.SyscallError",
            "syscall": syscall or G.SYSCALL.get(op, "connect"), "errno": errno}


EOF = {"type": "*errors.errorString", "msg": "EOF", "eof": True, "isEOF": True, "isClosed": False,
       "isDeadline": False}


class Trace:
    def __init__(self):
        self.procs = []
        self.events = []
        self.dir = None

    def proc(self, node, pid=None, t0=0):
        p = P(self, node, pid or (1000 + len(self.procs)), t0)
        self.procs.append(p)
        return p

    def event(self, ev, p, t, **kw):
        self.events.append({"k": "P", "pid": 1, "node": "drv", "s": len(self.events) + 1, "ev": ev, "t": t,
                            "cnode": p.node, "cpid": p.pid, **kw})

    def write(self, d):
        for p in self.procs:
            with open(os.path.join(d, f"{p.node}.{p.pid}.{p.t0}.jsonl"), "w") as fp:
                for r in p.recs:
                    fp.write(json.dumps(r) + "\n")
        if self.events:
            with open(os.path.join(d, "_driver.1.0.jsonl"), "w") as fp:
                fp.write(json.dumps(_header("driver", 1, "drv", 0)) + "\n")
                for r in self.events:
                    fp.write(json.dumps(r) + "\n")

    def run(self):
        d = tempfile.mkdtemp(prefix="nettcp-check-test-")
        try:
            self.write(d)
            return T.load_dir(d)
        finally:
            shutil.rmtree(d)


def _header(role, pid, node, t0):
    return {"k": "H", "v": 1, "role": role, "pid": pid, "ppid": 1, "node": node, "exe": "x", "args": [],
            "go": "go1.27.3", "host": "h", "timens": "time:[1]", "netns": "net:[1]", "file": "f",
            "t0": t0, "wall": 10 ** 18, "t1": t0}


class P:
    def __init__(self, tr, node, pid, t0):
        self.tr, self.node, self.pid, self.t0 = tr, node, pid, t0
        self.recs = [_header("node", pid, node, t0)]
        self.seq = 0

    def op(self, op, t0, t1, id=None, b=None, e=None, pending=False, g=1):
        self.seq += 1
        rb = {"k": "B", "pid": self.pid, "node": self.node, "s": self.seq, "g": g, "op": op, "t": t0}
        if id is not None:
            rb["id"] = id
        rb.update(b or {})
        self.recs.append(rb)
        if not pending:
            re = {"k": "E", "pid": self.pid, "node": self.node, "s": self.seq, "g": g, "op": op, "t": t1}
            if id is not None:
                re["id"] = id
            re.update(e if e is not None else {"err": None})
            self.recs.append(re)
        return self.seq

    def listen(self, t0, t1, a, lid="l1", err=None, pending=False):
        e = {"new": {"id": lid, "net": "tcp", "local": addr(a if not a.startswith(":") else "[::]" + a),
                     "remote": None}, "err": None} if err is None else {"err": err}
        return self.op("Listen", t0, t1, b={"net": "tcp", "addr": a}, e=e, pending=pending)

    def dial(self, t0, t1, a, cid="c1", port=40000, err=None, op="Dial", pending=False, remote=None):
        b = {"net": "tcp", "addr": a}
        if op == "DialTimeout":
            b["timeout"] = 1000
        e = {"new": {"id": cid, "net": "tcp", "local": addr(f"127.0.0.1:{port}"), "remote": addr(remote or a)},
             "err": None} if err is None else {"err": err}
        return self.op(op, t0, t1, b=b, e=e, pending=pending)

    def accept(self, t0, t1, lid, cid, local, remote, err=None, pending=False):
        e = {"new": {"id": cid, "net": "tcp", "local": addr(local), "remote": addr(remote)}, "err": None} \
            if err is None else {"err": err}
        return self.op("Accept", t0, t1, id=lid, e=e, pending=pending)

    def lclose(self, t0, t1, lid, err=None):
        return self.op("ListenerClose", t0, t1, id=lid, e={"err": err})

    def read(self, t0, t1, cid, n, data=b"", err=None, pending=False, g=1):
        e = {"n": len(data), "err": err}
        if data:
            e["data"] = data.hex()
        return self.op("Read", t0, t1, id=cid, b={"n": n}, e=e, pending=pending, g=g)

    def write(self, t0, t1, cid, data, n=None, err=None, pending=False, g=1):
        e = {"n": len(data) if n is None else n, "err": err}
        return self.op("Write", t0, t1, id=cid, b={"n": len(data), "data": data.hex()}, e=e, pending=pending, g=g)

    def close(self, t0, t1, cid, err=None, pending=False, g=1):
        return self.op("Close", t0, t1, id=cid, e={"err": err}, pending=pending, g=g)

    def closewrite(self, t0, t1, cid, err=None, g=1):
        return self.op("CloseWrite", t0, t1, id=cid, e={"err": err}, g=g)

    def deadline(self, t0, t1, cid, which="both", set_=True, err=None):
        b = {"which": which, "set": set_}
        if set_:
            b.update({"in": 1000, "wall": 1})
        return self.op("SetDeadline", t0, t1, id=cid, b=b, e={"err": err})

    def unmodeled(self, t0, t1, api, id=None):
        return self.op("Unmodeled", t0, t1, id=id, b={"api": api}, e={"api": api, "err": None})

    def addrq(self, t0, t1, op, id, a):
        return self.op(op, t0, t1, id=id, e={"addr": a})


A1 = "127.0.0.1:7101"


def setup_conn(tr, t=0, port=40000, lid="l1", dcid="c1", acid="c1", listen=True, srv=None, cli=None):
    """A server node listens at A1 and accepts a client's Dial; returns (client, server)."""
    cli = cli or tr.proc("client")
    srv = srv or tr.proc("server")
    if listen:
        srv.listen(t + 1, t + 2, A1, lid)
    cli.dial(t + 3, t + 6, A1, dcid, port=port)
    srv.accept(t + 4, t + 7, lid, acid, A1, f"127.0.0.1:{port}")
    return cli, srv
