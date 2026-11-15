"""From a traced call's result to the extension's result, by the trusted models of
`NetTcp/TrustedCode/net.lean`, which build Go's values from the extension's: the shape rules
(what Go values net.lean can return for each operation) and the error kinds (D14).

net.lean builds every failure as `model.opError op src addr (model.kindErr code name)` (a
`*net.OpError` with Net "tcp"), but EOF (`io.EOF` itself, from Read only). `model.kindErr`:
code 1 (closed) gives `poll.ErrNetClosing`, a `poll.errNetClosing`; code 2 (timeout)
`poll.ErrDeadlineExceeded`, a `*poll.DeadlineExceededError`; code 3 (sys) an `*os.SyscallError`
whose `Err` is a nonzero `syscall.Errno` (`model.sysErr`). `DialTimeout.impl` may also give, for any
failure of the extension's Dial, `net.errTimeout` (a `*net.timeoutError`) or
`poll.ErrDeadlineExceeded`. `OpError.Timeout`/`Temporary` (`model.errFlag`): false for
errNetClosing, true for *DeadlineExceededError and *timeoutError, arbitrary for *os.SyscallError.

So, reading a traced error backwards: errNetClosing is `closed`; *DeadlineExceededError is
`timeout` (but in DialTimeout, where it is DialTimeout.impl's own choice for a `sys` failure, `sys`);
*timeoutError is DialTimeout's `sys`; *os.SyscallError is `sys`. Each of these is the only
extension result net.lean turns into that Go value, except DialTimeout's *DeadlineExceededError
(code 2 through kindErr, or any code through the AnyBool branch): there `sys` is chosen, the only
failure DialStep has, so no admitted trace is lost.
"""

import model as M

# Go's OpError.Op of each traced operation (net.lean: the first argument of model.opError /
# model.connErr in each model)
GO_OP = {"Read": "read", "Write": "write", "Close": "close", "CloseWrite": "close",
         "SetDeadline": "set", "Accept": "accept", "ListenerClose": "close", "Dial": "dial",
         "DialTimeout": "dial", "Listen": "listen"}
# the *os.SyscallError's Syscall of a sys failure (model.kindErr's name); Dial, DialTimeout and
# Listen pass AnyString: arbitrary
SYSCALL = {"Read": "read", "Write": "write", "CloseWrite": "shutdown", "Accept": "accept4",
           "Close": "close", "ListenerClose": "close", "SetDeadline": "set"}
# operations whose OpError.Source is nil (#GoInterface.nil); the others' is the conn's laddr
SOURCE_NIL = {"SetDeadline", "Accept", "ListenerClose", "Dial", "DialTimeout", "Listen"}

CONN_OPS = ("Read", "Write", "Close", "CloseWrite", "SetDeadline")


def tcp_addr_ok(a):
    """A non-nil *net.TCPAddr (model.anyTCPAddr), as the tracer records it."""
    return isinstance(a, dict) and a.get("type") == "*net.TCPAddr" and not a.get("nil") and "s" in a


class Mapped:
    __slots__ = ("res", "problems", "bad", "note")

    def __init__(self, res=None, problems=None, bad=False, note=None):
        self.res, self.problems, self.bad, self.note = res, problems or [], bad, note


def err_kind(op, err):
    """The kind of a traced error (or "eof"), and the shape problems. Returns (kind, problems,
    bad): bad when no extension result gives this Go value."""
    probs = []
    if err is None:
        return None, probs, False
    t = err.get("type")
    if err.get("eof"):
        if op != "Read":
            probs.append(f"io.EOF from {op} (net.lean returns io.EOF only from Read)")
            return "eof", probs, True
        return "eof", probs, False
    if err.get("isEOF"):
        probs.append("an error wrapping io.EOF (net.lean returns io.EOF itself)")
    if t != "*net.OpError":
        if t == "syscall.Errno":
            probs.append(f"a bare syscall.Errno ({err.get('errno')}) from {op}: net.lean always wraps "
                         "failures in *net.OpError (D12: a failed epoll_ctl registration is not modeled)")
        else:
            probs.append(f"an error of type {t} from {op} (net.lean: *net.OpError)")
        return None, probs, True
    if err.get("op") != GO_OP[op]:
        probs.append(f"OpError.Op {err.get('op')!r} (net.lean's {op}: {GO_OP[op]!r})")
    if err.get("net") != "tcp":
        probs.append(f"OpError.Net {err.get('net')!r} (net.lean: \"tcp\")")
    src = err.get("source")
    if op in SOURCE_NIL:
        if src is not None:
            probs.append(f"OpError.Source {src} (net.lean's {op}: nil)")
    elif not tcp_addr_ok(src):
        probs.append(f"OpError.Source {src} (net.lean's {op}: the conn's laddr, a non-nil *TCPAddr)")
    if not tcp_addr_ok(err.get("addr")):
        probs.append(f"OpError.Addr {err.get('addr')} (net.lean's {op}: a non-nil *TCPAddr)")
    if "timeout" not in err or "temporary" not in err:
        probs.append("no Timeout()/Temporary() recorded for an *OpError")
    inner = err.get("inner")
    to, tmp = err.get("timeout"), err.get("temporary")
    bad = False
    if inner == "poll.errNetClosing":
        kind = M.CLOSED
        if to or tmp:
            probs.append("a closed-end error with Timeout() or Temporary() true (net.lean's errFlag: false)")
        if not err.get("isClosed"):
            probs.append("errors.Is(err, net.ErrClosed) false for poll.errNetClosing")
    elif inner == "*poll.DeadlineExceededError":
        kind = M.SYS if op == "DialTimeout" else M.TIMEOUT
        if not (to and tmp):
            probs.append("a deadline error with Timeout() or Temporary() false (net.lean's errFlag: true)")
        if not err.get("isDeadline"):
            probs.append("errors.Is(err, os.ErrDeadlineExceeded) false for *poll.DeadlineExceededError")
    elif inner == "*net.timeoutError":
        if op != "DialTimeout":
            probs.append(f"net's errTimeout from {op} (net.lean: only DialTimeout returns it)")
            bad = True
        kind = M.SYS
        if not (to and tmp):
            probs.append("errTimeout with Timeout() or Temporary() false (net.lean's errFlag: true)")
    elif inner == "*os.SyscallError":
        kind = M.SYS
        if not err.get("errno"):
            probs.append("an *os.SyscallError with no nonzero syscall.Errno (net.lean's sysErr: AnyErrno)")
        if op in SYSCALL and err.get("syscall") != SYSCALL[op]:
            probs.append(f"SyscallError.Syscall {err.get('syscall')!r} (net.lean's {op}: {SYSCALL[op]!r})")
        if err.get("isClosed") or err.get("isDeadline"):
            probs.append("errors.Is ErrClosed or ErrDeadlineExceeded true for an *os.SyscallError")
    else:
        probs.append(f"OpError.Err of type {inner} (net.lean: poll.errNetClosing, "
                     "*poll.DeadlineExceededError, *os.SyscallError, or DialTimeout's *net.timeoutError)")
        return None, probs, True
    return kind, probs, bad


def map_call(c):
    """The extension result of a returned traced call (Mapped.res):
      Read: a ReadRes; Write: (k, kind); Close, CloseWrite, SetDeadline, ListenerClose: kind;
      Accept, Dial, DialTimeout, Listen: ("ok", new) or ("err", kind)."""
    op, b, e = c.op, c.b, c.e
    kind, probs, bad = err_kind(op, e.get("err"))
    if kind == "eof" and op != "Read":
        return Mapped(None, probs, True)
    if op == "Read":
        n = e.get("n", 0)
        data = bytes.fromhex(e["data"]) if "data" in e else b""
        if n != len(data):
            probs.append(f"Read count {n} with {len(data)} bytes")
            bad = True
        if kind is None:
            res = M.R_BYTES(data)
        else:
            if n != 0:
                probs.append(f"a Read returned {n} bytes and an error (net.lean: 0 with an error)")
                bad = True
            res = M.R_EOF if kind == "eof" else M.R_ERR(kind)
        return Mapped(res, probs, bad)
    if op == "Write":
        k = e.get("n", 0)
        return Mapped((k, kind), probs, bad)
    if op in ("Close", "CloseWrite", "SetDeadline", "ListenerClose"):
        return Mapped(kind, probs, bad)
    if op in ("Accept", "Dial", "DialTimeout", "Listen"):
        if kind is None:
            new = e.get("new")
            want = "l" if op == "Listen" else "c"
            if not isinstance(new, dict) or not str(new.get("id", "")).startswith(want):
                probs.append(f"{op} succeeded with no new socket recorded ({new})")
                return Mapped(None, probs, True)
            if not tcp_addr_ok(new.get("local")):
                probs.append(f"the new socket's LocalAddr {new.get('local')} (net.lean: a non-nil *TCPAddr)")
            if op != "Listen" and not tcp_addr_ok(new.get("remote")):
                probs.append(f"the new socket's RemoteAddr {new.get('remote')} (net.lean: a non-nil *TCPAddr)")
            return Mapped(("ok", new), probs, bad)
        return Mapped(("err", kind), probs, bad)
    raise ValueError(op)
