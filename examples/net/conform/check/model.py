"""A literal transcription of the net extension's semantics, `GooseLang/Ext/Net/Impl.lean` (v3,
D1-D25, v3.4: no plan and no hosts, valid addresses `addrOk`, D20, and wildcards `wildOk`, D21).
NOT PROVED to agree with the Lean: each
definition names the Lean definition it transcribes (`[Lean: Name]`), keeps its case order and its
conjuncts, and says where it departs from a word-for-word reading. Read it side by side with
Impl.lean; the README's table maps every Lean name to its function here.

These are the relations as predicates: a relation `R x y z` of Lean is a function `r(x, y, z)` that
returns whether it holds. Where a Lean relation has an existential (`∃ k, ...`), the function either
takes the witness as an argument (`keep=` for a read's cut) or decides it at the only candidate the
other arguments leave (each such place says why the candidate is the only one); `test_check.py`
compares those decisions with a search over every `k` on small inputs. The checker's replay of a
witness (`replay.py`) calls these predicates on every step: they are what the Lean replay will
check.

Representation: a `GoString` and a `List w8` are Python `bytes`; a `GMap` a dict (never mutated:
every update copies); `Bool` a bool; `Option NetErr` `None` or one of the kind strings; a `w64`
an int in [0, 2^64).
"""

from typing import NamedTuple

W64 = 1 << 64

# ---------------------------------------------------------------------------------------------
# States

OPEN, FIN, CUT = "open", "fin", "cut"  # [Lean: NetStatus] .open .fin .cut


class NetDir(NamedTuple):
    """[Lean: NetDir] bytes written and not yet read, oldest first; status."""
    bytes: bytes
    status: str


DIR_FRESH = NetDir(b"", OPEN)  # [Lean: NetDir.fresh]


class NetEnd(NamedTuple):
    """[Lean: NetEnd] closed, read deadline set, write deadline set."""
    closed: bool
    rdl: bool
    wdl: bool


END_FRESH = NetEnd(False, False, False)  # [Lean: NetEnd.fresh]


class NetConn(NamedTuple):
    """[Lean: NetConn] addr, accepted, dEnd (side False = 0, the dialer's), aEnd (side True = 1),
    up (from the dialer to the acceptor), down (from the acceptor to the dialer), and (v3.3, D25)
    each end's write lock (dLock, aLock: held by a Write of that end between its first step and
    its last)."""
    addr: bytes
    accepted: bool
    dEnd: NetEnd
    aEnd: NetEnd
    up: NetDir
    down: NetDir
    dLock: bool = False
    aLock: bool = False


def conn_fresh(a):
    """[Lean: NetConn.fresh]"""
    return NetConn(a, False, END_FRESH, END_FRESH, DIR_FRESH, DIR_FRESH)


def conn_abandoned(a):
    """[Lean: NetConn.abandoned] D16: pending, the dialer's end closed, its direction shut and
    empty."""
    return NetConn(a, False, END_FRESH._replace(closed=True), END_FRESH, NetDir(b"", FIN), DIR_FRESH)


def end_st(c, s):
    """[Lean: NetConn.endSt] (`s` a bool: False the dialer, True the acceptor)."""
    return c.aEnd if s else c.dEnd


def out(c, s):
    """[Lean: NetConn.out] the direction from the end `s` (the one it writes)."""
    return c.down if s else c.up


def set_end(c, s, st):
    """[Lean: NetConn.setEnd]"""
    return c._replace(aEnd=st) if s else c._replace(dEnd=st)


def set_out(c, s, d):
    """[Lean: NetConn.setOut]"""
    return c._replace(down=d) if s else c._replace(up=d)


def lock(c, s):
    """[Lean: NetConn.lock] D25."""
    return c.aLock if s else c.dLock


def set_lock(c, s, b):
    """[Lean: NetConn.setLock] D25."""
    return c._replace(aLock=b) if s else c._replace(dLock=b)


class NetGlobal(NamedTuple):
    """[Lean: NetGlobal] conns (number -> NetConn). (v3.4: no plan.)"""
    conns: dict

    def set_conn(self, c, cn):
        """[Lean: NetGlobal.setConn]"""
        conns = dict(self.conns)
        conns[c] = cn
        return NetGlobal(conns)


class NetLocal(NamedTuple):
    """[Lean: NetLocal] lis (listener id -> (address as given to Listen, open)). (v3.4: no
    host.)"""
    lis: dict


def global_init(g):
    """[Lean: NetGlobal.init] no connection."""
    return g.conns == {}


def local_init(L):
    """[Lean: NetLocal.init] no listener."""
    return L.lis == {}


def end_id(c, s):
    """[Lean: endId] `2 c + s` as a w64."""
    return (2 * c + (1 if s else 0)) % W64


def is_end(e, c, s):
    """[Lean: IsEnd]"""
    return 2 * c + 1 < W64 and e == end_id(c, s)


def decode_end(e):
    """The only (c, s) with `IsEnd e c s` (`IsEnd` requires `2 c + 1 < 2^64`, so `endId` is
    injective there and `e = 2 c + s` exactly)."""
    return e // 2, e % 2 == 1


# ---------------------------------------------------------------------------------------------
# Errors (D14)

CLOSED, TIMEOUT, SYS = "closed", "timeout", "sys"  # [Lean: NetErr]
ERR_CODE = {CLOSED: 1, TIMEOUT: 2, SYS: 3}         # [Lean: NetErr.code]
CODE_ERR = {v: k for k, v in ERR_CODE.items()}
EOF_CODE = 4                                        # [Lean: readRes] EOF's code


def err_code(res):
    """[Lean: errCode]"""
    return 0 if res is None else ERR_CODE[res]


# ---------------------------------------------------------------------------------------------
# Read results [Lean: ReadRes]: ("bytes", bs) | ("eof",) | ("err", e). (v3.2, D22: a read that
# waits stutters; no result of its own.)

def R_BYTES(bs):
    return ("bytes", bytes(bs))


R_EOF = ("eof",)


def R_ERR(e):
    return ("err", e)


def read_avail(st, d, n, r, d2):
    """[Lean: ReadAvail st d n r d'] a read of n > 0 bytes at an open end, from d as it is.

    The first disjunct's `∃ k` is decided at k = |bs| for r = .bytes bs: `r = .bytes (d.bytes.take
    k)` with `k ≤ d.bytes.length` makes |bs| = k."""
    # the first k unread bytes
    if r[0] == "bytes":
        k = len(r[1])
        if (1 <= k and k <= n and k <= len(d.bytes) and r[1] == d.bytes[:k]
                and d2 == d._replace(bytes=d.bytes[k:])):
            return True
    # EOF: nothing unread, and the writer is done
    if d.bytes == b"" and d.status != OPEN and r == R_EOF and d2 == d:
        return True
    # an error, once the connection broke and nothing is unread (v3.5)
    if d.status == CUT and d.bytes == b"" and r == R_ERR(SYS) and d2 == d:
        return True
    # a timeout
    if st.rdl and r == R_ERR(TIMEOUT) and d2 == d:
        return True
    return False


def _cut_keep_candidates(d, r, d2):
    """The candidates for ReadOutcome's `∃ k, k ≤ d.bytes.length ∧ ReadAvail st ⟨d.bytes.take k,
    .cut⟩ n r d'`: in every disjunct of ReadAvail, d' is ⟨take k, cut⟩ with a prefix dropped (the
    bytes read, r's bytes), so k = |r's bytes| + |d'.bytes| is the only candidate."""
    k = len(d2.bytes) + (len(r[1]) if r[0] == "bytes" else 0)
    return [k]


def read_outcome(st, d, n, r, d2, keep=None):
    """[Lean: ReadOutcome st d n r d'] D1. `keep`, if given, is the witness of the cut's `∃ k` (the
    kept prefix); else it is decided at its only candidate (`_cut_keep_candidates`)."""
    if st.closed:
        return r == R_ERR(CLOSED) and d2 == d
    elif n == 0:
        return r == R_BYTES(b"") and d2 == d
    else:
        if read_avail(st, d, n, r, d2):
            return True
        # the connection breaks now
        ks = [keep] if keep is not None else _cut_keep_candidates(d, r, d2)
        return any(k <= len(d.bytes) and read_avail(st, NetDir(d.bytes[:k], CUT), n, r, d2) for k in ks)


def write_outcome(st, d, rs, k, res, d2):
    """[Lean: WriteOutcome st d rs k res d'] D2, D15: ONE STEP of a Write, of the bytes `rs` it has
    not written yet; `k` the count it adds, `res` None (the Write goes on unless it has written
    everything) or the failure's kind. The trusted `conn.Write.impl` loops over these steps
    (net.lean's `model.writeLoop`, Go's `poll.FD.Write`): the call returns (the steps' total, nil)
    once it is len(b), else (the total, err) at its first failing step. (v3.1, b334f68554.) A step
    that does not fail counts at least one byte unless `rs` is empty (v3.2, D22: one that would
    count none is a wait, a stutter)."""
    if st.closed:
        return k == 0 and res == CLOSED and d2 == d
    if d.status == FIN:
        return k == 0 and d2 == d and (res == SYS or (st.wdl and res == TIMEOUT))
    if d.status == CUT:
        # discarded
        return d2 == d and ((k <= len(rs) and (1 <= k or rs == b"") and res is None) or
                            (k == 0 and (res == SYS or (st.wdl and res == TIMEOUT))))
    # .open
    return (
        # the first k bytes (all, or some: the buffer full)
        (k <= len(rs) and (1 <= k or rs == b"") and res is None and
         d2 == d._replace(bytes=d.bytes + rs[:k])) or
        # the connection breaks
        (k == 0 and res == SYS and d2 == d._replace(status=CUT)) or
        # a timeout
        (st.wdl and k == 0 and res == TIMEOUT and d2 == d))


def shut(d):
    """[Lean: NetDir.shut]"""
    return d._replace(status=FIN) if d.status == OPEN else d


def close_outcome(st, d, res, st2, d2):
    """[Lean: CloseOutcome st d res st' d'] D3, D17."""
    if st.closed:
        return res == CLOSED and st2 == st and d2 == d
    return res is None and st2 == st._replace(closed=True) and d2 == shut(d)


def close_write_outcome(st, d, res, d2):
    """[Lean: CloseWriteOutcome st d res d'] D4."""
    if st.closed:
        return res == CLOSED and d2 == d
    return (res is None and d2 == shut(d)) or (res == SYS and d2 == d)


def deadline_outcome(st, kind, set_, res, st2):
    """[Lean: DeadlineOutcome st kind set res st'] D5 (`kind`: 0 both, 1 read, 2 write)."""
    if st.closed:
        return res == CLOSED and st2 == st
    return res is None and st2 == st._replace(rdl=st.rdl if kind == 2 else set_,
                                              wdl=st.wdl if kind == 1 else set_)


def keep_idle_valid(d):
    """[Lean: keepIdleValid d] D24: Go's setKeepAliveIdle (tcpsockopt_unix.go) of the
    time.Duration `d` (an int64, as a w64): None for d < 0 (no system call); else TCP_KEEPIDLE of
    int32((d' + 1s - 1) / 1s), d' = 15 s for d = 0, valid iff in 1..32767 (Linux's
    MAX_TCP_KEEPIDLE). Go's int64 arithmetic wraps, its division truncates toward zero."""
    def s64(x):
        x %= W64
        return x - W64 if x >= W64 // 2 else x
    di = s64(d)
    if di < 0:
        return None
    if di == 0:
        di = 15 * 10 ** 9
    t = s64(di + 10 ** 9 - 1)
    q = abs(t) // 10 ** 9 * (1 if t >= 0 else -1)
    n = q % (1 << 32)
    n = n - (1 << 32) if n >= 1 << 31 else n
    return 1 <= n <= 32767


def sock_opt_valid(kind, x):
    """[Lean: sockOptValid kind x] D24: kind 1 is TCP_KEEPIDLE of the duration x
    (keep_idle_valid), any other kind an option Linux never refuses (True)."""
    return keep_idle_valid(x) if kind == 1 else True


def sock_opt_outcome(st, valid, res):
    """[Lean: SockOptOutcome st valid res] D24: no system call (None): success; else `closed` on a
    closed end, success for a valid value, `sys` (EINVAL) for another."""
    if valid is None:
        return res is None
    if st.closed:
        return res == CLOSED
    return res is None if valid else res == SYS


def time_is_zero(wall, ext):
    """[Lean: timeIsZero] Go's Time.IsZero of a time.Time's two words."""
    return wall == 0 and ext == 0


# ---------------------------------------------------------------------------------------------
# Addresses (D6, D7, D8, D20, D21; v3.4: no plan, an address is valid or not by its spelling)

def strip_prefix(p, a):
    """[Lean: stripPrefix p a]"""
    return a[len(p):] if a.startswith(p) else None


def wild_port(a):
    """[Lean: wildPort] `(stripPrefix ":" a).or ((stripPrefix "0.0.0.0:" a).or (stripPrefix
    "[::]:" a))`."""
    for p in (b":", b"0.0.0.0:", b"[::]:"):
        r = strip_prefix(p, a)
        if r is not None:
            return r
    return None


def port_of(a):
    """[Lean: portOf] what follows the first `:`."""
    i = a.find(b":")
    return None if i < 0 else a[i + 1:]


def is_digit(c):
    """[Lean: isDigit]"""
    return 48 <= c <= 57


def digits_val(s, acc):
    """[Lean: digitsVal]"""
    for c in s:
        if not is_digit(c):
            return None
        acc = acc * 10 + (c - 48)
    return acc


def dec_nat(s):
    """[Lean: decNat] digits, at least one, no leading zero."""
    if len(s) == 0:
        return None
    if len(s) == 1:
        return digits_val(s, 0)
    return None if s[0] == 48 else digits_val(s, 0)


def split_by(sep, s):
    """[Lean: splitBy sep s []]"""
    return s.split(bytes([sep]))


def parse_addr(a):
    """[Lean: parseAddr]"""
    parts = split_by(58, a)
    if len(parts) != 2:
        return None
    ip, p = parts
    octs = split_by(46, ip)
    if len(octs) != 4:
        return None
    vals = [dec_nat(x) for x in octs] + [dec_nat(p)]
    if any(v is None for v in vals):
        return None
    return tuple(vals)


def port_ok(p):
    """[Lean: portOk] D20: not 0, at most 65535, outside 32768-60999."""
    return 1 <= p and p <= 65535 and (p < 32768 or 60999 < p)


def addr_ok(a):
    """[Lean: addrOk] D20."""
    r = parse_addr(a)
    if r is None:
        return False
    n1, n2, n3, n4, p = r
    return 1 <= n1 and n1 < 224 and n2 <= 255 and n3 <= 255 and n4 <= 255 and port_ok(p)


def wild_ok(a):
    """[Lean: wildOk] D21: a wildcard spelling whose port is canonical and valid."""
    p = wild_port(a)
    if p is None:
        return False
    n = dec_nat(p)
    return n is not None and port_ok(n)


def listen_ok(a):
    """[Lean: listenOk] D6, D21: `addrOk a || wildOk a`."""
    return addr_ok(a) or wild_ok(a)


def lis_accepts(la, a):
    """[Lean: lisAccepts la a] D7, D21: `la = a ∨ ∃ p, wildPort la = some p ∧ portOf a = some p`
    (the `∃ p` at its only candidate, wildPort la)."""
    if la == a:
        return True
    p = wild_port(la)
    return p is not None and port_of(a) == p


def addr_port(a):
    """Not in Impl.lean: the port string of a valid address or wildcard (`portOf`, or `wildPort`
    for a wildcard), the checker's component key. Every valid Dial address `x` a listener at `la`
    takes (`lis_accepts`) has `addr_port(x) == addr_port(la)`."""
    p = wild_port(a)
    return p if p is not None else port_of(a)


# ---------------------------------------------------------------------------------------------
# The step relation. An expression e' is represented by its value: a pair (word, code) for the
# operations that return one (`PairV`), a code for those that return a word, a ReadRes for Read.
# A stutter (`NetStep`'s other case, D22: `e' = op`, nothing changed) is not a step of a trace: a
# call that waits leaves none, so none is transcribed; nor are the panics of invalid uses
# (`IsNetStep`'s `OrInvalid`), which no traced call makes (an argument outside them has no step
# here).

def read_step(c, s, n, g, r, g2, keep=None):
    """[Lean: ReadStep c s n g e' g'] (e' = Val r.toVal, r given)."""
    cn = g.conns.get(c)
    if cn is None:
        return False
    # ∃ d': the only candidate is g2's direction (g' = g.setConn c (cn.setOut (!s) d'))
    cn2 = g2.conns.get(c)
    if cn2 is None:
        return False
    d2 = out(cn2, not s)
    return (read_outcome(end_st(cn, s), out(cn, not s), n, r, d2, keep) and
            g2 == g.set_conn(c, set_out(cn, not s, d2)))


def write_last(rs, k, res):
    """[Lean: writeLast rs k res] D25: the step ends its Write's loop (it fails, or it writes
    every byte left)."""
    return res is not None or k == len(rs)


def write_step(c, s, bs, first, g, k, res, g2):
    """[Lean: WriteStep c s bs first g e' g'] e' = (k, errCode res). D25: a Write's first step
    (`first`) takes the end's write lock, which must be free (else the step waits: a stutter, no
    outcome), a later one holds it; the lock is held after the step unless it is the loop's last."""
    cn = g.conns.get(c)
    cn2 = g2.conns.get(c)
    if cn is None or cn2 is None:
        return False
    d2 = out(cn2, s)
    return (lock(cn, s) == (not first) and 0 <= k < W64 and
            write_outcome(end_st(cn, s), out(cn, s), bs, k, res, d2) and
            g2 == g.set_conn(c, set_lock(set_out(cn, s, d2), s, not write_last(bs, k, res))))


def close_step(c, s, g, res, g2):
    """[Lean: CloseStep c s g e' g'] e' = errCode res."""
    cn = g.conns.get(c)
    cn2 = g2.conns.get(c)
    if cn is None or cn2 is None:
        return False
    st2, d2 = end_st(cn2, s), out(cn2, s)
    return (close_outcome(end_st(cn, s), out(cn, s), res, st2, d2) and
            g2 == g.set_conn(c, set_out(set_end(cn, s, st2), s, d2)))


def close_write_step(c, s, g, res, g2):
    """[Lean: CloseWriteStep c s g e' g']"""
    cn = g.conns.get(c)
    cn2 = g2.conns.get(c)
    if cn is None or cn2 is None:
        return False
    d2 = out(cn2, s)
    return (close_write_outcome(end_st(cn, s), out(cn, s), res, d2) and
            g2 == g.set_conn(c, set_out(cn, s, d2)))


def set_deadline_step(c, s, kind, set_, g, res, g2):
    """[Lean: SetDeadlineStep c s kind set g e' g']"""
    cn = g.conns.get(c)
    cn2 = g2.conns.get(c)
    if cn is None or cn2 is None:
        return False
    st2 = end_st(cn2, s)
    return (deadline_outcome(end_st(cn, s), kind, set_, res, st2) and
            g2 == g.set_conn(c, set_end(cn, s, st2)))


def fail_v(e):
    """[Lean: failV e] no id, and the kind's code."""
    return (0, ERR_CODE[e])


def new_conn(g, c):
    """[Lean: NewConn g c]"""
    return c != 0 and c not in g.conns and 2 * c + 1 < W64


def dial_step(a, g, e2, g2):
    """[Lean: DialStep a g e' g'] D8, D16. The `∃ c` of the second and third disjuncts: the only
    candidate is the connection g2 has and g has not."""
    if not addr_ok(a):
        return False
    if e2 == fail_v(SYS) and g2 == g:
        return True
    new = [c for c in g2.conns if c not in g.conns]
    for c in new:
        if (new_conn(g, c) and e2 == (end_id(c, False), 0) and
                g2 == g.set_conn(c, conn_fresh(a))):
            return True
        # D16: a failure that leaves the connection, abandoned
        if new_conn(g, c) and e2 == fail_v(SYS) and g2 == g.set_conn(c, conn_abandoned(a)):
            return True
    return False


def accept_step(a, is_open, g, e2, g2):
    """[Lean: AcceptStep a isOpen g e' g'] D7, D21 (`a` the listener's address). The `∃ c cn`:
    the only candidate is the connection that g2 has accepted and g has not."""
    if not is_open and e2 == fail_v(CLOSED) and g2 == g:
        return True
    if is_open and e2 == fail_v(SYS) and g2 == g:
        return True
    if is_open:
        for c, cn in g.conns.items():
            if (lis_accepts(a, cn.addr) and cn.accepted is False and 2 * c + 1 < W64 and
                    e2 == (end_id(c, True), 0) and
                    g2 == g.set_conn(c, cn._replace(accepted=True))):
                return True
    return False


def listen_step(a, L, e2, L2):
    """[Lean: ListenStep a L e' L'] D6, D21 (v3.4: no plan, no host; the listener is at `a`
    itself). The `∃ l` at the listener L2 has and L has not."""
    if e2 == fail_v(SYS) and L2 == L:
        return True
    if not all(v != (a, True) for v in L.lis.values()):
        return False
    for l in L2.lis:
        if (l != 0 and l not in L.lis and e2 == (l, 0) and
                L2 == NetLocal({**L.lis, l: (a, True)})):
            return True
    return False


def lis_close_outcome(is_open, res, is_open2):
    """[Lean: LisCloseOutcome isOpen res isOpen'] D9, D17."""
    if is_open:
        return res is None and is_open2 is False
    return res == CLOSED and is_open2 is False


def net_step(op, v, L, g, e2, L2, g2, keep=None):
    """[Lean: NetStep op v h L g e' h' L' g', its outcome rules on valid arguments: IsNetStep's
    steps, not the stutter nor the panics, D22] (the heap, unchanged, left out; `v` the argument as
    a Python value: Listen, Dial an address; Accept, LisClose a listener id; Read (e, n); Write
    (e, bs, first); Close, CloseWrite e; SetDeadline (e, kind, wall, ext); SetSockopt (e, kind, x)). The operations "AnyBool",
    "AnyString", "AnyW64", "AnyErrno" are not steps of a trace (they are the trusted models'
    choices of the parts of a Go value the model does not explain) and are not transcribed."""
    if op == "Listen":
        return listen_ok(v) and listen_step(v, L, e2, L2) and g2 == g
    if op == "Accept":
        l = v
        if l not in L.lis:
            return False
        a, o = L.lis[l]
        return accept_step(a, o, g, e2, g2) and L2 == L
    if op == "LisClose":
        l = v
        if l not in L.lis or l not in L2.lis:
            return False
        a, o = L.lis[l]
        o2 = L2.lis[l][1]
        res = None if e2 == 0 else CODE_ERR.get(e2)
        return (g2 == g and lis_close_outcome(o, res, o2) and e2 == err_code(res) and
                L2 == NetLocal({**L.lis, l: (a, o2)}))
    if op == "Dial":
        return dial_step(v, g, e2, g2) and L2 == L
    if op == "Read":
        e, n = v
        c, s = decode_end(e)
        return is_end(e, c, s) and read_step(c, s, n, g, e2, g2, keep) and L2 == L
    if op == "Write":
        e, bs, first = v
        c, s = decode_end(e)
        k, code = e2
        res = None if code == 0 else CODE_ERR.get(code, "?")
        return is_end(e, c, s) and write_step(c, s, bs, first, g, k, res, g2) and L2 == L
    if op == "SetSockopt":
        e, kind, x = v
        c, s = decode_end(e)
        cn = g.conns.get(c)
        res = None if e2 == 0 else CODE_ERR.get(e2, "?")
        return (is_end(e, c, s) and cn is not None and g2 == g and L2 == L and
                sock_opt_outcome(end_st(cn, s), sock_opt_valid(kind, x), res))
    if op in ("Close", "CloseWrite"):
        c, s = decode_end(v)
        res = None if e2 == 0 else CODE_ERR.get(e2, "?")
        f = close_step if op == "Close" else close_write_step
        return is_end(v, c, s) and f(c, s, g, res, g2) and L2 == L
    if op == "SetDeadline":
        e, kind, wall, ext = v
        c, s = decode_end(e)
        res = None if e2 == 0 else CODE_ERR.get(e2, "?")
        return (is_end(e, c, s) and
                set_deadline_step(c, s, kind, not time_is_zero(wall, ext), g, res, g2) and L2 == L)
    return False


def crash(L, L2):
    """[Lean: net_semantics.crash] D10: the listeners dropped (`L' = { L with lis := ∅ }`)."""
    return L2 == NetLocal({})
