"""A literal transcription of the TCP extension's semantics, `GooseLang/Ext/Tcp/Impl.lean` (v3,
D1-D22, v3.2), and of `Deploy.lean`'s `PlanWellFormed` (D20). NOT PROVED to agree with the Lean: each
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
every update copies); `Bool` a bool; `Option TcpErr` `None` or one of the kind strings; a `w64`
an int in [0, 2^64).
"""

from typing import NamedTuple

W64 = 1 << 64

# ---------------------------------------------------------------------------------------------
# States

OPEN, FIN, CUT = "open", "fin", "cut"  # [Lean: TcpStatus] .open .fin .cut


class TcpDir(NamedTuple):
    """[Lean: TcpDir] bytes written and not yet read, oldest first; status."""
    bytes: bytes
    status: str


DIR_FRESH = TcpDir(b"", OPEN)  # [Lean: TcpDir.fresh]


class TcpEnd(NamedTuple):
    """[Lean: TcpEnd] closed, read deadline set, write deadline set."""
    closed: bool
    rdl: bool
    wdl: bool


END_FRESH = TcpEnd(False, False, False)  # [Lean: TcpEnd.fresh]


class TcpConn(NamedTuple):
    """[Lean: TcpConn] addr, accepted, dEnd (side False = 0, the dialer's), aEnd (side True = 1),
    up (from the dialer to the acceptor), down (from the acceptor to the dialer)."""
    addr: bytes
    accepted: bool
    dEnd: TcpEnd
    aEnd: TcpEnd
    up: TcpDir
    down: TcpDir


def conn_fresh(a):
    """[Lean: TcpConn.fresh]"""
    return TcpConn(a, False, END_FRESH, END_FRESH, DIR_FRESH, DIR_FRESH)


def conn_abandoned(a):
    """[Lean: TcpConn.abandoned] D16: pending, the dialer's end closed, its direction shut and
    empty."""
    return TcpConn(a, False, END_FRESH._replace(closed=True), END_FRESH, TcpDir(b"", FIN), DIR_FRESH)


def end_st(c, s):
    """[Lean: TcpConn.endSt] (`s` a bool: False the dialer, True the acceptor)."""
    return c.aEnd if s else c.dEnd


def out(c, s):
    """[Lean: TcpConn.out] the direction from the end `s` (the one it writes)."""
    return c.down if s else c.up


def set_end(c, s, st):
    """[Lean: TcpConn.setEnd]"""
    return c._replace(aEnd=st) if s else c._replace(dEnd=st)


def set_out(c, s, d):
    """[Lean: TcpConn.setOut]"""
    return c._replace(down=d) if s else c._replace(up=d)


class TcpGlobal(NamedTuple):
    """[Lean: TcpGlobal] plan (address -> host), conns (number -> TcpConn)."""
    plan: dict
    conns: dict

    def set_conn(self, c, cn):
        """[Lean: TcpGlobal.setConn]"""
        conns = dict(self.conns)
        conns[c] = cn
        return TcpGlobal(self.plan, conns)


class TcpLocal(NamedTuple):
    """[Lean: TcpLocal] host; lis (listener id -> (address, open))."""
    host: bytes
    lis: dict


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

CLOSED, TIMEOUT, SYS = "closed", "timeout", "sys"  # [Lean: TcpErr]
ERR_CODE = {CLOSED: 1, TIMEOUT: 2, SYS: 3}         # [Lean: TcpErr.code]
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
    # an error, once the connection broke
    if d.status == CUT and r == R_ERR(SYS) and d2 == d:
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
        return any(k <= len(d.bytes) and read_avail(st, TcpDir(d.bytes[:k], CUT), n, r, d2) for k in ks)


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
    """[Lean: TcpDir.shut]"""
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


def time_is_zero(wall, ext):
    """[Lean: timeIsZero] Go's Time.IsZero of a time.Time's two words."""
    return wall == 0 and ext == 0


# ---------------------------------------------------------------------------------------------
# Addresses (D6, D21)

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


def listen_at(plan, host, a, a0):
    """[Lean: ListenAt plan host a a0] D6, D21. The `∀ x, (plan !! x).isSome → ...` ranges over
    the plan's keys (`plan !! x` is `none` elsewhere)."""
    if plan.get(a0) != host:
        return False
    if a0 == a:
        return True
    if plan.get(a) is not None:
        return False
    p = wild_port(a)
    return (p is not None and port_of(a0) == p and
            all(x == a0 for x in plan if port_of(x) == p))


def listen_resolve(plan, host, a):
    """The a0 with `ListenAt plan host a a0`, if any (it is unique: Impl.lean's `listenAt_unique`;
    the candidates are a itself and the plan's keys)."""
    for a0 in [a] + list(plan):
        if listen_at(plan, host, a, a0):
            return a0
    return None


# ---------------------------------------------------------------------------------------------
# The step relation. An expression e' is represented by its value: a pair (word, code) for the
# operations that return one (`PairV`), a code for those that return a word, a ReadRes for Read.
# A stutter (`TcpStep`'s other case, D22: `e' = op`, nothing changed) is not a step of a trace: a
# call that waits leaves none, so none is transcribed; nor are the panics of invalid uses
# (`IsTcpStep`'s `OrInvalid`), which no traced call makes (an argument outside them has no step
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


def write_step(c, s, bs, g, k, res, g2):
    """[Lean: WriteStep c s bs g e' g'] e' = (k, errCode res)."""
    cn = g.conns.get(c)
    cn2 = g2.conns.get(c)
    if cn is None or cn2 is None:
        return False
    d2 = out(cn2, s)
    return (0 <= k < W64 and write_outcome(end_st(cn, s), out(cn, s), bs, k, res, d2) and
            g2 == g.set_conn(c, set_out(cn, s, d2)))


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
    if g.plan.get(a) is None:
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
    """[Lean: AcceptStep a isOpen g e' g'] D7. The `∃ c cn`: the
    only candidate is the connection that g2 has accepted and g has not."""
    if not is_open and e2 == fail_v(CLOSED) and g2 == g:
        return True
    if is_open and e2 == fail_v(SYS) and g2 == g:
        return True
    if is_open:
        for c, cn in g.conns.items():
            if (cn.addr == a and cn.accepted is False and 2 * c + 1 < W64 and
                    e2 == (end_id(c, True), 0) and
                    g2 == g.set_conn(c, cn._replace(accepted=True))):
                return True
    return False


def listen_step(a, g, L, e2, L2):
    """[Lean: ListenStep a g L e' L'] D6, D21. The `∃ a0` is decided at listen_resolve's (unique)
    a0, the `∃ l` at the listener L2 has and L has not."""
    a0 = listen_resolve(g.plan, L.host, a)
    if a0 is None:
        return False
    if e2 == fail_v(SYS) and L2 == L:
        return True
    if not all(v != (a0, True) for v in L.lis.values()):
        return False
    for l in L2.lis:
        if (l != 0 and l not in L.lis and e2 == (l, 0) and
                L2 == TcpLocal(L.host, {**L.lis, l: (a0, True)})):
            return True
    return False


def lis_close_outcome(is_open, res, is_open2):
    """[Lean: LisCloseOutcome isOpen res isOpen'] D9, D17."""
    if is_open:
        return res is None and is_open2 is False
    return res == CLOSED and is_open2 is False


def tcp_step(op, v, L, g, e2, L2, g2, keep=None):
    """[Lean: TcpStep op v h L g e' h' L' g', its outcome rules on valid arguments: IsTcpStep's
    steps, not the stutter nor the panics, D22] (the heap, unchanged, left out; `v` the argument as
    a Python value: Listen, Dial an address; Accept, LisClose a listener id; Read (e, n); Write
    (e, bs); Close, CloseWrite e; SetDeadline (e, kind, wall, ext)). The operations "AnyBool",
    "AnyString", "AnyW64", "AnyErrno" are not steps of a trace (they are the trusted models'
    choices of the parts of a Go value the model does not explain) and are not transcribed."""
    if op == "Listen":
        return listen_step(v, g, L, e2, L2) and g2 == g
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
                L2 == TcpLocal(L.host, {**L.lis, l: (a, o2)}))
    if op == "Dial":
        return dial_step(v, g, e2, g2) and L2 == L
    if op == "Read":
        e, n = v
        c, s = decode_end(e)
        return is_end(e, c, s) and read_step(c, s, n, g, e2, g2, keep) and L2 == L
    if op == "Write":
        e, bs = v
        c, s = decode_end(e)
        k, code = e2
        res = None if code == 0 else CODE_ERR.get(code, "?")
        return is_end(e, c, s) and write_step(c, s, bs, g, k, res, g2) and L2 == L
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
    """[Lean: tcp_semantics.crash] D10: the host kept, the listeners dropped."""
    return L2 == TcpLocal(L.host, {})


# ---------------------------------------------------------------------------------------------
# Deploy.lean (D20)

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


def addr_ok(a):
    """[Lean: addrOk]"""
    r = parse_addr(a)
    if r is None:
        return False
    n1, n2, n3, n4, p = r
    return (1 <= n1 and n1 < 224 and n2 <= 255 and n3 <= 255 and n4 <= 255 and
            1 <= p and p <= 65535 and (p < 32768 or 60999 < p))


def keys_distinct(l):
    """[Lean: keysDistinct]"""
    keys = [a for a, _ in l]
    return len(keys) == len(set(keys))


def plan_well_formed(l):
    """[Lean: PlanWellFormed l] for the plan as a list of (address, host) pairs."""
    return keys_distinct(l) and all(addr_ok(a) for a, _ in l)
