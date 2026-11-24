"""The search's states and steps: the model of model.py (Impl.lean) with its hidden choices taken
lazily, so that the linearization search (lincheck.py) need not enumerate them. README.md,
"Lazy cuts and prefixes", proves that this is exact: a lazy state stands for a set of the model's
states (its concretization, `gamma` below), and each lazy step's successors stand, together, for
exactly the model states that the model's step (with every hidden choice) reaches from that set
with the same observed result. So a history is admitted by the lazy steps iff it is admitted by
the model's. The witness is then made concrete, and checked against model.py, by replay.py.

The hidden choices of the model, for a connection: when a direction is cut (a Read of it, D1;
a Write into it that fails with `sys`, D2), and how many of its bytes a cut keeps (D1's `∃ k`).
The rest of a connection's step is determined by the operation and its observed result.

A direction, lazily, is `(segs, n, status, a)`:
  - `segs`, `n`: its bytes (a tuple of (write id, lo, hi) slices of the component's writes, and
    their total length: the bytes are those of the model's NetDir);
  - `status`: OPEN, FIN or CUT;
  - `a`: for an OPEN or FIN direction, the number of bytes appended since the last Read of it by
    its reader (a Read of n > 0 bytes at an open end: a cut point, D1), or None if it has had no
    such Read. A CUT direction has `a` None.
gamma((B, st, a)) = {(B, st)} ∪ {(P, cut) : P a prefix of B[:|B| - a]} if a is not None (and st is
OPEN or FIN): the direction as it is, or cut at its reader's last Read keeping every byte it had,
with the bytes written since discarded; gamma((B, cut, _)) = {(P, cut) : P a prefix of B}: a cut
direction stands for every prefix of its bytes (a later Read may cut it again, keeping any prefix:
ReadOutcome's second disjunct applies to a cut direction too).

Every step function returns (successors, reason): a list of (state, choice) and, when it is empty,
why. `choice` is what the witness needs of a step whose result the trace does not have (an
operation cut short by its process's end): the result chosen, as a dict.
"""

import model as M

OPEN, FIN, CUT = M.OPEN, M.FIN, M.CUT
CLOSED, TIMEOUT, SYS = M.CLOSED, M.TIMEOUT, M.SYS

# ---------------------------------------------------------------------------------------------
# Byte sequences as slices of the component's writes (W: write id -> bytes)


def seg_take(segs, k):
    out = []
    for w, lo, hi in segs:
        if k <= 0:
            break
        m = min(hi - lo, k)
        out.append((w, lo, lo + m))
        k -= m
    return tuple(out)


def seg_drop(segs, k):
    out = []
    for w, lo, hi in segs:
        if k >= hi - lo:
            k -= hi - lo
            continue
        out.append((w, lo + k, hi))
        k = 0
    return tuple(out)


def seg_startswith(segs, data, W):
    pos = 0
    mv = memoryview(data)
    for w, lo, hi in segs:
        if pos >= len(data):
            break
        m = min(hi - lo, len(data) - pos)
        if memoryview(W[w])[lo:lo + m] != mv[pos:pos + m]:
            return False
        pos += m
    return pos >= len(data)


def seg_bytes(segs, W):
    return b"".join(W[w][lo:hi] for w, lo, hi in segs)


def seg_append(segs, w, k):
    return segs + ((w, 0, k),) if k > 0 else segs


def seg_append_range(segs, w, lo, hi):
    return segs + ((w, lo, hi),) if hi > lo else segs


DIR_FRESH = ((), 0, OPEN, None)
DIR_ABANDONED = ((), 0, FIN, None)  # Impl: NetConn.abandoned's `up`


def ldir(d, W):
    """The model's NetDir for the lazy direction as it is (its gamma's first member)."""
    return M.NetDir(seg_bytes(d[0], W), d[2])


def gamma(d, W):
    """The concretization of a lazy direction, as a set of model NetDirs (for the tests)."""
    b = seg_bytes(d[0], W)
    if d[2] == CUT:
        return {M.NetDir(b[:i], CUT) for i in range(len(b) + 1)}
    out = {M.NetDir(b, d[2])}
    if d[3] is not None:
        keep = len(b) - d[3]
        out |= {M.NetDir(b[:i], CUT) for i in range(keep + 1)}
    return out


def shut(d):
    """Impl: NetDir.shut. gamma commutes with it: a cut member stays cut."""
    return (d[0], d[1], FIN, d[3]) if d[2] == OPEN else d


def _after_read(d, segs, n):
    """The direction after a cut point that keeps it as it is: `a` becomes 0."""
    return (segs, n, d[2], None if d[2] == CUT else 0)


# ---------------------------------------------------------------------------------------------
# A connection: (dEnd, aEnd, up, down, inflight), ends as model.NetEnd; side 0 the dialer, 1 the
# acceptor. Impl: NetConn without `addr` and `accepted` (the address component's). `inflight`: the
# Write calls that have taken steps and not finished, as (op index, progress so far, side): a Go
# Write is a loop of the extension's steps (poll.FD.Write), each at its own point in the call's
# interval; the search's record of where each call is in its loop, and (v3.3, D25) the model's
# write locks: an end's lock is held exactly while a Write of that end is in flight.

END_FRESH = M.END_FRESH
CONN_FRESH = (END_FRESH, END_FRESH, DIR_FRESH, DIR_FRESH, frozenset())
CONN_ABANDONED = (END_FRESH._replace(closed=True), END_FRESH, DIR_ABANDONED, DIR_FRESH, frozenset())


def set_dir(c, i, d):
    return (c[0], c[1], d, c[3], c[4]) if i == 0 else (c[0], c[1], c[2], d, c[4])


def set_end(c, s, e):
    return (e, c[1], c[2], c[3], c[4]) if s == 0 else (c[0], e, c[2], c[3], c[4])


def progress(c, j):
    for x, p, _ in c[4]:
        if x == j:
            return p
    return 0


def set_progress(c, j, p, s=None):
    """p None: the call is done (removed); else its progress, the call a Write of the end s."""
    fl = frozenset(x for x in c[4] if x[0] != j)
    if p is not None:
        fl = fl | {(j, p, s)}
    return (c[0], c[1], c[2], c[3], fl)


def lock_holder(c, s, j, dn):
    """Impl: NetConn.lock (D25). The other Write of the end s in flight (holding its write lock),
    if any; `dn(i)` says whether operation i is done (a dropped unfinished call: its process
    ended)."""
    for x, _, xs in c[4]:
        if x != j and xs == s and not dn(x):
            return x
    return None


def _none(why):
    return [], why


def read(c, s, n, r, W):
    """Impl: ReadOutcome (the reader's end s, the direction towards it, from 1 - s), lazily.

    r is the observed result: ("bytes", bs) | ("eof",) | ("err", kind). A Read of n > 0 bytes at an
    open end is a cut point: the successor's `a` is 0 (gamma: cut here, keeping everything).
      - bytes: a prefix of the direction (cut or not); no cut needed (gamma covers the cut ones);
      - EOF: as it is if empty and FIN (or CUT); else a cut keeping nothing;
      - sys: a cut keeping nothing (v3.5: a sys error needs nothing unread; the cut direction
        as it is if it is empty);
      - timeout: with the read deadline, as it is.
    """
    st = c[s]
    d = c[2 + (1 - s)]
    if st.closed:
        if r == M.R_ERR(CLOSED):
            return [(c, None)], None
        return _none("the end is closed (by its own Close, linearized before): ReadOutcome gives "
                     "only `closed`")
    if n == 0:
        if r == M.R_BYTES(b""):
            return [(c, None)], None
        return _none("a Read with an empty buffer returns nothing at once (ReadOutcome, n = 0)")
    segs, ln, stat, a = d
    kind = r[0]
    if kind == "bytes":
        bs = r[1]
        if len(bs) == 0:
            return _none("a Read of n > 0 bytes returned (0, nil): ReadAvail returns at least 1 byte")
        if len(bs) > n:
            return _none(f"{len(bs)} bytes read into a buffer of {n}")
        if len(bs) > ln or not seg_startswith(segs, bs, W):
            got = seg_bytes(seg_take(segs, min(ln, len(bs) + 8)), W)
            return _none(f"the bytes read are not the next unread bytes of the direction "
                         f"({ln} unread, status {stat}; they begin {_show(got)}, read {_show(bs)})")
        nd = _after_read(d, seg_drop(segs, len(bs)), ln - len(bs))
        return [(set_dir(c, 1 - s, nd), None)], None
    if kind == "eof":
        if ln == 0 and stat == FIN:
            nd = _after_read(d, (), 0)
        else:
            nd = ((), 0, CUT, None)
        return [(set_dir(c, 1 - s, nd), None)], None
    if r == M.R_ERR(SYS):
        return [(set_dir(c, 1 - s, ((), 0, CUT, None)), None)], None
    if r == M.R_ERR(TIMEOUT):
        if not st.rdl:
            return _none("a read timeout with no read deadline set (ReadAvail: `st.rdl = true`)")
        return [(set_dir(c, 1 - s, _after_read(d, segs, ln)), None)], None
    if r == M.R_ERR(CLOSED):
        return _none("`closed` from a Read at an end not closed (ReadOutcome: only on a closed end)")
    return _none(f"no ReadOutcome gives {r}")


def write_step(c, s, w, lo, L, k, res):
    """Impl: WriteOutcome, ONE step of a Write (the writer's end s, the direction from it): the
    remaining bytes are the component's write w from lo to L; progress k (res None) or a failure
    (k = 0). Returns (conn', None) or (None, why).

    The corner (README.md): the one step only a cut direction allows among those a FIN or OPEN one
    does not, progress into a FIN direction (a CloseWrite before it), is admitted iff gamma has a
    cut member, the direction cut at its reader's last Read (`a` not None), keeping what it had
    then. (`closed` comes from a closed end only; every other result the cut case allows, the OPEN
    case does too.)"""
    st = c[s]
    d = c[2 + s]
    segs, ln, stat, a = d
    rl = L - lo
    if st.closed:
        if k == 0 and res == CLOSED:
            return c, None
        return None, "the end is closed: a Write step fails `closed`, writing nothing (WriteOutcome)"
    if res is not None and k != 0:
        return None, "a failing Write step writes nothing"
    if not 0 <= k <= rl:
        return None, f"progress {k} of {rl} remaining bytes"
    if res == TIMEOUT and not st.wdl:
        return None, "a write timeout with no write deadline set at that step (WriteOutcome: `st.wdl = true`)"
    if res == CLOSED:
        return None, ("`closed` from a Write step at an end not closed (WriteOutcome: only once the end "
                      "is closed, by a Close linearized before that step)")
    if stat == OPEN:
        if res is None:
            return set_dir(c, s, (seg_append_range(segs, w, lo, lo + k), ln + k, OPEN,
                                  None if a is None else a + k)), None
        if res == SYS:
            return set_dir(c, s, (segs, ln, CUT, None)), None
        return c, None  # timeout
    if stat == CUT:  # discarded
        return c, None
    # FIN
    if res is not None:  # sys, timeout
        return c, None
    if a is None:  # progress (or an empty Write's one step) with no failure: the cut case only
        return None, (f"a step of {k} bytes with no failure into a direction shut by its writer "
                      "(WriteOutcome: only into a cut one), and no Read of it by the peer could have cut it")
    return set_dir(c, s, (seg_take(segs, ln - a), ln - a, CUT, None)), None


def write(c, s, j, w, L, n, res, dn):
    """The steps of a Write call (the component's op j, write w, L bytes long) that returned
    (n, res): progress steps summing to n, then, for a failure, a failing step (Impl's `poll.FD.Write`
    loop: the count is the progress's sum, the error the last step's). A step's successor is
    partial (the call goes on) unless it is the call's last. No step while another Write of the end
    is in flight (D25, its write lock; `dn` as lock_holder's).

    The progress is taken in one step (all that is left of n): that dominates splitting it, since
    with the write lock no other Write's bytes can come between two of its steps (README.md, "A
    Write is a loop of steps")."""
    h = lock_holder(c, s, j, dn)
    if h is not None:
        return _none(f"the end's write lock is held by the Write {h} in flight (D25: Writes of one end "
                     "do not interleave)")
    if res is None and n != L:
        return _none(f"a successful Write returned {n} of {L} bytes (it loops until all are written)")
    if res is not None and not (n < L or n == 0):
        return _none(f"a failed Write returned all {L} bytes (its last step fails, writing nothing)")
    p = progress(c, j)
    if p < n:
        need = n - p
        nc, why = write_step(c, s, w, p, L, need, None)
        if nc is None:
            return [], why
        if res is None and p + need == L:
            return [(set_progress(nc, j, None), {"k": need})], None
        return [(set_progress(nc, j, p + need, s), {"k": need}, True)], None
    if res is None:  # L == 0: the one step, of nothing, finishes
        nc, why = write_step(c, s, w, 0, 0, 0, None)
        return ([(set_progress(nc, j, None), {"k": 0})], None) if nc is not None else ([], why)
    nc, why = write_step(c, s, w, p, L, 0, res)
    if nc is None:
        return [], why
    return [(set_progress(nc, j, None), {"fail": M.ERR_CODE[res]})], None


def write_pending(c, s, j, w, L, dn):
    """A Write that never returned: any steps, then the process ended (the search may also drop
    it at any point: lincheck's optional operations, which ends it where its steps left it).
    Successors ending the call: every remaining byte written (it finished); all but the last
    written and a sys failure (a cut keeping them). From a FIN or CUT direction or a closed end its
    steps change nothing (gamma covers the cut members of FIN). No step while another Write of the
    end is in flight (D25)."""
    if lock_holder(c, s, j, dn) is not None:
        return _none("the end's write lock is held by another Write in flight (D25)")
    p = progress(c, j)
    rl = L - p
    st = c[s]
    segs, ln, stat, a = c[2 + s]
    done = set_progress(c, j, None)
    if st.closed or stat != OPEN:
        return [(done, {"steps": []})], None
    out = [(set_dir(done, s, (seg_append_range(segs, w, p, L), ln + rl, OPEN, None if a is None else a + rl)),
            {"steps": [{"k": rl}]})]
    km = rl - 1 if rl > 0 else 0
    out.append((set_dir(done, s, (seg_append_range(segs, w, p, p + km), ln + km, CUT, None)),
                {"steps": ([{"k": km}] if km else []) + [{"fail": M.ERR_CODE[SYS]}]}))
    return out, None


def close(c, s, res):
    """Impl: CloseOutcome."""
    st = c[s]
    if st.closed:
        if res == CLOSED:
            return [(c, None)], None
        return _none("a second Close returns `closed` (CloseOutcome)")
    if res is not None:
        return _none(f"Close of an open end returned {res} (CloseOutcome, D17: it succeeds)")
    c2 = set_end(c, s, st._replace(closed=True))
    return [(set_dir(c2, s, shut(c[2 + s])), None)], None


def close_write(c, s, res):
    """Impl: CloseWriteOutcome."""
    st = c[s]
    if st.closed:
        if res == CLOSED:
            return [(c, None)], None
        return _none("CloseWrite of a closed end returns `closed` (CloseWriteOutcome)")
    if res is None:
        return [(set_dir(c, s, shut(c[2 + s])), None)], None
    if res == SYS:
        return [(c, None)], None
    return _none(f"CloseWrite of an open end returned {res} (CloseWriteOutcome: nil or sys)")


def deadline(c, s, kind, set_, res):
    """Impl: DeadlineOutcome."""
    st = c[s]
    if st.closed:
        if res == CLOSED:
            return [(c, None)], None
        return _none("SetDeadline of a closed end returns `closed` (DeadlineOutcome)")
    if res is not None:
        return _none(f"SetDeadline of an open end returned {res} (DeadlineOutcome: it succeeds)")
    st2 = st._replace(rdl=st.rdl if kind == 2 else set_, wdl=st.wdl if kind == 1 else set_)
    return [(set_end(c, s, st2), None)], None


# --- operations cut short by their process's end: the result is not observed, so a step may
# take any outcome. Their successors below stand for every outcome, up to dominance (README.md,
# "Calls cut short"); the search may also leave them out (lincheck's optional operations).

def read_pending(c, s, n, more_reads):
    """A Read that never returned. Successors: a sys error (a cut keeping nothing, v3.5); with the
    read deadline, a timeout; EOF of an empty FIN direction; and, if another Read of the same end
    may still be linearized after it (`more_reads`), each count of bytes it could have taken."""
    st = c[s]
    if st.closed:
        return [(c, {"code": M.ERR_CODE[CLOSED]})], None
    if n == 0:
        return [(c, {"code": 0, "k": 0})], None
    d = c[2 + (1 - s)]
    segs, ln, stat, a = d
    out = [(set_dir(c, 1 - s, ((), 0, CUT, None)), {"code": M.ERR_CODE[SYS]})]
    if st.rdl:
        out.append((set_dir(c, 1 - s, _after_read(d, segs, ln)), {"code": M.ERR_CODE[TIMEOUT]}))
    if ln == 0 and stat == FIN:
        out.append((set_dir(c, 1 - s, _after_read(d, (), 0)), {"code": M.EOF_CODE}))
    if more_reads:
        for k in range(1, min(n, ln) + 1):
            out.append((set_dir(c, 1 - s, _after_read(d, seg_drop(segs, k), ln - k)), {"code": 0, "k": k}))
    return out, None


def close_pending(c, s):
    st = c[s]
    if st.closed:
        return [(c, {"code": M.ERR_CODE[CLOSED]})], None
    r, _ = close(c, s, None)
    return [(r[0][0], {"code": 0})], None


def close_write_pending(c, s):
    st = c[s]
    if st.closed:
        return [(c, {"code": M.ERR_CODE[CLOSED]})], None
    return [(set_dir(c, s, shut(c[2 + s])), {"code": 0})], None


def deadline_pending(c, s, kind, set_):
    st = c[s]
    if st.closed:
        return [(c, {"code": M.ERR_CODE[CLOSED]})], None
    r, _ = deadline(c, s, kind, set_, None)
    return [(r[0][0], {"code": 0})], None


# ---------------------------------------------------------------------------------------------
# A port p (v3.4: no plan; a component per port, since a listener at `la` takes only connections
# dialed to an address with la's port, `lisAccepts`, and a Dial of `a` makes one with a's port):
# (open, pending, tokens). `open`: the open listeners whose address has the port p, as (node,
# listener, address) triples (Impl: each node's NetLocal.lis restricted to them; ListenStep allows
# one open per node and address); `pending`: the connections dialed to an address with port p that
# a Dial in the trace returned, not yet accepted, as (connection, address) pairs (Impl:
# NetConn.accepted = false); `tokens`: how many connections to each address are pending that no
# Dial returned (D16's abandoned ones, and those of Dials cut short by their process's end), a
# sorted tuple of (address, count > 0). Those of one address are interchangeable here: each is
# accepted by at most one Accept, and the connection component of an Accept that took one sees only
# its acceptor's operations, whose outcomes are the same from NetConn.abandoned and from
# NetConn.fresh (README.md, "Accepts no Dial returned"); those of different addresses differ only
# in which listeners take them, so an Accept of one tries each address its listener takes.

ADDR0 = (frozenset(), frozenset(), ())


def _tok_add(tok, a, k):
    d = dict(tok)
    d[a] = d.get(a, 0) + k
    return tuple(sorted((x, n) for x, n in d.items() if n > 0))


def listen(st, node, lid, la, ok):
    """Impl: ListenStep at `la` (listenOk holds: the checker takes only valid Listens)."""
    open_, pend, tok = st
    if not ok:
        return [(st, None)], None
    if any(n == node and x == la for n, _, x in open_):
        return _none("this node has an open listener at the address already (ListenStep: only sys)")
    return [((open_ | {(node, lid, la)}, pend, tok), None)], None


def _is_open(open_, node, lid):
    return any(n == node and l == lid for n, l, _ in open_)


def accept(st, node, lid, la, res, conn):
    """Impl: AcceptStep, of the listener `lid` at `la`. res: None with conn (a connection key, or
    None for one no Dial returned), or a kind. The choice of a connection no Dial returned is
    {"token": its address}: one successor per address with a token that the listener takes."""
    open_, pend, tok = st
    is_open = _is_open(open_, node, lid)
    if res is None:
        if not is_open:
            return _none("the listener is closed (AcceptStep: only `closed`)")
        if conn is None:
            outs = [((open_, pend, _tok_add(tok, a, -1)), {"token": a})
                    for a, _ in tok if M.lis_accepts(la, a)]
            if not outs:
                return _none("no Dial returned this connection, and no failed (or unfinished) Dial "
                             "of an address the listener takes is linearized before it and not yet "
                             "accepted")
            return outs, None
        pa = [x for x in pend if x[0] == conn]
        if not pa:
            return _none("its connection is not pending (not dialed yet, or accepted already)")
        if not M.lis_accepts(la, pa[0][1]):
            return _none(f"its connection was dialed to {pa[0][1].decode()}, which the listener at "
                         f"{la.decode()} does not take (lisAccepts)")
        return [((open_, pend - {pa[0]}, tok), None)], None
    if res == SYS:
        if not is_open:
            return _none("a sys failure of a closed listener (AcceptStep: only `closed`)")
        return [(st, None)], None
    if res == CLOSED:
        if is_open:
            return _none("`closed` from an open listener (AcceptStep: only once it is closed)")
        return [(st, None)], None
    return _none(f"no AcceptStep gives {res}")


def lis_close(st, node, lid, res):
    """Impl: LisCloseOutcome."""
    open_, pend, tok = st
    mine = [x for x in open_ if x[0] == node and x[1] == lid]
    if mine:
        if res is None:
            return [((open_ - {mine[0]}, pend, tok), None)], None
        return _none(f"Close of an open listener returned {res} (LisCloseOutcome, D17: it succeeds)")
    if res == CLOSED:
        return [(st, None)], None
    return _none("a second Close of a listener returns `closed` (LisCloseOutcome)")


def dial_ok(st, conn, a):
    """Impl: DialStep's second disjunct: a new connection to `a`, pending."""
    open_, pend, tok = st
    return [((open_, pend | {(conn, a)}, tok), None)], None


def dial_fail(st, a, res):
    """Impl: DialStep's failures: failV .sys, with no connection or (D16) an abandoned one. The
    second dominates (a pending connection constrains nothing: an Accept may take it or not), so
    it is the only successor; the witness turns one no Accept took into the first."""
    open_, pend, tok = st
    if res != SYS:
        return _none(f"a Dial failure of kind {res} (DialStep: only sys)")
    return [((open_, pend, _tok_add(tok, a, 1)), {"abandoned": True})], None


def dial_pending(st, a):
    """A Dial that never returned: it may have succeeded (DialStep has no other precondition than
    addrOk), leaving a connection pending that no Dial returned; that dominates leaving it out."""
    open_, pend, tok = st
    return [((open_, pend, _tok_add(tok, a, 1)), {"pending": True})], None


def crash(st, node):
    """Impl: net_semantics.crash: the node's listeners are gone."""
    open_, pend, tok = st
    return [((frozenset(x for x in open_ if x[0] != node), pend, tok), None)], None


def _show(b, k=24):
    if len(b) <= k:
        return repr(b)
    return repr(b[:k])[:-1] + f"...'(+{len(b) - k})"
