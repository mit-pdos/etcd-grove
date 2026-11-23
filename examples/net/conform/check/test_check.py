#!/usr/bin/env python3
"""Tests of the conformance checker (README.md, "Tests").

- Model: model.py's decisions of the Lean relations' existentials against a search over every
  witness; Deploy.lean's examples; ListenAt's.
- Lazy against eager: random histories of one connection, decided by the checker's search over the
  lazy model (lazy.py, lincheck.py) and by a brute-force search over every order and every hidden
  choice of model.py's literal relations; the verdicts must agree (the exactness that README.md's
  "Lazy cuts and prefixes" argues).
- Positive hand-made traces (admitted, with a witness that replays), negative ones (not admitted,
  at the operation the test names), scope.
- The committed sample (../testdata/*.tar.gz): every run admitted.
- The mutation check on the sample: every mutant rejected.

Run: python3 -B examples/net/conform/check/test_check.py   (or `go test ./net/conform/check`)
"""

import glob
import itertools
import os
import random
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import checker  # noqa: E402
import lazy as Z  # noqa: E402
import lincheck  # noqa: E402
import model as M  # noqa: E402
import mutate  # noqa: E402
import trace as T  # noqa: E402
from tracebuild import (A1, EOF, Trace, err_closed, err_errtimeout, err_sys, err_timeout,  # noqa: E402
                        setup_conn)

TESTDATA = os.path.join(HERE, "..", "testdata")
OPEN, FIN, CUT = M.OPEN, M.FIN, M.CUT


# ---------------------------------------------------------------------------------------------
# The model

def read_outcome_enum(st, d, n, r, d2):
    """ReadOutcome with its ∃ k decided by trying every k."""
    if st.closed or n == 0:
        return M.read_outcome(st, d, n, r, d2)
    if M.read_avail(st, d, n, r, d2):
        return True
    return any(M.read_avail(st, M.NetDir(d.bytes[:k], CUT), n, r, d2) for k in range(len(d.bytes) + 1))


def all_dirs(maxlen=3, alphabet=b"ab"):
    out = []
    for L in range(maxlen + 1):
        for t in itertools.product(alphabet, repeat=L):
            for s in (OPEN, FIN, CUT):
                out.append(M.NetDir(bytes(t), s))
    return out


ENDS = [M.NetEnd(c, r, w) for c in (False, True) for r in (False, True) for w in (False, True)]
READ_RESULTS = [M.R_BYTES(b""), M.R_BYTES(b"a"), M.R_BYTES(b"ab"), M.R_BYTES(b"b"), M.R_EOF,
                M.R_ERR(M.SYS), M.R_ERR(M.TIMEOUT), M.R_ERR(M.CLOSED)]


class ModelTest(unittest.TestCase):
    def test_read_outcome_exists_k(self):
        dirs = all_dirs(3)
        for st in ENDS:
            for d in dirs:
                for n in (0, 1, 2):
                    for r in READ_RESULTS:
                        for d2 in dirs:
                            self.assertEqual(M.read_outcome(st, d, n, r, d2), read_outcome_enum(st, d, n, r, d2),
                                             (st, d, n, r, d2))

    def test_read_examples(self):
        # Tests.lean: TestReadPartial, its excluded twin, in-order delivery, the empty read
        st0 = M.END_FRESH
        b3 = b"abc"
        self.assertTrue(M.read_outcome(st0, M.NetDir(b3, OPEN), 2, M.R_BYTES(b"a"), M.NetDir(b"bc", OPEN)))
        self.assertFalse(M.read_outcome(st0, M.NetDir(b3, OPEN), 1, M.R_BYTES(b"ab"), M.NetDir(b"c", OPEN)))
        self.assertFalse(M.read_outcome(st0, M.NetDir(b3, OPEN), 3, M.R_BYTES(b"b"), M.NetDir(b"ac", OPEN)))
        stR = st0._replace(rdl=True)
        self.assertTrue(M.read_outcome(stR, M.NetDir(b3, OPEN), 0, M.R_BYTES(b""), M.NetDir(b3, OPEN)))
        # a timeout needs the deadline
        self.assertFalse(M.read_outcome(st0, M.NetDir(b3, OPEN), 3, M.R_ERR(M.TIMEOUT), M.NetDir(b3, OPEN)))
        # a break keeps a prefix; EOF after it
        self.assertTrue(M.read_outcome(st0, M.NetDir(b3, OPEN), 3, M.R_BYTES(b"a"), M.NetDir(b"b", CUT)))
        self.assertTrue(M.read_outcome(st0, M.NetDir(b3, OPEN), 3, M.R_EOF, M.NetDir(b"", CUT)))

    def test_write_examples(self):
        st0, stW, stC = M.END_FRESH, M.END_FRESH._replace(wdl=True), M.END_FRESH._replace(closed=True)
        # one step of a Write (rs: what remains of its bytes)
        o = M.NetDir(b"x", OPEN)
        self.assertTrue(M.write_outcome(st0, o, b"ab", 2, None, M.NetDir(b"xab", OPEN)))  # finishes
        self.assertTrue(M.write_outcome(st0, o, b"ab", 1, None, M.NetDir(b"xa", OPEN)))   # goes on
        self.assertFalse(M.write_outcome(st0, o, b"ab", 3, None, M.NetDir(b"xab", OPEN)))
        self.assertTrue(M.write_outcome(st0, o, b"ab", 0, M.SYS, M.NetDir(b"x", CUT)))
        self.assertFalse(M.write_outcome(st0, o, b"ab", 1, M.SYS, M.NetDir(b"xa", CUT)))  # nothing appended
        self.assertFalse(M.write_outcome(st0, o, b"ab", 0, M.TIMEOUT, o))
        self.assertTrue(M.write_outcome(stW, o, b"ab", 0, M.TIMEOUT, o))
        self.assertFalse(M.write_outcome(st0, o, b"ab", 0, M.CLOSED, o))  # D15 is gone: a Close first
        self.assertTrue(M.write_outcome(stC, o, b"ab", 0, M.CLOSED, o))
        self.assertFalse(M.write_outcome(stC, o, b"ab", 2, None, M.NetDir(b"xab", OPEN)))
        f = M.NetDir(b"", FIN)
        self.assertTrue(M.write_outcome(st0, f, b"ab", 0, M.SYS, f))
        self.assertFalse(M.write_outcome(st0, f, b"ab", 2, None, f))   # the corner: only on a cut one
        c = M.NetDir(b"", CUT)
        self.assertTrue(M.write_outcome(st0, c, b"ab", 2, None, c))
        self.assertTrue(M.write_outcome(st0, c, b"ab", 0, M.SYS, c))
        # v3.2 (D22): a step that counts none of a non-empty rs is a wait (a stutter), no outcome;
        # an empty rs's one step finishes with 0
        self.assertFalse(M.write_outcome(st0, o, b"ab", 0, None, o))
        self.assertFalse(M.write_outcome(st0, c, b"ab", 0, None, c))
        self.assertTrue(M.write_outcome(st0, o, b"", 0, None, o))
        self.assertTrue(M.write_outcome(st0, c, b"", 0, None, c))
        self.assertFalse(M.write_outcome(st0, c, b"ab", 0, M.CLOSED, c))  # closed: a closed end only
        self.assertFalse(M.write_outcome(st0, f, b"", 0, None, f))  # an empty Write's step, after CloseWrite

    def test_close_and_closewrite(self):
        st0 = M.END_FRESH
        o = M.NetDir(b"x", OPEN)
        self.assertTrue(M.close_outcome(st0, o, None, st0._replace(closed=True), M.NetDir(b"x", FIN)))
        self.assertFalse(M.close_outcome(st0, o, M.SYS, st0, o))
        stC = st0._replace(closed=True)
        self.assertTrue(M.close_outcome(stC, o, M.CLOSED, stC, o))
        self.assertTrue(M.close_write_outcome(st0, M.NetDir(b"", CUT), None, M.NetDir(b"", CUT)))
        self.assertTrue(M.close_write_outcome(st0, o, M.SYS, o))

    def test_addr_ok(self):
        # Impl.lean's / Tests.lean's examples (D20)
        self.assertTrue(M.addr_ok(b"127.0.0.1:7101"))
        self.assertTrue(M.addr_ok(b"10.0.0.2:65535"))
        for a in (b":7101", b"localhost:7101", b"127.0.0.01:7101", b"127.0.0.1:40000", b"127.0.0.1:0",
                  b"0.1.2.3:7101", b"224.0.0.1:7101", b"127.0.0.1:65536", b"127.0.0.1:07101",
                  b"127.0.0.1", b"1.2.3:7101", b"[::1]:7101", b"0.0.0.0:7101"):
            self.assertFalse(M.addr_ok(a), a)

    def test_listen_ok(self):
        # D6, D21: a valid address, or a wildcard with a canonical valid port
        for a in (b"127.0.0.1:7101", b"192.0.2.1:7101", b":7101", b"0.0.0.0:7101", b"[::]:7101"):
            self.assertTrue(M.listen_ok(a), a)
        for a in (b":0", b":40000", b":07101", b"0.0.0.0:40000", b"[::]:", b"localhost:7101",
                  b"[::1]:7101", b"127.0.0.1:0"):
            self.assertFalse(M.listen_ok(a), a)
        self.assertTrue(M.wild_ok(b":7101"))
        self.assertFalse(M.wild_ok(b"127.0.0.1:7101"))

    def test_lis_accepts(self):
        # D7, D21: a listener takes its own address; a wildcard any address with its port
        a1, a2 = b"127.0.0.1:7101", b"127.0.0.2:7101"
        self.assertTrue(M.lis_accepts(a1, a1))
        self.assertFalse(M.lis_accepts(a1, a2))
        for w in (b":7101", b"0.0.0.0:7101", b"[::]:7101"):
            self.assertTrue(M.lis_accepts(w, a1))
            self.assertTrue(M.lis_accepts(w, a2))
            self.assertFalse(M.lis_accepts(w, b"127.0.0.1:7102"))
        self.assertEqual(M.addr_port(a1), b"7101")
        self.assertEqual(M.addr_port(b"[::]:7101"), b"7101")

    def test_listen_step(self):
        # v3.4: any node may listen at any valid address; only sys with one open at it already
        a = b"192.0.2.1:7101"
        L = M.NetLocal({})
        L1 = M.NetLocal({1: (a, True)})
        self.assertTrue(M.local_init(L))
        self.assertTrue(M.net_step("Listen", a, L, M.NetGlobal({}), (1, 0), L1, M.NetGlobal({})))
        self.assertTrue(M.net_step("Listen", a, L, M.NetGlobal({}), M.fail_v(M.SYS), L, M.NetGlobal({})))
        self.assertFalse(M.net_step("Listen", a, L1, M.NetGlobal({}), (2, 0),
                                    M.NetLocal({1: (a, True), 2: (a, True)}), M.NetGlobal({})))
        self.assertTrue(M.net_step("Listen", b":7101", L1, M.NetGlobal({}), (2, 0),
                                   M.NetLocal({1: (a, True), 2: (b":7101", True)}), M.NetGlobal({})))
        self.assertFalse(M.net_step("Listen", b"127.0.0.1:40000", L, M.NetGlobal({}), M.fail_v(M.SYS), L,
                                    M.NetGlobal({})))  # not listenOk: a panic, no outcome
        self.assertTrue(M.crash(L1, L))

    def test_dial_accept_steps(self):
        a = b"127.0.0.1:7101"
        g = M.NetGlobal({})
        g1 = g.set_conn(1, M.conn_fresh(a))
        self.assertTrue(M.dial_step(a, g, (M.end_id(1, False), 0), g1))
        self.assertTrue(M.dial_step(a, g, M.fail_v(M.SYS), g))
        self.assertTrue(M.dial_step(a, g, M.fail_v(M.SYS), g.set_conn(1, M.conn_abandoned(a))))  # D16
        self.assertFalse(M.dial_step(a, g, M.fail_v(M.TIMEOUT), g))
        self.assertFalse(M.dial_step(b"127.0.0.1:40000", g, M.fail_v(M.SYS), g))  # not addrOk
        self.assertFalse(M.dial_step(b":7101", g, M.fail_v(M.SYS), g))  # a wildcard: not addrOk
        g2 = g1.set_conn(1, M.conn_fresh(a)._replace(accepted=True))
        self.assertTrue(M.accept_step(a, True, g1, (M.end_id(1, True), 0), g2))
        self.assertFalse(M.accept_step(a, False, g1, (M.end_id(1, True), 0), g2))
        self.assertFalse(M.accept_step(a, True, g2, (M.end_id(1, True), 0), g2))  # accepted already
        self.assertTrue(M.accept_step(a, False, g1, M.fail_v(M.CLOSED), g1))
        self.assertTrue(M.accept_step(b":7101", True, g1, (M.end_id(1, True), 0), g2))  # D21
        self.assertFalse(M.accept_step(b"127.0.0.2:7101", True, g1, (M.end_id(1, True), 0), g2))
        self.assertFalse(M.accept_step(b":7102", True, g1, (M.end_id(1, True), 0), g2))


# ---------------------------------------------------------------------------------------------
# Lazy against eager, on random histories of one connection

ALPH = b"xy"
PENDING = "pending"  # the result of an operation cut short (no E record)


def eager_results(op):
    kind = op[0]
    if kind == "R":
        n = op[2]
        res = [M.R_BYTES(b""), M.R_EOF, M.R_ERR(M.SYS), M.R_ERR(M.TIMEOUT), M.R_ERR(M.CLOSED)]
        for L in range(1, n + 1):
            for t in itertools.product(ALPH, repeat=L):
                res.append(M.R_BYTES(bytes(t)))
        return res
    if kind == "W":
        L = len(op[2])
        return [(k, r) for k in range(L + 1) for r in (None, M.SYS, M.TIMEOUT, M.CLOSED)]
    return [None, M.SYS, M.TIMEOUT, M.CLOSED]


def _sd(c, i, d):
    return (c[0], c[1], d, c[3]) if i == 0 else (c[0], c[1], c[2], d)


def _se(c, s, e):
    return (e, c[1], c[2], c[3]) if s == 0 else (c[0], e, c[2], c[3])


def eager_wstep(c, s, rs, k, res):
    """Every model state one Write step (progress k, or a failure) allows from c."""
    d = c[2 + s]
    out = set()
    for d2 in {d, M.NetDir(d.bytes + rs[:k], d.status), d._replace(status=CUT)}:
        if M.write_outcome(c[s], d, rs, k, res, d2):
            out.add(_sd(c, s, d2))
    return out


def eager_write_moves(c, s, w, p, r):
    """The steps of a Write call (bytes w, progress p so far, result r or PENDING) from c:
    [(label, the call is done after it, new progress, set of conns)]. Progress 0 into an open
    direction is a wait (no step), into a cut one a step that changes nothing: neither is listed."""
    L = len(w)
    rs = w[p:]
    moves = []
    if r is PENDING:
        for k in range(1, L - p + 1):
            moves.append((("k", k), p + k == L, p + k, eager_wstep(c, s, rs, k, None)))
        for rr in (M.SYS, M.TIMEOUT, M.CLOSED):
            moves.append((("f", rr), True, p, eager_wstep(c, s, rs, 0, rr)))
        if p == L:
            moves.append((("k", 0), True, p, eager_wstep(c, s, rs, 0, None)))
        return moves
    n, res = r
    if res is None:
        if n != L:
            return []
        if p == L:
            moves.append((("k", 0), True, p, eager_wstep(c, s, rs, 0, None)))
        for k in range(1, L - p + 1):
            moves.append((("k", k), p + k == L, p + k, eager_wstep(c, s, rs, k, None)))
    else:
        if not (n < L or n == 0):
            return []
        for k in range(1, n - p + 1):
            moves.append((("k", k), False, p + k, eager_wstep(c, s, rs, k, None)))
        if p == n:
            moves.append((("f", res), True, p, eager_wstep(c, s, rs, 0, res)))
    return moves


def eager_step(c, op, r):
    """Every model state the literal relations allow after op with result r from c: c is
    (dEnd, aEnd, up, down) of model types. A Write here is taken as one call of its loop: its
    progress in one step, then its failure (realize() only)."""
    kind, s = op[0], op[1]
    out = set()
    if kind == "R":
        d = c[2 + (1 - s)]
        cands = {d}
        b = d.bytes
        for i in range(len(b) + 1):
            for j in range(i, len(b) + 1):
                for stt in (OPEN, FIN, CUT):
                    cands.add(M.NetDir(b[i:j], stt))
        for d2 in cands:
            if read_outcome_enum(c[s], d, op[2], r, d2):
                out.add(_sd(c, 1 - s, d2))
    elif kind == "W":
        n, res = r
        w = op[2]
        mid = eager_wstep(c, s, w, n, None) if n > 0 else {c}
        if res is None:
            return mid if n == len(w) else set()
        if not (n < len(w) or n == 0):
            return set()
        for m in mid:
            out |= eager_wstep(m, s, w[n:], 0, res)
    elif kind == "C":
        st, d = c[s], c[2 + s]
        for st2 in (st, st._replace(closed=True)):
            for d2 in (d, M.shut(d)):
                if M.close_outcome(st, d, r, st2, d2):
                    out.add(_sd(_se(c, s, st2), s, d2))
    elif kind == "CW":
        d = c[2 + s]
        for d2 in (d, M.shut(d)):
            if M.close_write_outcome(c[s], d, r, d2):
                out.add(_sd(c, s, d2))
    else:  # deadline
        _, s, dk, set_ = op
        st = c[s]
        for st2 in ENDS:
            if M.deadline_outcome(st, dk, set_, r, st2):
                out.add(_se(c, s, st2))
    return out


def eager_admits(ops, init):
    """ops: list of (op, result or PENDING for unfinished, call, ret or None); a brute-force search
    over every order consistent with real time, every split of every Write into steps, and every
    model successor. A state is (conn, the progress of each Write call)."""
    n = len(ops)
    memo = {}
    p0 = tuple(0 for _ in ops)

    def go(done, states):
        if all(done >> i & 1 for i in range(n) if ops[i][1] is not PENDING and ops[i][3] is not None):
            return True
        key = (done, states)
        if key in memo:
            return memo[key]
        ans = False
        for i in range(n):
            if done >> i & 1:
                continue
            op, r, call, ret = ops[i]
            # i may step next only if no undone operation j must precede it
            if any(not done >> j & 1 and ops[j][3] is not None and ops[j][3] < call
                   for j in range(n) if j != i):
                continue
            nd = done | (1 << i)
            if r is PENDING and go(nd, states):  # unfinished: it stops here (or never began)
                ans = True
                break
            if op[0] == "W":
                branches = {}
                for c, pr in states:
                    # D25: no step while another Write of the end is between its first step
                    # and its last (it holds the end's write lock)
                    if any(j != i and not done >> j & 1 and ops[j][0][0] == "W" and
                           ops[j][0][1] == op[1] and pr[j] > 0 for j in range(n)):
                        continue
                    for label, fin, np_, cs in eager_write_moves(c, op[1], op[2], pr[i], r):
                        pr2 = pr[:i] + (np_,) + pr[i + 1:]
                        b = branches.setdefault((label, fin), set())
                        b |= {(c2, pr2) for c2 in cs}
                for (label, fin), nxt in branches.items():
                    if nxt and go(nd if fin else done, frozenset(nxt)):
                        ans = True
                        break
                if ans:
                    break
                continue
            rs = eager_results(op) if r is PENDING else [r]
            nxt = set()
            for c, pr in states:
                for rr in rs:
                    nxt |= {(c2, pr) for c2 in eager_step(c, op, rr)}
            if nxt and go(nd, frozenset(nxt)):
                ans = True
                break
        memo[key] = ans
        return ans

    return go(0, frozenset([(init, p0)]))


def lazy_admits(ops, init_lazy):
    W = []
    lops = []
    for i, (op, r, call, ret) in enumerate(ops):
        kind, s = op[0], op[1]
        if kind == "R":
            if r is PENDING:
                others = [j for j, o in enumerate(ops) if j != i and o[0][0] == "R" and o[0][1] == s]
                step = (lambda st, dn, s=s, n=op[2], others=others:
                        Z.read_pending(st, s, n, any(not dn(j) for j in others)))
            else:
                step = lambda st, dn, s=s, n=op[2], r=r: Z.read(st, s, n, r, W)
        elif kind == "W":
            w = len(W)
            W.append(op[2])
            if r is PENDING:
                step = (lambda st, dn, s=s, j=i, w=w, L=len(op[2]):
                        Z.write_pending(st, s, j, w, L, dn))
            else:
                step = (lambda st, dn, s=s, j=i, w=w, L=len(op[2]), r=r:
                        Z.write(st, s, j, w, L, r[0], r[1], dn))
        elif kind == "C":
            step = (lambda st, dn, s=s: Z.close_pending(st, s)) if r is PENDING else \
                (lambda st, dn, s=s, r=r: Z.close(st, s, r))
        elif kind == "CW":
            step = (lambda st, dn, s=s: Z.close_write_pending(st, s)) if r is PENDING else \
                (lambda st, dn, s=s, r=r: Z.close_write(st, s, r))
        else:
            _, s, dk, set_ = op
            step = (lambda st, dn, s=s, k=dk, z=set_: Z.deadline_pending(st, s, k, z)) if r is PENDING else \
                (lambda st, dn, s=s, k=dk, z=set_, r=r: Z.deadline(st, s, k, z, r))
        lops.append(lincheck.Op(call, ret, step, f"{op} {r}", optional=r is PENDING))
    return lincheck.search(lops, init_lazy).ok


def random_history(rng):
    n = rng.randint(2, 6)
    ops = []
    for _ in range(n):
        s = rng.randint(0, 1)
        k = rng.random()
        if k < 0.35:
            op = ("R", s, rng.randint(0, 2))
        elif k < 0.7:
            op = ("W", s, bytes(rng.choice(ALPH) for _ in range(rng.randint(0, 2))))
        elif k < 0.8:
            op = ("C", s)
        elif k < 0.9:
            op = ("CW", s)
        else:
            op = ("D", s, rng.randint(0, 2), rng.random() < 0.7)
        ops.append(op)
    return ops


def corner_history(rng):
    """One direction, from the dialer (side 0) to the acceptor: Writes, CloseWrites and the
    reader's Reads, where a Write after CloseWrite needs a cut (README.md's corner)."""
    n = rng.randint(3, 6)
    ops = []
    for _ in range(n):
        k = rng.random()
        if k < 0.4:
            op = ("W", 0, bytes(rng.choice(ALPH) for _ in range(rng.randint(0, 2))))
        elif k < 0.7:
            op = ("R", 1, rng.randint(1, 2))
        elif k < 0.9:
            op = ("CW", 0)
        else:
            op = ("C", rng.randint(0, 1))
        ops.append(op)
    return ops


def realize(rng, ops, init):
    """Results for ops from a random execution of the model in a random order (so that many
    histories are admitted), then perturbed (so that many are not), with random intervals."""
    order = list(range(len(ops)))
    rng.shuffle(order)
    st = init
    res = [None] * len(ops)
    for i in order:
        cands = []
        for r in eager_results(ops[i]):
            nx = eager_step(st, ops[i], r)
            if nx:
                cands.append((r, sorted(nx)))
        if not cands:
            res[i] = rng.choice(eager_results(ops[i]))
            continue
        r, nx = rng.choice(cands)
        res[i] = r
        st = rng.choice(nx)
    if rng.random() < 0.4:
        i = rng.randrange(len(ops))
        res[i] = rng.choice(eager_results(ops[i]))
    # intervals: in the execution's order, overlapping at random
    t = 0
    times = {}
    for i in order:
        t += rng.randint(1, 3)
        times[i] = (t, t + rng.choice([0, 1, 2, 4]))
    out = []
    for i, op in enumerate(ops):
        call, ret = times[i]
        r = res[i]
        if rng.random() < 0.12:
            out.append((op, PENDING, call, rng.choice([None, ret + 2])))
        else:
            out.append((op, r, call, ret))
    return out


class LazyVsEager(unittest.TestCase):
    def test_random_histories(self):
        self.compare(random_history, 7, 1500)

    def test_random_corner_histories(self):
        self.compare(corner_history, 11, 1500)

    def compare(self, gen, seed, N):
        rng = random.Random(seed)
        agree = adm = 0
        for case in range(N):
            ops = gen(rng)
            abandoned = rng.random() < 0.15
            init = (M.END_FRESH._replace(closed=True), M.END_FRESH, M.NetDir(b"", FIN), M.DIR_FRESH) \
                if abandoned else (M.END_FRESH, M.END_FRESH, M.DIR_FRESH, M.DIR_FRESH)
            hist = realize(rng, ops, init)
            e = eager_admits(hist, init)
            lz = lazy_admits(hist, Z.CONN_ABANDONED if abandoned else Z.CONN_FRESH)
            self.assertEqual(e, lz, f"case {case}: eager {e}, lazy {lz}: {hist} (abandoned {abandoned})")
            agree += 1
            adm += e
        # the histories exercise both verdicts
        self.assertGreater(adm, N // 5)
        self.assertLess(adm, N - N // 5)

    def test_corner_closewrite_then_write(self):
        # the precision corner (the survey's A4): after CloseWrite, a Write may succeed only if the
        # direction was cut, here only at the reader's Read before it
        W = (("W", 0, b"x"), (0, None))
        hist = [(("W", 0, b"x"), (1, None), 1, 2), (("R", 1, 2), M.R_BYTES(b"x"), 3, 4),
                (("CW", 0), None, 5, 6), (("W", 0, b"y"), (1, None), 7, 8)]
        init = (M.END_FRESH, M.END_FRESH, M.DIR_FRESH, M.DIR_FRESH)
        self.assertTrue(eager_admits(hist, init))
        self.assertTrue(lazy_admits(hist, Z.CONN_FRESH))
        hist2 = [h for h in hist if h[0][0] != "R"]
        self.assertFalse(eager_admits(hist2, init))
        self.assertFalse(lazy_admits(hist2, Z.CONN_FRESH))
        del W


# ---------------------------------------------------------------------------------------------
# Hand-made traces

class Base(unittest.TestCase):
    def setUp(self):
        self.tr = Trace()

    def check(self):
        return checker.check_run(self.tr.run())

    def admitted(self):
        r = self.check()
        self.assertEqual(r["verdict"], "ADMITTED", checker.report(r, verbose=True))
        self.assertIsNotNone(r["witness"])
        return r

    def rejected(self, proc, seq):
        r = self.check()
        hard = sorted([f for f in r["findings"] if f.kind in checker.HARD], key=lambda f: f.t)
        self.assertEqual(r["verdict"], "NOT ADMITTED", checker.report(r, verbose=True))
        wheres = [f.where for f in hard]
        self.assertIn(f"{proc.node}/{proc.pid}#{seq}", wheres, checker.report(r, verbose=True))
        return r


class Positive(Base):
    def test_echo(self):
        d, a = setup_conn(self.tr)
        d.write(10, 11, "c1", b"hello")
        a.read(12, 13, "c1", 10, b"hello")
        a.write(14, 15, "c1", b"hello")
        d.read(16, 17, "c1", 3, b"hel")
        d.read(18, 19, "c1", 3, b"lo")
        d.close(20, 21, "c1")
        a.read(22, 23, "c1", 10, err=EOF)
        a.read(24, 25, "c1", 10, err=EOF)
        a.close(26, 27, "c1")
        d.read(28, 29, "c1", 10, err=err_closed("Read"))
        r = self.admitted()
        w = r["witness"]
        self.assertEqual([s["op"] for s in w["steps"]][:3], ["Listen", "Dial", "Accept"])
        self.assertEqual(w["version"], 2)
        self.assertNotIn("plan", w)
        self.assertEqual(w["steps"][0]["addr"], "127.0.0.1:7101")
        self.assertNotIn("a0", w["steps"][0])

    def test_concurrent_writes_reordered(self):
        d, a = setup_conn(self.tr)
        d.write(10, 20, "c1", b"AA", g=1)
        d.write(11, 19, "c1", b"BB", g=2)
        a.read(21, 22, "c1", 10, b"BBAA")
        self.admitted()

    def test_read_returns_before_write_returns(self):
        d, a = setup_conn(self.tr)
        d.write(10, 30, "c1", b"xyz")
        a.read(12, 15, "c1", 10, b"xy")
        a.read(16, 17, "c1", 10, b"z")
        self.admitted()

    def test_break_prefix_reset_eof(self):
        d, a = setup_conn(self.tr)
        d.write(10, 11, "c1", b"abcdef")
        d.close(14, 15, "c1")
        a.read(16, 17, "c1", 100, b"abc")
        a.read(18, 19, "c1", 100, err=err_sys("Read", 104))
        a.read(20, 21, "c1", 100, err=EOF)
        r = self.admitted()
        # the reset cuts keeping nothing (v3.5: a sys error needs nothing unread), and the EOF
        # reads the dead direction as it is
        cuts = [s["cut"]["keep"] for s in r["witness"]["steps"] if s.get("cut")]
        self.assertEqual(cuts, [0])

    def test_write_after_peer_close(self):
        d, a = setup_conn(self.tr)
        a.close(10, 11, "c1")
        d.write(12, 13, "c1", b"one")
        d.write(14, 15, "c1", b"two", n=0, err=err_sys("Write", 32))
        d.write(16, 17, "c1", b"three")  # success into a cut direction: discarded
        d.read(18, 19, "c1", 10, err=EOF)
        self.admitted()

    def test_partial_write_timeout(self):
        d, a = setup_conn(self.tr)
        d.deadline(8, 9, "c1", "write")
        d.write(10, 11, "c1", b"0123456789", n=4, err=err_timeout("Write"))
        a.read(12, 13, "c1", 100, b"0123")
        d.close(14, 15, "c1")
        a.read(16, 17, "c1", 100, err=EOF)
        self.admitted()

    def test_read_timeout_with_data_then_cleared(self):
        d, a = setup_conn(self.tr)
        a.deadline(8, 9, "c1", "read")
        d.write(10, 11, "c1", b"late")
        a.read(12, 13, "c1", 100, err=err_timeout("Read"))
        a.deadline(14, 15, "c1", "read", set_=False)
        a.read(16, 17, "c1", 100, b"late")
        self.admitted()

    def test_deadline_set_while_read_blocked(self):
        d, a = setup_conn(self.tr)
        a.read(10, 30, "c1", 100, err=err_timeout("Read"), g=1)
        a.deadline(12, 13, "c1", "read")
        self.admitted()

    def test_accept_any_order_and_dial_before_listen(self):
        c1, s = self.tr.proc("c1"), self.tr.proc("server")
        c2 = self.tr.proc("c2")
        c1.dial(1, 2, A1, "c1", port=40001)  # D7: before any Listen, accepted later
        s.listen(3, 4, A1)
        c2.dial(5, 6, A1, "c1", port=40002)
        s.accept(7, 8, "l1", "c2", A1, "127.0.0.1:40002")
        s.accept(9, 10, "l1", "c3", A1, "127.0.0.1:40001")
        self.admitted()

    def test_write_close_race(self):
        # D15: (k > 0, closed) at an open end; the peer reads exactly the k bytes, then EOF
        d, a = setup_conn(self.tr)
        d.write(10, 30, "c1", b"abcdefgh", n=3, err=err_closed("Write"), g=1)
        d.close(20, 21, "c1", g=2)
        a.read(25, 26, "c1", 100, b"abc")
        a.read(31, 32, "c1", 100, err=EOF)
        self.admitted()

    def test_write_deadline_set_during(self):
        # D15 (the v3 axiom review's refutation): a Write blocked for buffer space, a write
        # deadline set by another goroutine meanwhile, the Write times out having written some
        d, a = setup_conn(self.tr)
        d.write(10, 30, "c1", b"abcdefgh", n=3, err=err_timeout("Write"), g=1)
        a.read(12, 13, "c1", 100, b"ab")
        d.deadline(20, 21, "c1", "write")
        a.read(22, 23, "c1", 100, b"c")
        r = self.admitted()
        parts = [x for x in r["witness"]["steps"] if x["op"] == "Write"]
        self.assertEqual([(x["res"]["k"], x["res"]["code"]) for x in parts], [(3, 0), (0, 2)])
        self.assertEqual(parts[1]["data"], b"defgh".hex())

    def test_overlapping_writes_contiguous(self):
        # two Writes of one end overlapping in time: each one's bytes contiguous, in either order
        # (D25, Go's write lock); their steps never interleave
        for got in (b"AAAABB", b"BBAAAA"):
            with self.subTest(got=got):
                self.tr = Trace()
                d, a = setup_conn(self.tr)
                d.write(10, 30, "c1", b"AAAA", g=1)
                d.write(11, 29, "c1", b"BB", g=2)
                a.read(31, 32, "c1", 10, got)
                self.admitted()

    def test_overlapping_writes_interleaved(self):
        # the same, interleaved: excluded since v3.3 (D25: a Write holds its end's write lock from
        # its first step to its last, as Go's poll.FD.Write holds fdMutex's write lock)
        d, a = setup_conn(self.tr)
        d.write(10, 30, "c1", b"AAAA", g=1)
        d.write(11, 29, "c1", b"BB", g=2)
        a.read(31, 32, "c1", 10, b"AABBAA")
        r = self.check()
        self.assertEqual(r["verdict"], "NOT ADMITTED", checker.report(r, verbose=True))

    def test_dialtimeout_abandoned(self):
        # D16: a DialTimeout fails (either timeout shape), and the listener accepts its connection,
        # which reads EOF
        c, s = self.tr.proc("client"), self.tr.proc("server")
        s.listen(1, 2, A1)
        c.dial(3, 6, A1, op="DialTimeout", err=err_errtimeout())
        c.dial(7, 9, A1, op="DialTimeout", err=err_timeout("DialTimeout"))
        s.accept(4, 8, "l1", "c1", A1, "127.0.0.1:40001")
        s.accept(10, 11, "l1", "c2", A1, "127.0.0.1:40002")
        s.read(12, 13, "c1", 10, err=EOF)
        s.write(14, 15, "c2", b"z")
        s.read(16, 17, "c2", 10, err=err_sys("Read", 104))
        r = self.admitted()
        dials = [x for x in r["witness"]["steps"] if x["op"] == "Dial"]
        self.assertTrue(all("abandoned" in x["res"] for x in dials), dials)

    def test_wildcard_listen(self):
        c, s = self.tr.proc("client"), self.tr.proc("server")
        s.listen(1, 2, ":7101")
        c.dial(3, 6, A1, "c1", port=40001)
        s.accept(4, 7, "l1", "c1", A1, "127.0.0.1:40001")
        s.addrq(8, 9, "ListenerAddr", "l1", {"type": "*net.TCPAddr", "net": "tcp", "s": "[::]:7101"})
        r = self.admitted()
        st = r["witness"]["steps"][0]
        self.assertEqual(st["addr"], ":7101")  # v3.4: the listener is at the wildcard itself

    def test_wildcard_two_addresses(self):
        # v3.4, D21: a wildcard listener takes connections dialed to any address with its port
        c, s = self.tr.proc("client"), self.tr.proc("server")
        s.listen(1, 2, ":7101")
        c.dial(3, 6, A1, "c1", port=40001)
        c.dial(7, 8, "127.0.0.2:7101", "c2", port=40002)
        s.accept(4, 7, "l1", "c1", A1, "127.0.0.1:40001")
        s.accept(8, 9, "l1", "c2", "127.0.0.2:7101", "127.0.0.1:40002")
        self.admitted()

    def test_wildcard_and_address_listeners(self):
        # v3.4: a node may listen at a wildcard and at an address with its port (Linux refuses the
        # second, EADDRINUSE: the model allows both outcomes); a connection no Dial returned, of
        # 127.0.0.2:7101, is accepted by the wildcard
        c, s = self.tr.proc("client"), self.tr.proc("server")
        s.listen(1, 2, A1, "l1")
        s.listen(3, 4, ":7101", "l2")
        c.dial(5, 8, "127.0.0.2:7101", op="DialTimeout", err=err_errtimeout())
        s.accept(6, 9, "l2", "c1", "127.0.0.2:7101", "127.0.0.1:40001")
        r = self.admitted()
        dials = [x for x in r["witness"]["steps"] if x["op"] == "Dial"]
        self.assertTrue(all("abandoned" in x["res"] for x in dials), dials)

    def test_two_nodes_one_address(self):
        # v3.4: no plan: any node may listen at any valid address, two nodes at one address
        c, s, t = self.tr.proc("client"), self.tr.proc("server"), self.tr.proc("other")
        s.listen(1, 2, A1)
        t.listen(1, 2, A1)
        c.dial(3, 6, A1, "c1", port=40001)
        t.accept(4, 7, "l1", "c1", A1, "127.0.0.1:40001")
        self.admitted()

    def test_listen_not_local(self):
        # v3.4, D6: a Listen at an address that is not the machine's fails (EADDRNOTAVAIL): sys
        s = self.tr.proc("server")
        s.listen(1, 2, "192.0.2.1:7101", err=err_sys("Listen", 99, "bind"))
        r = self.admitted()
        self.assertEqual(r["witness"]["steps"][0]["res"], {"code": 3})

    def test_closewrite_halfclose(self):
        d, a = setup_conn(self.tr)
        d.write(10, 11, "c1", b"req")
        d.closewrite(12, 13, "c1")
        a.read(14, 15, "c1", 10, b"req")
        a.read(16, 17, "c1", 10, err=EOF)
        a.write(18, 19, "c1", b"resp")
        a.close(20, 21, "c1")
        d.read(22, 23, "c1", 10, b"resp")
        d.read(24, 25, "c1", 10, err=EOF)
        d.write(26, 27, "c1", b"more", n=0, err=err_sys("Write", 32))
        self.admitted()

    def test_killed_writer(self):
        # a Write that never returned (its process killed) delivered a prefix; then EOF
        c, s = self.tr.proc("writer"), self.tr.proc("server")
        s.listen(1, 2, A1)
        c.dial(3, 6, A1, "c1")
        s.accept(4, 7, "l1", "c1", A1, "127.0.0.1:40000")
        c.write(10, 11, "c1", b"aaaa")
        c.write(12, None, "c1", b"bbbbbbbb", pending=True)
        self.tr.event("start", c, 0)
        self.tr.event("kill", c, 20)
        self.tr.event("exit", c, 21, code=-1, signal="killed", signo=9)
        s.read(13, 14, "c1", 100, b"aaaab")
        s.read(15, 16, "c1", 100, b"bb")
        s.read(30, 31, "c1", 100, err=EOF)
        r = self.admitted()
        pend = [x for x in r["witness"]["steps"] if x.get("pending")]
        self.assertEqual(pend[0]["res"], {"k": 8, "code": 0})

    def test_server_crash_and_restart(self):
        c = self.tr.proc("client")
        s1 = self.tr.proc("server", pid=2001, t0=0)
        s1.listen(1, 2, A1)
        c.dial(3, 6, A1, "c1", port=40001)
        s1.accept(4, 7, "l1", "c1", A1, "127.0.0.1:40001")
        s1.accept(8, None, "l1", "c2", A1, "x", pending=True)
        c.write(9, 10, "c1", b"ping")
        self.tr.event("start", s1, 0)
        self.tr.event("kill", s1, 11)
        self.tr.event("exit", s1, 12, code=-1, signal="killed", signo=9)
        c.read(13, 14, "c1", 10, err=err_sys("Read", 104))
        c.dial(15, 16, A1, err=err_sys("Dial", 111, "connect"))
        s2 = self.tr.proc("server", pid=2002, t0=20)
        self.tr.event("start", s2, 19)
        s2.listen(21, 22, A1)  # the crash dropped the old listener
        c.dial(23, 26, A1, "c2", port=40002)
        s2.accept(24, 27, "l1", "c1", A1, "127.0.0.1:40002")
        r = self.admitted()
        ops = [x["op"] for x in r["witness"]["steps"]]
        self.assertIn("Crash", ops)
        self.assertLess(ops.index("Crash"), len(ops) - 3)

    def test_corner_retro_cut(self):
        # after CloseWrite a Write succeeds: admitted only through a cut, here at the peer's last
        # Read before it (README "Lazy cuts and prefixes", the corner)
        d, a = setup_conn(self.tr)
        d.write(10, 11, "c1", b"x")
        a.read(12, 13, "c1", 10, b"x")
        d.closewrite(14, 15, "c1")
        d.write(16, 17, "c1", b"y")
        r = self.admitted()
        self.assertEqual(r["witness"]["retro_cuts"], 1)
        rd = [x for x in r["witness"]["steps"] if x["op"] == "Read"][0]
        self.assertEqual(rd["cut"], {"keep": 1})

    def test_cut_by_write_then_closewrite_then_write(self):
        d, a = setup_conn(self.tr)
        d.write(10, 11, "c1", b"xx", n=1, err=err_sys("Write", 104))
        d.closewrite(12, 13, "c1")
        d.write(14, 15, "c1", b"y")
        a.read(16, 17, "c1", 10, b"x")
        a.read(18, 19, "c1", 10, err=EOF)
        self.admitted()

    def test_shutdown_pending_at_exit(self):
        d, a = setup_conn(self.tr)
        a.read(10, None, "c1", 10, pending=True, g=2)
        a.close(11, None, "c1", pending=True, g=3)
        self.tr.event("start", a, 0)
        self.tr.event("exit", a, 20, code=0)
        d.read(21, 22, "c1", 10, err=EOF)
        self.admitted()

    def test_reused_four_tuple(self):
        c, s = self.tr.proc("client"), self.tr.proc("server")
        s.listen(1, 2, A1)
        c.dial(3, 6, A1, "c1", port=40001)
        s.accept(4, 7, "l1", "c1", A1, "127.0.0.1:40001")
        c.write(8, 9, "c1", b"one")
        s.read(10, 11, "c1", 10, b"one")
        c.close(12, 13, "c1")
        s.close(14, 15, "c1")
        c.dial(16, 18, A1, "c2", port=40001)
        s.accept(17, 19, "l1", "c2", A1, "127.0.0.1:40001")
        c.write(20, 21, "c2", b"two")
        s.read(22, 23, "c2", 10, b"two")
        self.admitted()


class Negative(Base):
    def test_bytes_invented(self):
        d, a = setup_conn(self.tr)
        d.write(10, 11, "c1", b"abc")
        x = a.read(12, 13, "c1", 10, b"abd")
        self.rejected(a, x)

    def test_bytes_reordered(self):
        d, a = setup_conn(self.tr)
        d.write(10, 11, "c1", b"ab")
        d.write(12, 13, "c1", b"cd")
        x = a.read(14, 15, "c1", 10, b"cdab")
        self.rejected(a, x)

    def test_bytes_read_twice(self):
        d, a = setup_conn(self.tr)
        d.write(10, 11, "c1", b"ab")
        a.read(12, 13, "c1", 10, b"ab")
        x = a.read(14, 15, "c1", 10, b"ab")
        self.rejected(a, x)

    def test_bytes_after_sys_read_error(self):
        # v3.5 (D1, TestStickyReset): no byte follows a sys read error
        d, a = setup_conn(self.tr)
        d.write(10, 11, "c1", b"abcdef")
        a.read(12, 13, "c1", 100, b"abc")
        a.read(14, 15, "c1", 100, err=err_sys("Read", 104))
        x = a.read(16, 17, "c1", 100, b"def")
        self.rejected(a, x)

    def test_read_before_write_called(self):
        d, a = setup_conn(self.tr)
        x = a.read(10, 11, "c1", 10, b"ab")
        d.write(12, 13, "c1", b"ab")
        self.rejected(a, x)

    def test_read_past_what_was_written(self):
        d, a = setup_conn(self.tr)
        d.write(10, 11, "c1", b"ab")
        x = a.read(12, 13, "c1", 10, b"abc")
        self.rejected(a, x)

    def test_short_successful_write(self):
        d, a = setup_conn(self.tr)
        x = d.write(10, 11, "c1", b"abcd", n=3)
        self.rejected(d, x)

    def test_read_closed_on_open_end(self):
        # ErrClosed on an end no Close of it precedes (a racing Close that began after it returned)
        d, a = setup_conn(self.tr)
        x = a.read(10, 11, "c1", 10, err=err_closed("Read"))
        a.close(12, 13, "c1")
        self.rejected(a, x)

    def test_read_timeout_no_deadline(self):
        d, a = setup_conn(self.tr)
        x = a.read(10, 11, "c1", 10, err=err_timeout("Read"))
        self.rejected(a, x)

    def test_write_timeout_no_deadline(self):
        d, a = setup_conn(self.tr)
        x = d.write(10, 11, "c1", b"abc", n=1, err=err_timeout("Write"))
        self.rejected(d, x)

    def test_timeout_after_deadline_cleared(self):
        d, a = setup_conn(self.tr)
        a.deadline(8, 9, "c1", "read")
        a.deadline(10, 11, "c1", "both", set_=False)
        x = a.read(12, 13, "c1", 10, err=err_timeout("Read"))
        self.rejected(a, x)

    def test_data_after_own_close(self):
        d, a = setup_conn(self.tr)
        d.write(10, 11, "c1", b"ab")
        a.close(12, 13, "c1")
        x = a.read(14, 15, "c1", 10, b"ab")
        self.rejected(a, x)

    def test_write_closed_with_no_close(self):
        # a Write fails `closed` with no Close of its end before its end (v3's D15 admitted this;
        # with Write a loop of steps, `closed` needs the end closed at the failing step)
        d, a = setup_conn(self.tr)
        x = d.write(10, 11, "c1", b"abc", n=1, err=err_closed("Write"))
        a.read(12, 13, "c1", 10, b"a")
        d.close(14, 15, "c1")
        self.rejected(d, x)

    def test_write_timeout_deadline_after(self):
        # the deadline is set only after the Write returned
        d, a = setup_conn(self.tr)
        x = d.write(10, 11, "c1", b"abc", n=1, err=err_timeout("Write"))
        d.deadline(12, 13, "c1", "write")
        self.rejected(d, x)

    def test_write_after_own_close(self):
        d, a = setup_conn(self.tr)
        d.close(10, 11, "c1")
        x = d.write(12, 13, "c1", b"ab")
        self.rejected(d, x)

    def test_data_written_after_break_read(self):
        d, a = setup_conn(self.tr)
        d.write(10, 11, "c1", b"ab", n=1, err=err_sys("Write", 104))
        d.write(12, 13, "c1", b"cd")
        x = a.read(14, 15, "c1", 10, b"acd")
        self.rejected(a, x)

    def test_close_returns_sys(self):
        d, a = setup_conn(self.tr)
        x = d.close(10, 11, "c1", err=err_sys("Close", 9))
        self.rejected(d, x)

    def test_second_close_succeeds(self):
        d, a = setup_conn(self.tr)
        d.close(10, 11, "c1")
        x = d.close(12, 13, "c1")
        self.rejected(d, x)

    def test_setdeadline_closed_end_succeeds(self):
        d, a = setup_conn(self.tr)
        d.close(10, 11, "c1")
        x = d.deadline(12, 13, "c1")
        self.rejected(d, x)

    def test_corner_closewrite_write_no_cut_point(self):
        # the corner, rejected: no Read of the direction could have cut it
        d, a = setup_conn(self.tr)
        d.closewrite(10, 11, "c1")
        x = d.write(12, 13, "c1", b"y")
        self.rejected(d, x)

    def test_corner_closewrite_write_closed_no_cut_point(self):
        d, a = setup_conn(self.tr)
        d.closewrite(10, 11, "c1")
        x = d.write(12, 13, "c1", b"yy", n=1, err=err_closed("Write"))
        self.rejected(d, x)

    def test_corner_data_after_closewrite_read(self):
        # the corner's Write is admitted through a cut, so its bytes are discarded: read, rejected
        d, a = setup_conn(self.tr)
        d.write(10, 11, "c1", b"x")
        a.read(12, 13, "c1", 10, b"x")
        d.closewrite(14, 15, "c1")
        d.write(16, 17, "c1", b"y")
        x = a.read(18, 19, "c1", 10, b"y")
        self.rejected(a, x)

    def test_accept_after_crash(self):
        # the listener's process has ended (driver: kill, exit); an Accept on it after that, while
        # its node's next process runs
        c = self.tr.proc("client")
        s1 = self.tr.proc("server", pid=2001, t0=0)
        s1.listen(1, 2, A1)
        self.tr.event("start", s1, 0)
        self.tr.event("kill", s1, 10)
        self.tr.event("exit", s1, 11, code=-1, signal="killed", signo=9)
        s2 = self.tr.proc("server", pid=2002, t0=20)
        self.tr.event("start", s2, 19)
        s2.listen(21, 22, A1)
        c.dial(23, 24, A1, "c1", port=40001)
        x = s1.accept(25, 26, "l1", "c1", A1, "127.0.0.1:40001")
        r = self.rejected(s1, x)
        self.assertIn("not-admitted", {f.kind for f in r["findings"]})

    def test_two_open_listeners(self):
        s = self.tr.proc("server")
        s.listen(1, 2, A1, "l1")
        x = s.listen(3, 4, A1, "l2")
        self.rejected(s, x)

    def test_accept_closed_listener_sys(self):
        c, s = self.tr.proc("client"), self.tr.proc("server")
        s.listen(1, 2, A1)
        s.lclose(3, 4, "l1")
        x = s.accept(5, 6, "l1", None, None, None, err=err_sys("Accept", 103, "accept4"))
        self.rejected(s, x)

    def test_accept_other_address(self):
        # D7: a listener at 127.0.0.1:7101 does not take a connection dialed to 127.0.0.2:7101
        c, s = self.tr.proc("client"), self.tr.proc("server")
        s.listen(1, 2, A1)
        c.dial(3, 6, "127.0.0.2:7101", "c1", port=40001)
        x = s.accept(4, 7, "l1", "c1", "127.0.0.2:7101", "127.0.0.1:40001")
        self.rejected(s, x)

    def test_accept_token_other_address(self):
        # the connection no Dial returned is of 127.0.0.2:7101: the listener at A1 cannot take it
        c, s = self.tr.proc("client"), self.tr.proc("server")
        s.listen(1, 2, A1)
        c.dial(3, 6, "127.0.0.2:7101", op="DialTimeout", err=err_errtimeout())
        x = s.accept(4, 7, "l1", "c1", "127.0.0.2:7101", "127.0.0.1:40001")
        self.rejected(s, x)

    def test_wildcard_other_port(self):
        c, s = self.tr.proc("client"), self.tr.proc("server")
        s.listen(1, 2, ":7102")
        c.dial(3, 6, A1, "c1", port=40001)
        x = s.accept(4, 7, "l1", "c1", A1, "127.0.0.1:40001")
        self.rejected(s, x)

    def test_accept_no_dial(self):
        c, s = self.tr.proc("client"), self.tr.proc("server")
        s.listen(1, 2, A1)
        x = s.accept(3, 4, "l1", "c1", A1, "127.0.0.1:40001")
        self.rejected(s, x)

    def test_accept_failed_dial_after(self):
        # the failed Dial began after the Accept returned
        c, s = self.tr.proc("client"), self.tr.proc("server")
        s.listen(1, 2, A1)
        x = s.accept(3, 4, "l1", "c1", A1, "127.0.0.1:40001")
        c.dial(5, 6, A1, op="DialTimeout", err=err_errtimeout())
        self.rejected(s, x)

    def test_data_from_abandoned(self):
        c, s = self.tr.proc("client"), self.tr.proc("server")
        s.listen(1, 2, A1)
        c.dial(3, 6, A1, op="DialTimeout", err=err_errtimeout())
        s.accept(4, 7, "l1", "c1", A1, "127.0.0.1:40001")
        x = s.read(8, 9, "c1", 10, b"z")
        self.rejected(s, x)

    def test_two_accepts_one_failed_dial(self):
        c, s = self.tr.proc("client"), self.tr.proc("server")
        s.listen(1, 2, A1)
        c.dial(3, 6, A1, op="DialTimeout", err=err_errtimeout())
        s.accept(4, 7, "l1", "c1", A1, "127.0.0.1:40001")
        x = s.accept(8, 9, "l1", "c2", A1, "127.0.0.1:40002")
        self.rejected(s, x)

    def test_plain_dial_timeout(self):
        # Dial (not DialTimeout) failing with a deadline error: net.lean's Dial.impl gives it only
        # for the extension's `timeout`, which DialStep never returns
        c = self.tr.proc("client")
        x = c.dial(3, 6, A1, err=err_timeout("Dial"))
        self.rejected(c, x)

    def test_shape_closed_with_timeout(self):
        d, a = setup_conn(self.tr)
        d.close(10, 11, "c1")
        e = err_closed("Read")
        e["timeout"] = True
        x = d.read(12, 13, "c1", 10, err=e)
        self.rejected(d, x)

    def test_shape_eof_wrapped(self):
        d, a = setup_conn(self.tr)
        d.close(10, 11, "c1")
        e = err_sys("Read")
        e["isEOF"] = True
        x = a.read(12, 13, "c1", 10, err=e)
        self.rejected(a, x)

    def test_shape_eof_from_write(self):
        d, a = setup_conn(self.tr)
        x = d.write(10, 11, "c1", b"ab", n=0, err=EOF)
        self.rejected(d, x)

    def test_shape_bare_errno(self):
        d, a = setup_conn(self.tr)
        x = d.write(10, 11, "c1", b"ab", n=0, err={"type": "syscall.Errno", "msg": "x", "errno": 22})
        self.rejected(d, x)

    def test_shape_wrong_op(self):
        d, a = setup_conn(self.tr)
        d.close(10, 11, "c1")
        e = err_closed("Read")
        e["op"] = "write"
        x = d.read(12, 13, "c1", 10, err=e)
        self.rejected(d, x)

    def test_shape_wrong_syscall(self):
        d, a = setup_conn(self.tr)
        x = d.closewrite(10, 11, "c1", err=err_sys("CloseWrite", 107, "write"))
        self.rejected(d, x)

    def test_shape_data_and_error(self):
        d, a = setup_conn(self.tr)
        d.write(10, 11, "c1", b"ab")
        x = a.read(12, 13, "c1", 10, b"ab", err=err_sys("Read"))
        self.rejected(a, x)

    def test_empty_success_read(self):
        d, a = setup_conn(self.tr)
        x = a.read(12, 13, "c1", 10, b"")
        self.rejected(a, x)

    def test_nil_local_addr(self):
        d, a = setup_conn(self.tr)
        x = d.addrq(10, 11, "LocalAddr", "c1", None)
        self.rejected(d, x)

    def test_clock_two_time_namespaces(self):
        d, a = setup_conn(self.tr)
        a.recs[0]["timens"] = "time:[2]"
        r = self.check()
        self.assertEqual(r["verdict"], "NOT ADMITTED")
        self.assertIn("clock", {f.kind for f in r["findings"]})


class Scope(Base):
    def out(self):
        r = self.check()
        self.assertEqual(r["verdict"], "OUT OF SCOPE", checker.report(r, verbose=True))
        return r

    def test_unmodeled(self):
        d, a = setup_conn(self.tr)
        d.unmodeled(8, 9, "TCPConn.SetNoDelay", "c1")
        d.write(10, 11, "c1", b"x")
        a.read(12, 13, "c1", 10, b"x")
        self.out()

    def test_listen_invalid(self):
        # an ephemeral port: not listenOk, the model's Listen panics
        c, s = self.tr.proc("client"), self.tr.proc("server")
        s.listen(1, 2, "127.0.0.1:40000")
        c.dial(3, 6, "127.0.0.1:40000", "c1", port=40001, remote="127.0.0.1:40000")
        s.accept(4, 7, "l1", "c1", "127.0.0.1:40000", "127.0.0.1:40001")
        r = self.out()
        self.assertTrue(any("listenOk" in f.what for f in r["findings"]))
        self.assertTrue(any("addrOk" in f.what for f in r["findings"]))

    def port0(self, port):
        c, s = self.tr.proc("client"), self.tr.proc("server")
        s.op("Listen", 1, 2, b={"net": "tcp", "addr": "127.0.0.1:0"},
             e={"new": {"id": "l1", "net": "tcp", "local": {"type": "*net.TCPAddr", "net": "tcp",
                                                              "s": f"127.0.0.1:{port}"}, "remote": None}, "err": None})
        c.dial(3, 6, f"127.0.0.1:{port}", "c1", port=40001)
        s.accept(4, 7, "l1", "c1", f"127.0.0.1:{port}", "127.0.0.1:40001")
        return self.out()

    def test_port0(self):
        # the kernel's port is valid: checked as a Listen of it
        r = self.port0(7200)
        self.assertIsNotNone(r["witness"])  # every component admitted, the Listen at the kernel's port
        self.assertEqual(r["witness"]["steps"][0]["addr"], "127.0.0.1:7200")

    def test_port0_ephemeral(self):
        # the kernel's port is ephemeral (as it is by default): not listenOk, nor its Dial addrOk
        r = self.port0(45000)
        self.assertTrue(any("listenOk" in f.what for f in r["findings"]))

    def test_hostname(self):
        c, s = self.tr.proc("client"), self.tr.proc("server")
        s.listen(1, 2, A1)
        c.dial(3, 6, "localhost:7101", "c1", port=40001, remote=A1)
        s.accept(4, 7, "l1", "c1", A1, "127.0.0.1:40001")
        c.write(8, 9, "c1", b"x")
        self.out()

    def test_inconclusive_when_tainted(self):
        # a listener deadline (unmodeled) and an Accept timeout: inconclusive, not a finding
        s = self.tr.proc("server")
        s.listen(1, 2, A1)
        s.unmodeled(3, 4, "TCPListener.SetDeadline", "l1")
        s.accept(5, 6, "l1", None, None, None, err=err_timeout("Accept"))
        r = self.out()
        self.assertIn("inconclusive", {f.kind for f in r["findings"]})


# ---------------------------------------------------------------------------------------------
# Real traces

class Sample(unittest.TestCase):
    def test_sample_admitted(self):
        files = sorted(glob.glob(os.path.join(TESTDATA, "*.tar.gz")))
        self.assertTrue(files)
        n = 0
        for f in files:
            for run in T.load_targz(f):
                r = checker.check_run(run)
                self.assertEqual(r["verdict"], "ADMITTED", checker.report(r, verbose=True))
                self.assertIsNotNone(r["witness"])
                n += 1
        self.assertEqual(n, 15)

    def test_sample_mutants_rejected(self):
        files = sorted(glob.glob(os.path.join(TESTDATA, "*.tar.gz")))
        tot = rej = 0
        missed = []
        for f in files:
            for run in T.load_targz(f):
                res, miss = mutate.run(run, n=3, seed=1)
                for kind, (t, r) in res.items():
                    tot += t
                    rej += r
                missed += miss
        self.assertGreater(tot, 100)
        self.assertEqual(missed, [])


if __name__ == "__main__":
    unittest.main()
