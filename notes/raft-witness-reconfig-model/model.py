# Explicit-state model of etcd-raft membership changes with a witness, as raft#168 does it in
# the fork raft-witness-goose-lean (9ed005d46). An extension of issues/raft-conf-lag-model/
# model.py (same abstraction: atomic elections, one AppendEntries round trip per `app`,
# apply-time configuration switching) with:
#   - entries (term, subterm, kind, data); the leader's epoch (subterm, excluded per half);
#   - a configuration (incoming, outgoing, witness in incoming, witness in outgoing), changed
#     by confchange's rules (AddWitness, remove of the witness, EnterJoint copying
#     Witnesses[0] to [1], LeaveJoint clearing [1]);
#   - the witness W's storage, updated atomically (the CAS), and each node's witness proxy
#     cache (the storage state at that node's last access);
#   - the witness's vote rule (handleVote: responders within the stored incoming
#     replication set), the candidate's readiness (getWitnessVoteRequestReadiness, per half),
#     maybeCommit's quorum-1 index per replicating half (min over halves of one witness),
#     the witness's append (handleAppend / handleAppendNoUpdate, from the storage or the
#     cache), ChangeReplicationSet (any member excluded, a superset of the code's choices),
#     ResetReplicationSet on a leader's switchToConfig when a witness is involved.
# Checked: state machine safety (committed prefixes agree), leader completeness at each
# win, election safety (one winner per term).
#
# usage: model.py NREG INIT MODE MAXT MAXLOG MAXCONF MAXVAL [flags]
#   NREG regular nodes 1..NREG, INIT the initial regular voters 1..INIT; the witness is
#   W = NREG + 1. MODE faithful (configuration moves with apply; raft's
#   hasUnappliedConfChanges guard on campaign) or crash (a node may restart with its commit
#   lost: commit = applied = 0, the configuration of the empty prefix).
#   flags: joint (joint changes), w0 (the witness in the initial configuration), wops (the
#   witness may be added/removed), noreplay (no witness), lag-cand (a candidate may campaign
#   with committed conf entries it has not applied: drops raft's guard, to test what it buys),
#   rsout (the witness checks responders against the outgoing set too: a candidate fix).
import sys, itertools, os
from collections import deque

NREG = int(sys.argv[1]); INIT = frozenset(range(1, int(sys.argv[2]) + 1))
MODE = sys.argv[3]
MAXT, MAXLOG, MAXCONF, MAXVAL = map(int, sys.argv[4:8])
FLAGS = set(sys.argv[8:])
JOINT = 'joint' in FLAGS
W = NREG + 1
W0 = 'w0' in FLAGS
WOPS = 'wops' in FLAGS
LAGCAND = 'lag-cand' in FLAGS
ENTER2 = 'enter2' in FLAGS  # joint changes of two adds (a ConfChangeV2 with two Changes)
REG = range(1, NREG + 1)
ALL = list(REG) + [W]
REDUCED = bool(os.environ.get('REDUCED'))

# a configuration: (inc, out, w0, w1); inc/out frozensets of members (the witness included)
C0 = (INIT | ({W} if W0 else frozenset()), frozenset(), W if W0 else 0, 0)

def apply_op(c, op):
    inc, out, w0, w1 = c
    k = op[0]
    if k == 'add': inc = inc | {op[1]}
    elif k == 'rem':
        inc = inc - {op[1]}
        if op[1] == w0: w0 = 0
    elif k == 'addw': inc = inc | {W}; w0 = W
    elif k == 'enter':  # copy incoming to outgoing (with its witness), then the change
        out, w1 = inc, w0
        inc, out_, w0, w1_ = apply_op((inc, frozenset(), w0, 0), op[1])
    elif k == 'enter2':  # a joint change of two simple changes (ConfChangeV2 with two Changes)
        out, w1 = inc, w0
        inc, _, w0, _ = apply_op(apply_op((inc, frozenset(), w0, 0), op[1]), op[2])
    elif k == 'leave': out, w1 = frozenset(), 0
    return (inc, out, w0, w1)

def cfg_at(log, k):
    c = C0
    for e in log[:k]:
        if e[2] == 'c': c = apply_op(c, e[3])
    return c

def maj(S, C): return len(S & C) * 2 > len(C)
def isq(c, S):
    inc, out, _, _ = c
    return bool(inc) and maj(S, inc) and (not out or maj(S, out))
def members(c): return c[0] | c[1]
def has_w(c): return c[2] != 0 or c[3] != 0
def last(log): return (log[-1][0], log[-1][1]) if log else (0, 0)
def uptodate(a, b):  # a at least as up to date as b (raft: term, index)
    ta = a[-1][0] if a else 0; tb = b[-1][0] if b else 0
    return (ta, len(a)) >= (tb, len(b))

def rs_nonw(c, ep, h):
    """The non-witness members of half h's replication set (NonWitnessVoters)."""
    V = c[h]; w = c[2 + h]; ex = ep[1 + h]
    return frozenset(V - {w, ex})
def w_in_rs(c, ep, h):
    w = c[2 + h]
    return w != 0 and ep[1 + h] != w

def votes_to_win(V, half):
    if not half: return 0
    q = len(half) // 2 + 1
    g = len(V & half)
    if g >= q: return 0
    return q - g  # pending (every other voter has not responded yet)

def readiness(c, V):
    """getWitnessVoteRequestReadiness: the witnesses to ask."""
    v1 = votes_to_win(V, c[0]); v2 = votes_to_win(V, c[1])
    if v1 > 1 and v2 > 1: return set()
    w1, w2 = c[2], c[3]
    if w1 == 0 and w2 == 0: return set()
    out = set()
    if w1 == w2:
        if (v1 == 1 and v2 <= 1) or (v1 <= 1 and v2 == 1): out.add(w1)
    else:
        if w1 and v1 == 1: out.add(w1)
        if w2 and v2 == 1: out.add(w2)
    return out

def olq(c, ep, match, h, me):
    """MajorityConfig.OneLessThanQuorum of half h over the replication set's non-witness
    members' Match (the scoped indexer: others count 0)."""
    V = c[h]; n = len(V)
    if n == 0: return None
    if n == 1: return 0
    rs = rs_nonw(c, ep, h)
    vals = sorted([match[ALL.index(v)] if v in rs else 0 for v in V])
    return vals[n - n // 2]

def committed_index(c, match):
    def half(V):
        if not V: return 10 ** 9
        vals = sorted([match[ALL.index(v)] for v in V])
        return vals[len(V) - (len(V) // 2 + 1)]
    return min(half(c[0]), half(c[1]))

# node: (term, role, log, commit, applied, match, pending, epoch)
#   epoch: (sub, ex0, ex1) (a leader's); match over ALL
# witness storage: (term, vote, lead, lt, ls, li, rsin, rsout)
WS0 = (0, 0, 0, 0, 0, 0, frozenset(), frozenset())
# state: (nodes, wst, caches, nc, nv, won)  won: frozenset of terms won (election safety)

def succ(st):
    nodes, wst, caches, nc, nv, won = st
    out = []
    def mk(ch=None, wst2=None, cch=None, nc2=None, nv2=None, won2=None):
        ns = list(nodes)
        for i, v in (ch or {}).items(): ns[i - 1] = v
        cs = list(caches)
        for i, v in (cch or {}).items(): cs[i - 1] = v
        return (tuple(ns), wst if wst2 is None else wst2, tuple(cs),
                nc if nc2 is None else nc2, nv if nv2 is None else nv2,
                won if won2 is None else won2)
    for i in REG:
        term, role, log, commit, applied, match, pending, ep = nodes[i - 1]
        c = cfg_at(log, applied)
        # ---- election (atomic) ----
        if role != 'L' and i in members(c) and (LAGCAND or not any(e[2] == 'c' for e in log[applied:commit])):
            others = [j for j in REG if j != i and uptodate(log, nodes[j - 1][2])]
            for r in range(len(others) + 1):
                for Vt in itertools.combinations(others, r):
                    V = frozenset(Vt) | {i}
                    Tmin = max(nodes[j - 1][0] for j in V) + 1
                    wins = []
                    if isq(c, V):
                        wins.append((Tmin, V, None))
                    else:
                        # the witness, asked with the responders V' (the grants so far), V' ⊆ V
                        for wi in readiness(c, V):
                            if not isq(c, V | {wi}): continue
                            for r2 in range(1, len(V) + 1):
                                for Vp in itertools.combinations(sorted(V), r2):
                                    Vp = frozenset(Vp)
                                    if i not in Vp or wi not in readiness(c, Vp): continue
                                    for T in sorted({Tmin, wst[0] + 1}):
                                        if T < Tmin: continue
                                        wins.append((T, V, ('w', Vp)))
                    for (T, V, how) in wins:
                        if T > MAXT or len(log) + 1 > MAXLOG: continue
                        wst2 = wst; cch = {}
                        if how is not None:
                            Vp = how[1]
                            wt, wv, wl, lt, ls, li, rsin, rsout = wst
                            if T < wt: continue  # older term: no answer
                            if T > wt: wt, wv, wl = T, 0, 0
                            if not (wv == i or (wv == 0 and wl == 0)): continue
                            cl = last(log)
                            if cl < (lt, ls): continue
                            if cl == (lt, ls):
                                if 'norscheck' not in FLAGS and not Vp <= rsin: continue
                                if 'rsout' in FLAGS and rsout and not (Vp & c[1]) <= rsout: continue
                            wst2 = (wt, i, wl, lt, ls, li, rsin, rsout)
                            cch = {i: wst2}
                        ch = {}
                        for j in V:
                            if j == i: continue
                            n = nodes[j - 1]
                            ch[j] = (T, 'F', n[2], n[3], n[4], (), 0, ())
                        ep2 = (0, c[2], c[3])  # ResetReplicationSet(true): the witness excluded
                        nl = log + ((T, 0, 'e', None),)
                        m = tuple(len(nl) if v == i else 0 for v in ALL)
                        ch[i] = (T, 'L', nl, commit, applied, m, len(log), ep2)
                        ns_ = mk(ch, wst2, cch, won2=won | {T})
                        bad = None
                        if T in won: bad = 'election safety'
                        for k in REG:
                            lk, ck = nodes[k - 1][2], nodes[k - 1][3]
                            if nl[:ck] != lk[:ck]: bad = 'leader completeness'
                        out.append((('elect', i, tuple(sorted(V)), T, how and tuple(sorted(how[1]))), ns_, bad))
        # ---- a leader's actions ----
        if role == 'L':
            def lead(nl, pend=pending, ep2=ep, m=None):
                mm = m if m is not None else match
                mm = tuple(len(nl) if v == i else mm[ALL.index(v)] for v in ALL)
                return (term, role, nl, commit, applied, mm, pend, ep2)
            if nv < MAXVAL and len(log) < MAXLOG:
                out.append((('propv', i, nv + 1), mk({i: lead(log + ((term, ep[0], 'v', nv + 1),))}, nv2=nv + 1), None))
            if nc < MAXCONF and len(log) < MAXLOG and not (pending > applied):
                inc, outc, w0, w1 = c
                ops = []
                if not outc:
                    simple = [('add', j) for j in REG if j not in inc]
                    simple += [('rem', j) for j in inc if j != i and j != W and len(inc) > 1]
                    if WOPS:
                        if w0 == 0 and W not in inc: simple.append(('addw',))
                        if w0 == W and len(inc) > 1: simple.append(('rem', W))
                    ops += simple
                    if JOINT:
                        ops += [('enter', o) for o in simple]
                        if ENTER2:
                            ops += [('enter2', o1, o2) for o1 in simple for o2 in simple
                                    if o1 < o2 and o1[0] == o2[0] == 'add']
                for op in ops:
                    nl = log + ((term, ep[0], 'c', op),)
                    out.append((('propc', i, op), mk({i: lead(nl, len(nl))}, nc2=nc + 1), None))
            # ChangeReplicationSet: a new subterm, any member excluded per witnessed half
            if has_w(c) and len(log) < MAXLOG:
                choices = []
                for h in (0, 1):
                    if c[2 + h]:
                        choices.append([x for x in c[h] if x != i])
                    else:
                        choices.append([ep[1 + h]])
                for ex0 in choices[0]:
                    for ex1 in choices[1]:
                        if (ex0, ex1) == (ep[1], ep[2]): continue
                        ep2 = (ep[0] + 1, ex0, ex1)
                        nl = log + ((term, ep2[0], 'e', None),)
                        out.append((('rschange', i, ex0, ex1), mk({i: lead(nl, ep2=ep2)}), None))
            # AppendEntries to a regular node
            for j in REG:
                if j == i: continue
                tj, rj, lj, cj, aj, mj, pj, ej = nodes[j - 1]
                if tj > term: continue
                p = 0
                while p < min(len(lj), len(log)) and lj[p] == log[p]: p += 1
                if p < cj: continue
                for q in (range(p, min(p + 1, len(log)) + 1) if REDUCED else range(p, len(log) + 1)):
                    nl = lj if (len(lj) >= q and lj[:q] == log[:q]) else log[:q]
                    ncm = max(cj, min(commit, q))
                    chj = (term, 'F', nl, ncm, aj, (), 0, ())
                    nm = tuple(max(match[k], q) if ALL[k] == j else match[k] for k in range(len(ALL)))
                    chi = (term, role, log, commit, applied, nm, pending, ep)
                    out.append((('app', i, j, q), mk({j: chj, i: chi}), None))
            # maybeCommit's append to the witness
            idx = {}
            for h in (0, 1):
                if w_in_rs(c, ep, h):
                    x = olq(c, ep, match, h, i)
                    if x is not None:
                        w = c[2 + h]
                        idx[w] = x if w not in idx else min(idx[w], x)
            if 'fixa' in FLAGS:
                # the fix: a witness is sent an entry only if every half it is the witness of
                # has it in its replication set
                idx = {w: x for w, x in idx.items()
                       if all(w_in_rs(c, ep, h) for h in (0, 1) if c[2 + h] == w)}
            for w, x in idx.items():
                if x == 0 or x > len(log): continue
                e = log[x - 1]
                if not (e[0] == term and e[1] == ep[0]): continue
                rsin = rs_nonw(c, ep, 0); rsout = rs_nonw(c, ep, 1)
                for via in ('cache', 'store'):
                    s0 = caches[i - 1] if via == 'cache' else wst
                    if s0 is None: continue
                    wt, wv, wl, lt, ls, li, ri, ro = s0
                    ack = None; wst2 = None
                    if term < wt: continue
                    if via == 'cache':
                        if term != wt: continue
                        if (term, ep[0]) == (lt, ls): ack = x
                        elif (term, ep[0]) < (lt, ls): ack = li
                        else: continue
                        cch = {}
                    else:
                        if term > wt: wt, wv, wl = term, 0, i
                        if (term, ep[0]) == (lt, ls): ack = x
                        elif (term, ep[0]) < (lt, ls): ack = li
                        else:
                            lt, ls, li, ri, ro = term, ep[0], x, rsin, rsout
                            ack = x
                        wst2 = (wt, wv, wl, lt, ls, li, ri, ro)
                        cch = {i: wst2}
                    k = ALL.index(w)
                    nm = tuple(max(match[kk], ack) if kk == k else match[kk] for kk in range(len(ALL)))
                    chi = (term, role, log, commit, applied, nm, pending, ep)
                    out.append((('wapp', i, x, via), mk({i: chi}, wst2, cch), None))
            # commit
            N = committed_index(c, match)
            if N > commit and N <= len(log) and log[N - 1][0] == term:
                out.append((('commit', i, N), mk({i: (term, role, log, N, applied, match, pending, ep)}), None))
        # ---- apply ----
        if applied < commit:
            na = applied + 1
            n2 = (term, role, log, commit, na, match, pending, ep)
            c2 = cfg_at(log, na)
            if role == 'L' and log[na - 1][2] == 'c':
                t, ro, lg, cm, a, m, pe, e_ = n2
                if i not in members(c2):  # stepDownOnRemoval
                    n2 = (t, 'F', lg, cm, a, (), 0, ())
                else:
                    if has_w(c) or has_w(c2) or e_[1] or e_[2]:  # maybeStartNewSubterm(false, true)
                        if len(lg) >= MAXLOG: n2 = None
                        else:
                            e2 = (e_[0] + 1, c2[2], c2[3])
                            lg = lg + ((t, e2[0], 'e', None),)
                            m = tuple(len(lg) if v == i else m[ALL.index(v)] for v in ALL)
                            n2 = (t, ro, lg, cm, a, m, pe, e2)
                    if n2 is not None and JOINT and c2[1] and n2[4] >= n2[6]:  # auto-leave
                        t, ro, lg, cm, a, m, pe, e_ = n2
                        if len(lg) >= MAXLOG: n2 = None
                        else:
                            lg = lg + ((t, e_[0], 'c', ('leave',)),)
                            m = tuple(len(lg) if v == i else m[ALL.index(v)] for v in ALL)
                            n2 = (t, ro, lg, cm, a, m, len(lg), e_)
            if n2 is not None:
                out.append((('apply', i, na), mk({i: n2}), None))
        if MODE == 'crash' and commit > 0:
            out.append((('crash', i), mk({i: (term, 'F', log, 0, 0, (), 0, ())}), None))
    return out

def sms(st):
    nodes = st[0]
    for a in nodes:
        for b in nodes:
            k = min(a[3], b[3])
            if a[2][:k] != b[2][:k]: return False
    return True

def init():
    n0 = (0, 'F', (), 0, 0, (), 0, ())
    return (tuple(n0 for _ in REG), WS0, tuple(None for _ in REG), 0, 0, frozenset())

def bfs():
    s0 = init()
    parent = {s0: None}
    dq = deque([(s0, 0)]); cnt = 0; maxd = 0
    while dq:
        s, d = dq.popleft(); cnt += 1
        if d > maxd:
            print('finished depth', maxd, 'states', cnt - 1, 'seen', len(parent), flush=True); maxd = d
        for a, ns, bad in succ(s):
            if bad is None and not sms(ns): bad = 'state machine safety'
            if ns in parent and bad is None: continue
            if ns not in parent: parent[ns] = (s, a)
            if bad is not None:
                print('VIOLATION:', bad, 'at depth', d + 1)
                tr = [a]; x = s
                while parent[x] is not None:
                    px, pa = parent[x]; tr.append(pa); x = px
                for t in reversed(tr): print('  ', t)
                show(ns)
                return 1
            dq.append((ns, d + 1))
    print('no violation; states', cnt, 'max depth', maxd)
    return 0

def show(s):
    nodes, wst, caches, nc, nv, won = s
    for i, n in zip(REG, nodes):
        print('  node', i, 'term', n[0], n[1], 'log', n[2], 'commit', n[3], 'applied', n[4],
              'cfg', cfg_at(n[2], n[4]), 'epoch', n[7])
    print('  witness', wst)

def replay(path):
    s = init()
    for line in open(path):
        line = line.strip()
        if not line or line.startswith('#'): continue
        want = eval(line)
        nx = [(ns, bad) for a, ns, bad in succ(s) if a == want]
        if not nx:
            print('not enabled:', want); show(s)
            print('enabled:', [a for a, _, _ in succ(s) if a[0] == want[0]])
            return 2
        s, bad = nx[0]
        print('ok', want, bad or ('' if sms(s) else 'UNSAFE (sms)'))
    show(s)
    return 0

def walks(n, seed, maxlen=80):
    """Random walks: at each step an action kind uniformly, then an action of it."""
    import random
    random.seed(seed)
    steps = 0
    for w in range(n):
        s = init(); tr = []
        while len(tr) < maxlen:
            nx = succ(s)
            if not nx: break
            byk = {}
            for a, ns, bad in nx: byk.setdefault(a[0], []).append((a, ns, bad))
            a, s, bad = random.choice(byk[random.choice(list(byk))])
            tr.append(a); steps += 1
            if bad is None and not sms(s): bad = 'state machine safety'
            if bad:
                print('VIOLATION:', bad, 'walk', w, 'step', len(tr))
                for t in tr: print('  ', t)
                show(s)
                return 1
    print('walks', n, 'steps', steps, 'no violation')
    return 0

if __name__ == '__main__':
    if os.environ.get('REPLAY'): sys.exit(replay(os.environ['REPLAY']))
    if os.environ.get('WALKS'):
        sys.exit(walks(int(os.environ['WALKS']), int(os.environ.get('SEED', '1')),
                       int(os.environ.get('MAXLEN', '80'))))
    sys.exit(bfs())
