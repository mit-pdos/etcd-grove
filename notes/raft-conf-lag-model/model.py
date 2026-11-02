# Abstract model of etcd-raft membership with apply-time configuration switching.
# Node: (term, role, log, commit, applied, cfgidx, match, pending, pcommit)
#   log: tuple of entries (term, kind, data); kind 'v' value, 'c' conf op, 'e' empty
#   commit/applied: raft's view; cfgidx: prefix through which ApplyConfChange was called
#   faithful: cfgidx == applied. lag: applied may run ahead of cfgidx (Advance before
#   ApplyConfChange). crash: a node may restart with the HardState.Commit persisted
#   before its last append (entries persisted, the commit that came with them lost).
import sys, itertools
from collections import deque

N = int(sys.argv[1]); INIT = frozenset(range(1, int(sys.argv[2]) + 1))
MODE = sys.argv[3]
MAXT, MAXLOG, MAXCONF, MAXVAL = map(int, sys.argv[4:8])
JOINT = len(sys.argv) > 8 and sys.argv[8] == 'joint'
NODES = range(1, N + 1)
import os
REDUCED = bool(os.environ.get("REDUCED"))

def cfg_at(log, k):
    inc, out = INIT, frozenset()
    for e in log[:k]:
        if e[1] == 'c':
            op = e[2]
            if op[0] == 'add': inc = inc | {op[1]}
            elif op[0] == 'rem': inc = inc - {op[1]}
            elif op[0] == 'enter': out, inc = inc, frozenset(op[1])
            elif op[0] == 'leave': out = frozenset()
    return inc, out

def maj(S, C): return len(S & C) * 2 > len(C)

def isq(cfg, S):
    inc, out = cfg
    return bool(inc) and maj(S, inc) and (not out or maj(S, out))

def uptodate(a, b):
    ta = a[-1][0] if a else 0; tb = b[-1][0] if b else 0
    return (ta, len(a)) >= (tb, len(b))

def members(cfg): return cfg[0] | cfg[1]

def succ(st):
    nodes, nc, nv = st
    out = []
    def upd(ch, nc2=nc, nv2=nv):
        ns = list(nodes)
        for i, v in ch.items(): ns[i - 1] = v
        return (tuple(ns), nc2, nv2)
    for i in NODES:
        term, role, log, commit, applied, cfgidx, match, pending, pcommit = nodes[i - 1]
        cfg = cfg_at(log, cfgidx)
        # election (atomic; pre-vote uses the same quorum and up-to-date check)
        if role != 'L' and i in members(cfg):
            if not any(e[1] == 'c' for e in log[applied:commit]):  # hasUnappliedConfChanges
                others = [j for j in NODES if j != i and uptodate(log, nodes[j - 1][2])]
                for r in range(len(others) + 1):
                    for V in itertools.combinations(others, r):
                        S = frozenset(V) | {i}
                        if not isq(cfg, S): continue
                        T = max(nodes[j - 1][0] for j in S) + 1
                        if T > MAXT or len(log) + 1 > MAXLOG: continue
                        ch = {}
                        for j in V:
                            n = nodes[j - 1]
                            ch[j] = (T, 'F') + n[2:6] + ((), 0, n[8])
                        nl = log + ((T, 'e', None),)
                        m = tuple(len(nl) if j == i else 0 for j in NODES)
                        ch[i] = (T, 'L', nl, commit, applied, cfgidx, m, len(log), pcommit)
                        out.append((('elect', i, tuple(sorted(S)), T), upd(ch)))
        if role == 'L':
            def lead(nl, pend, c=commit):
                m = tuple(len(nl) if j == i else match[j - 1] for j in NODES)
                return (term, role, nl, c, applied, cfgidx, m, pend, pcommit)
            if nv < MAXVAL and len(log) < MAXLOG:
                out.append((('propv', i, nv + 1), upd({i: lead(log + ((term, 'v', nv + 1),), pending)}, nc, nv + 1)))
            if nc < MAXCONF and len(log) < MAXLOG and not (pending > applied):
                inc, outc = cfg
                ops = []
                if outc:
                    pass  # only an empty (leave) change is accepted; auto-leave proposes it
                else:
                    ops += [('add', j) for j in NODES if j not in inc]
                    ops += [('rem', j) for j in inc if j != i and len(inc) > 1]
                    if JOINT:
                        for j in NODES:
                            new = inc ^ {j}
                            if j != i and new: ops.append(('enter', tuple(sorted(new))))
                for op in ops:
                    nl = log + ((term, 'c', op),)
                    out.append((('propc', i, op), upd({i: lead(nl, len(nl))}, nc + 1, nv)))
            for j in NODES:
                if j == i: continue
                tj, rj, lj, cj, aj, gj, mj, pj, pcj = nodes[j - 1]
                if tj > term: continue
                p = 0
                while p < min(len(lj), len(log)) and lj[p] == log[p]: p += 1
                if p < cj: continue
                for q in (range(p, min(p + 1, len(log)) + 1) if REDUCED else range(p, len(log) + 1)):
                    nl = lj if (len(lj) >= q and lj[:q] == log[:q]) else log[:q]
                    ncm = max(cj, min(commit, q))
                    pc = cj if nl != lj else pcj
                    chj = (term, 'F', nl, ncm, aj, gj, (), 0, pc)
                    nm = tuple(max(match[k - 1], q) if k == j else match[k - 1] for k in NODES)
                    chi = (term, role, log, commit, applied, cfgidx, nm, pending, pcommit)
                    out.append((('app', i, j, q), upd({j: chj, i: chi})))
            for Nn in range(len(log), commit, -1):
                if log[Nn - 1][0] != term: continue
                S = frozenset(k for k in NODES if k == i or match[k - 1] >= Nn)
                if isq(cfg, S):
                    out.append((('commit', i, Nn), upd({i: (term, role, log, Nn, applied, cfgidx, match, pending, pcommit)})))
                    break
        def after_cfg(n2, ng):
            t, ro, lg, c, a, g, m, pe, pc = n2
            c2 = cfg_at(lg, ng)
            if ro == 'L' and i not in members(c2):  # stepDownOnRemoval
                return (t, 'F', lg, c, a, g, (), 0, pc)
            if JOINT and ro == 'L' and c2[1] and a >= pe and len(lg) < MAXLOG:  # auto-leave
                nl = lg + ((t, 'c', ('leave',)),)
                mm = tuple(len(nl) if j == i else m[j - 1] for j in NODES)
                return (t, ro, nl, c, a, g, mm, len(nl), pc)
            return n2
        if applied < commit:
            na = applied + 1
            ng = na if MODE != 'lag' else cfgidx
            n2 = after_cfg((term, role, log, commit, na, ng, match, pending, pcommit), ng)
            out.append((('apply', i, na), upd({i: n2})))
        if MODE == 'lag' and cfgidx < applied:
            ng = cfgidx + 1
            n2 = after_cfg((term, role, log, commit, applied, ng, match, pending, pcommit), ng)
            out.append((('applyconf', i, ng), upd({i: n2})))
        if MODE == 'crash' and pcommit < commit:
            out.append((('crash', i, pcommit), upd({i: (term, 'F', log, pcommit, 0, 0, (), 0, pcommit)})))
    return out

def safe(st):
    nodes = st[0]
    for a in nodes:
        for b in nodes:
            k = min(a[3], b[3])
            if a[2][:k] != b[2][:k]: return False
    return True

s0 = (tuple((0, 'F', (), 0, 0, 0, (), 0, 0) for _ in NODES), 0, 0)
dq = deque([s0]); cnt = 0
if __name__ == '__main__' and len(sys.argv) > 9:  # replay a scripted trace
    s = s0
    for line in open(sys.argv[9]):
        want = eval(line)
        nxt = [ns for a, ns in succ(s) if a == want]
        if not nxt: print('action not enabled:', want); sys.exit(2)
        s = nxt[0]; print('ok', want, 'safe' if safe(s) else 'UNSAFE')
    for i, n in enumerate(s[0], 1):
        print('  node', i, 'term', n[0], n[1], 'log', n[2], 'commit', n[3], 'applied', n[4],
              'cfgidx', n[5], 'cfg', sorted(cfg_at(n[2], n[5])[0]))
    sys.exit(0)
import os, random
if os.environ.get('WALKS'):
    random.seed(int(os.environ.get('SEED', '1')))
    walks = int(os.environ['WALKS']); viol = 0; steps = 0; first = None
    for w in range(walks):
        st = s0; tr = []
        while True:
            nx = succ(st)
            if not nx or len(tr) >= 60: break
            byt = {}
            for a_, s_ in nx: byt.setdefault(a_[0], []).append((a_, s_))
            a, st = random.choice(byt[random.choice(list(byt))]); tr.append(a); steps += 1
            if not safe(st):
                viol += 1
                if first is None: first = list(tr)
                break
    print('walks', walks, 'steps', steps, 'violations', viol)
    if first:
        for a in first: print('  ', a)
    sys.exit(0)
depth = {s0: 0}; maxd = 0
while dq:
    s = dq.popleft(); cnt += 1
    d = depth[s]
    if d > maxd:
        print('finished all states at depth', maxd, 'states so far', cnt - 1, flush=True); maxd = d
    if not safe(s):
        print('VIOLATION after', cnt, 'states, depth', d)
        sys.exit(1)
    for a, ns in succ(s):
        if ns not in depth:
            depth[ns] = d + 1; dq.append(ns)
print('no violation; states explored:', cnt, 'max depth', maxd)
