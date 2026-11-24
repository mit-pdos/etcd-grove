#!/usr/bin/env python3
# Usage: etc/dsv/backtrack.py [-v] RUN... (as root; RUN as for tokens.py: a name under $DSV_LAB/runs, or
# a path): how much a run went back over work it had done, from its per-minute work-tree snapshots
# (runs/RUN/snapshots.git, written by snapshot.sh). Times are minutes from the run's first transcript
# line, pauses left out (tokens.clock). -v: the late rewrites, cascades and regressions one by one.
#
# Files: every X/Spec/....lean and X/Proof/....lean under the work tree. The same file in several copies
# (the project and the agent's worktrees) is one file: its path below the copy's root (the directory
# holding X/). A version is new content (comments, whitespace and imports dropped) not seen before in
# any copy, so a merge that brings a worktree's file into the project is not a rewrite.
#   spec rewrites     versions of a spec after its first; "late" when some proof that imports it
#                     (directly or through other specs) was already finished (no `sorry`) somewhere
#   proof rewrites    versions of a proof after it was first finished; a regression is a copy that
#                     was finished and gets a `sorry` again
#   invalidated       for each late spec rewrite, the finished proofs that import it; "reproved" are
#                     those with a new version afterwards
#   cascades          late spec rewrites linked through the call graph (the proof of G imports F's spec:
#                     G calls F) less than WINDOW minutes apart: going down a level to fix a spec and
#                     back up. Depth: the longest caller chain among the rewritten functions. A late
#                     rewrite needs a dependent proof finished GRACE minutes before (not a generator's rerun)
#   rework            lines changed in proofs after they were finished, over the lines of the final
#                     proofs; and in specs after their first version, over the final specs' lines
import difflib, os, re, subprocess, sys
from collections import defaultdict
from datetime import datetime
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import tokens

WINDOW = 45   # minutes between linked rewrites of a cascade
GRACE = 5     # a proof finished less than GRACE minutes before a spec rewrite is setup, not done work
IMPORT = re.compile(r'\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?(\S+)')
PATH = re.compile(r'^(?:(.*)/)?([^/]+)/(Spec|Proof)/(.+\.lean)$')


def strip(src):
    """the Lean source without comments, imports or blank space differences"""
    src = re.sub(r'/-.*?-/', ' ', src, flags=re.S)
    src = re.sub(r'--[^\n]*', '', src)
    src = '\n'.join(l for l in src.split('\n') if not IMPORT.match(l))
    return re.sub(r'\s+', ' ', src).strip()


def has_sorry(src):
    return re.search(r'\bsorry\b', strip(src)) is not None


def imports(src, pkg_prefix):
    return [m.replace('.', '/') + '.lean' for m in (IMPORT.match(l).group(1) for l in src.split('\n') if IMPORT.match(l))]


class Snapshots:
    def __init__(self, gitdir):
        self.g = gitdir

    def run(self, *a, input=None):
        return subprocess.run(['git', '--git-dir', self.g, *a], capture_output=True, input=input).stdout

    def commits(self):
        out = self.run('log', '--reverse', '--format=%H %s').decode().split('\n')
        return [l.split(' ', 1) for l in out if l.strip()]

    def changes(self, c, parent):
        a = ['diff-tree', '-r', '--no-commit-id', '--name-status', '-z']
        out = self.run(*(a + ([parent, c] if parent else ['--root', c]))).decode().split('\0')
        out = [x for x in out if x]
        return list(zip(out[0::2], out[1::2]))

    def blobs(self, c, paths):
        if not paths: return {}
        out = self.run('cat-file', '--batch', input=''.join('%s:%s\n' % (c, p) for p in paths).encode())
        res, i = {}, 0
        for p in paths:
            j = out.index(b'\n', i); head = out[i:j].split()
            if len(head) < 3 or head[1] == b'missing': i = j + 1; continue
            n = int(head[2]); res[p] = out[j + 1:j + 1 + n].decode(errors='replace'); i = j + 1 + n + 1
        return res


def analyze(run):
    S = Snapshots(os.path.join(run, 'snapshots.git'))
    t0, active, _ = tokens.clock(run)
    cs = S.commits()
    if not cs: return None
    if t0 is None:
        t0 = datetime.fromisoformat(cs[0][1].replace('Z', '+00:00'))
        active = lambda t: (t - t0).total_seconds() / 60
    mins = lambda s: active(datetime.fromisoformat(s.replace('Z', '+00:00')))

    versions = defaultdict(list)    # logical file -> [(t, normalized, raw)] new contents, in order
    seen = defaultdict(set)
    copies = {}                     # (root, logical) -> raw current content
    finished = {}                   # proof logical -> first time finished
    regress = []                    # (t, logical, root)
    copy_done = set()
    latest = {}                     # logical -> raw latest content (for imports)
    parent = None
    for c, stamp in cs:
        t = mins(stamp)
        ch = [(s, p) for s, p in S.changes(c, parent) if PATH.match(p)]
        parent = c
        body = S.blobs(c, [p for s, p in ch if s != 'D'])
        for s, p in ch:
            m = PATH.match(p); root, logical = m.group(1) or '', '%s/%s/%s' % m.group(2, 3, 4)
            if s == 'D':
                copies.pop((root, logical), None); continue
            raw = body.get(p)
            if raw is None: continue
            copies[(root, logical)] = raw; latest[logical] = raw
            n = strip(raw)
            if n not in seen[logical]:
                seen[logical].add(n); versions[logical].append((t, n, raw))
            if '/Proof/' in logical:
                if not has_sorry(raw):
                    finished.setdefault(logical, t); copy_done.add((root, logical))
                elif (root, logical) in copy_done:
                    copy_done.discard((root, logical)); regress.append((t, logical, root or '.'))

    # the import graph over logical files (a module A.B.C is A/B/C.lean below a root)
    logical_files = set(versions)
    imp = {f: [i for i in imports(latest[f], '') if i in logical_files] for f in logical_files}
    spec = lambda f: '/Spec/' in f
    proof_of = lambda f: f.replace('/Spec/', '/Proof/')
    spec_of = lambda f: f.replace('/Proof/', '/Spec/')

    def closure(f):  # the files f depends on, through Spec and non-function modules (never a Proof's import of a Proof)
        out, todo = set(), list(imp.get(f, []))
        while todo:
            x = todo.pop()
            if x in out: continue
            out.add(x); todo += imp.get(x, [])
        return out
    deps = {f: closure(f) for f in logical_files if '/Proof/' in f}
    users = defaultdict(set)
    for p, ds in deps.items():
        for d in ds:
            if spec(d): users[d].add(p)
    # call graph: G calls F when G's proof imports F's spec directly
    callers = defaultdict(set)
    for p in deps:
        for d in imp.get(p, []):
            if spec(d) and spec_of(p) != d: callers[d].add(spec_of(p))

    r = dict(run=os.path.basename(run.rstrip('/')), snapshots=len(cs),
             span='%.0f-%.0f' % (mins(cs[0][1]), mins(cs[-1][1])))
    specs = sorted(f for f in versions if spec(f)); proofs = sorted(f for f in versions if '/Proof/' in f)
    rewrites = []                   # (t, spec, late, invalidated, reproved)
    for f in specs:
        for t, n, raw in versions[f][1:]:
            done = sorted(p for p in users[f] if p in finished and finished[p] <= t - GRACE)
            rep = [p for p in done if any(tv > t for tv, _, _ in versions[p])]
            rewrites.append((t, f, bool(done), done, rep))
    rewrites.sort()
    late = [x for x in rewrites if x[2]]
    prew = {p: [t for t, _, _ in versions[p] if t > finished[p]] for p in proofs if p in finished}

    # cascades: late rewrites linked when one's function calls the other's and they are less than WINDOW
    # apart; a component spanning several functions went down a level and back up. Its depth: the
    # longest caller chain among its functions.
    n = len(late); comp = list(range(n))
    def find(x):
        while comp[x] != x: comp[x] = comp[comp[x]]; x = comp[x]
        return x
    for a in range(n):
        for b in range(a + 1, n):
            (ta, fa), (tb, fb) = late[a][:2], late[b][:2]
            if abs(ta - tb) <= WINDOW and (fa in callers[fb] or fb in callers[fa]):
                comp[find(a)] = find(b)
    groups = defaultdict(list)
    for a in range(n): groups[find(a)].append(late[a][:2])
    def depth(fs):
        memo = {}
        def d(f):
            if f not in memo:
                memo[f] = 0; memo[f] = 1 + max((d(g) for g in callers[f] if g in fs), default=0)
            return memo[f]
        return max(d(f) for f in fs)
    chains = [sorted(g) for g in groups.values()]
    deep = [(depth({f for _, f in c}), c) for c in chains if len({f for _, f in c}) > 1]

    def churn(f, since):
        vs = [raw for t, _, raw in versions[f] if t >= since]
        return sum(sum(1 for l in difflib.ndiff(a.split('\n'), b.split('\n')) if l[:1] in '+-')
                   for a, b in zip(vs, vs[1:]))
    final_lines = lambda fs: sum(len(latest[f].split('\n')) for f in fs) or 1
    pc = sum(churn(p, finished[p]) for p in finished)
    sc = sum(churn(f, versions[f][0][0]) for f in specs)

    r['spec files'] = len(specs)
    r['spec rewrites (early / late)'] = '%d (%d / %d)' % (len(rewrites), len(rewrites) - len(late), len(late))
    r['specs rewritten / late'] = '%d / %d' % (len({x[1] for x in rewrites}), len({x[1] for x in late}))
    r['proof files / finished'] = '%d / %d' % (len(proofs), len(finished))
    r['proof rewrites after finished'] = '%d (in %d proofs)' % (sum(map(len, prew.values())), sum(1 for v in prew.values() if v))
    r['regressions (copy back to sorry)'] = len(regress)
    r['proofs invalidated / reproved'] = '%d / %d' % (sum(len(x[3]) for x in late), sum(len(x[4]) for x in late))
    r['cascades (>1 level), max depth'] = '%d, %d' % (len(deep), max((d for d, _ in deep), default=1 if late else 0))
    r['proof churn after finished'] = '%d lines (%.0f%% of final)' % (pc, 100 * pc / final_lines(finished))
    r['spec churn after first'] = '%d lines (%.0f%% of final)' % (sc, 100 * sc / final_lines(specs))
    short = lambda f: re.sub(r'^[^/]+/(Spec|Proof)/', '', f)[:-5]
    detail = ['late spec rewrites (min  spec  invalidated -> reproved):']
    detail += ['  %5.0f  %s  %d -> %d' % (t, short(f), len(d), len(rp)) for t, f, _, d, rp in late]
    detail += ['cascades (depth: rewrites, in time order):'] + ['  %d: %s' % (d, ', '.join('%s@%.0f' % (short(f), t) for t, f in c)) for d, c in deep]
    detail += ['regressions:'] + ['  %5.0f  %s (%s)' % (t, short(f), root) for t, f, root in regress]
    return r, detail


if __name__ == '__main__':
    args = sys.argv[1:]; verbose = '-v' in args; args = [a for a in args if a != '-v']
    res = [x for x in (analyze(tokens.run_dir(a)) for a in args) if x]
    rows = [r for r, _ in res]
    keys = list(dict.fromkeys(k for r in rows for k in r if k != 'run'))
    w = max(len(k) for k in keys) + 2
    cw = [max(len(r['run']), *(len(str(r.get(k, ''))) for k in keys)) + 2 for r in rows]
    print(' ' * w + ''.join(r['run'].ljust(c) for r, c in zip(rows, cw)))
    for k in keys:
        print(k.ljust(w) + ''.join(str(r.get(k, '-')).ljust(c) for r, c in zip(rows, cw)))
    if verbose:
        for r, d in res:
            print('\n== ' + r['run']); print('\n'.join(d))
