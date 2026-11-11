#!/usr/bin/env python3
"""Check that a trust-boundary axiom whose Go function returns holding an `RWMutex` reader slot
charges a token for it, and that its closer gives one back (notes/begin-tok-plan.md, §5).

`sync.RWMutex` counts at most `2 ^ 30` readers; a reader slot held past a function's return (bbolt's
`DB.Begin(false)`: `mmaplock.RLock()` in `beginTx`, released by `removeTx`) is a resource the caller
must pay for, as the proved `DB.Begin.spec` does with a `threadTok`
(notes/axiom-review/backend-snapshot-begin.md). An axiom whose triple hands out such a slot for
free is false of Go (the read transactions of `bboltrd`).

1. The slot holders, from the Go sources of the projects (`.lake/goose/<project>`, which
   `etc/goose.py` fetches, this repository's own modules, and the standard library for its own
   packages; the sources, not the translations, so that a names-only function is scanned too):
   - a lock is (package, owner type, field): the struct type that declares the field, resolved
     from the expression's prefix by type (`db.mmaplock` with `db *DB`: `go.etcd.io/bbolt.DB.mmaplock`;
     a field promoted from an embedded struct is its declaring struct's; `s.RLock()` on a variable of
     a struct type embedding the mutex is that type's `RWMutex`), so that two types' same-named
     fields are two locks. An owner not resolved (an index, an interface, a mutex parameter) is
     `?`, which matches no resolved lock: a holder whose release is unresolved stays a holder (`-v`
     lists them);
   - a function holds a slot when an `E.RLock()` in it is followed by no `E.RUnlock()` at the same
     or an outer block depth and by no deferred `E.RUnlock()` (an `RUnlock` in an inner block is an
     error path's: `beginTx`'s `if !db.opened { ...RUnlock(); return }`);
   - a function releases one when it has an `E.RUnlock()` with no `E.RLock()` before it
     (`removeTx`), or calls a releaser of it (`close`, `Rollback`);
   - a function holds one too when it calls a holder (in its own package or one its file imports,
     resolved by type, below) and keeps what the call returns, a fixed point across packages
     (`DB.Begin`, and through it `backend.Snapshot`). **The release rule**: the result counts as
     released only when it is bound to a destination -- a variable or a field (`t, err :=`,
     `if t, err :=`, `x.tx =`) -- and a later resolved call of a releaser of that lock (one that
     does not itself hold it) is made on the destination (`t.Rollback()`, `x.tx.Rollback()`) or
     takes it as an argument. Every other result is held: returned, discarded (`_`), unbound (an
     expression statement, an argument of another call, a channel send `ch <- newBackend(...)`),
     or the call run by `go` or `defer`. A releaser called on something else does not release it.
2. The axioms: every `axiom <F>.wp_proof` under `Proof/` (and a part's `<root>/Proof/`) maps to its
   Go function by the layout (`Spec/<pkg>/<T>__<M>[_variant].lean`). If it is a holder, the axiom
   must state `<F>.spec`, and the spec file's declaration `abbrev <F>.spec` (only it: comments,
   docstrings and the file's other declarations are not read) must be one triple
   `∀ ..., {{ pre }} e {{ binders, RET v; post }}` whose **pre consumes a token**: a separating
   conjunct of the pre whose head is a token (`TOKENS`, applied to arguments or not), under
   parentheses, `iprop(...)` or `∃ x,`; in every disjunct of a `∨`; or in a branch of an
   `if c then A else B` (either branch: `Begin_kv`'s `if w then wrTok γ else threadTok`, whose read
   branch is the holder's, `w` not being mapped to the Go call's literal). A token under a wand,
   `□`, `⌜⌝`, a nested triple or any other connective does not count.
3. The closers: `etc/reader-slot-pairs.txt` lists each holder axiom with its closer axiom, an axiom
   of the same tree that states its spec, whose Go function releases every lock the holder holds,
   and whose **post returns a token**: a token conjunct, as in 2., of the post after `RET v;` (in
   every branch of an `if`). A holder axiom with no pair fails.
4. Exceptions: `etc/reader-slot-allow.txt`, one line per axiom:
   `NAME  lock=PKG.TYPE.FIELD...  (closer=AXIOM | held-for-life-by=PKG.[TYPE.]FUNC)  # why`.
   The `lock=`s must be exactly the locks the gate finds the axiom's function holding (an entry
   for one lock covers no other). The pairing is checked: a `closer=` as in 3. without the token
   (it releases the locks); a `held-for-life-by=` goroutine is a Go function here, started by a
   `go` statement in a function the holder reaches by resolved calls, which itself holds or
   releases those locks (`storage.OpenBackend`'s slot, rotated by `backend.run`'s commits). A
   malformed entry, or one without a reason, fails.

Calls are resolved by type, not only by name: a method call's receiver type comes from the
function's receiver, parameters, composite literals (`v := &T{...}`), struct fields (embedded ones
promoted) and the results of resolved calls, so `h.Write(...)` on a `hash.Hash32` is not mvcc's
`store.Write`. A call with a literal `bool` argument is specialised on it: the branches of an
`if p { ... return }` / `if !p { ... }` the argument rules out are skipped (`Begin(true)` takes the
writer's `rwlock`, not a reader slot of `mmaplock`). Unresolved calls are not followed.

Fails closed: the check exits 1, naming what is missing, when a Go source tree it needs is not here
-- `.lake/goose/<project>` of bbolt, etcd, or any project an axiom's package maps to (`PROJECTS`, per
part: RaftWitness's raft is `raft-witness`), a package of such a project, or the toolchain's GOROOT
(`go env GOROOT`) -- and when an axiom's package has no source and is not a known third-party
package (`THIRD_PARTY`, an explicit list). It also refuses fewer than `MIN_SCANNED` scanned axioms:
raise the floor to the count `reader-slot: ok (...)` prints when axioms are added (in the same
commit); lower it only with a reason. Every file's axiom is checked, also when its name occurs in
another file (RaftWitness's copies of main-tree modules, `k8s.io/api`'s two `Resource`s), each tree
against its own sources.

Limits (the gate's reach):
- Unscanned axioms (`-v` lists them, by reason): 201 of the 401 axioms on 2026-11-06. 175 are of
  third-party packages not cloned here (names-only dependencies, `THIRD_PARTY`), by package: grpc 30
  (and credentials/insecure 1, grpclog 1, health 2, grpc_health_v1 2, metadata 4, peer 1, status 4),
  protobuf `proto` 22 (and RaftWitness's copies 9), zap 22 (zapcore 1), prometheus client_golang 7
  and grpc_ecosystem's 5, k8s.io/utils clock 7 and trace 2, k8s
  apimachinery/apiserver/api/component-base and klog 31 (apps/v1 3, core/v1 3, errors 2, meta/v1 1,
  conversion 1, fields 1, labels 1, runtime/schema 2, intstr 1, resourceversion 1, util/runtime 1,
  audit 1, etcd3/metrics 4, component-base metrics 1 and tracing 4, klog 4), Masterminds/semver 6,
  x/time/rate 5, otel attribute 4 and trace 2 (otelgrpc 1), x/crypto/bcrypt 2, xiang90/probing 2,
  go-humanize 1, clockwork 1. 26 are variants with no Go function of their name (standard
  library: context 8, fmt 6, errors 4, encoding/binary 3, container/heap 1; etcd: client
  resolver 1, traceutil 1, membership 1, snap 1). None of those packages' functions is known to
  hold a reader slot past its return, but the gate does not check it.
- A function that releases its reader before it returns is not a holder, however long it holds
  it. The hazard (notes/axiom-review/begin-tok-restated.md, A10): a future spec of `backend.Hash`
  or `Defrag` that runs a caller's callback inside `db.View` would let the callback nest unpaid
  readers (call `Begin(false)` again, or wait on a reader), which this scan would not catch.
  Such a spec must take a token for the callback's duration.
- Release and hold are path-insensitive beyond a literal `bool` argument: `Tx.Commit` counts as a
  releaser of `mmaplock` (it reaches `tx.close()` → `removeTx`), though on a read transaction it
  returns `ErrTxNotWritable` first; so a `closer=bbolt.Tx.Commit_kv` would pass the release check.
  A paired closer must also give the token back (3.), which `Commit_kv`'s post does not.
- A name-level check of the sources and a syntactic one of the spec, not a proof, as
  `errorf-wrap-check.py` is.

usage: etc/reader-slot-check.py [-v]   (exit 1 on a holder axiom whose pre consumes no token, a
                                        missing pair, a closer that does not release the lock or
                                        whose post returns no token, an allow entry whose locks or
                                        pairing do not match, a missing source tree, or fewer than
                                        MIN_SCANNED axioms scanned)
"""
import os
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
TOKENS = re.compile(r'\b(threadTok|levelTok|rdTok|ownThreadLoan)\b')
PAIRS = ROOT / 'etc' / 'reader-slot-pairs.txt'
ALLOW = ROOT / 'etc' / 'reader-slot-allow.txt'
# a part (CLAUDE.md, "Layout") and the source tree it is translated from, searched first
PARTS = {'RaftWitness': ['raft-witness'], 'PorcupineDag': []}
# the Go source trees `etc/goose.py` clones (`.lake/goose/<project>`; `READER_SLOT_GOOSE` points the
# check at another directory, for testing that a missing tree fails it)
GOOSE = pathlib.Path(os.environ.get('READER_SLOT_GOOSE', ROOT / '.lake' / 'goose'))
# the projects whose sources must be here: an axiom of a package below the Lean directory (the Go
# path mangled) is scanned in that project's tree (per part; '' is this repository's own modules),
# and the check fails if the tree, or the package in it, is missing
PROJECTS = {
    '': {'go_etcd_io/bbolt': 'bbolt', 'go_etcd_io/etcd': 'etcd', 'go_etcd_io/raft': 'raft',
         'github_com/mit_pdos/etcd_grove': ''},
    'RaftWitness': {'go_etcd_io/raft': 'raft-witness'},
    'PorcupineDag': {},
}
ALWAYS = ('bbolt', 'etcd')     # required even if no axiom of theirs is left
# the packages known to be third-party and not cloned (names-only translations): their axioms are
# unscanned, "no Go source here"; an axiom of any other package without sources fails the check
THIRD_PARTY = (
    'github_com/Masterminds/semver', 'github_com/dustin/go_humanize', 'github_com/grpc_ecosystem',
    'github_com/jonboulle/clockwork', 'github_com/prometheus/client_golang', 'github_com/xiang90/probing',
    'go_opentelemetry_io/contrib', 'go_opentelemetry_io/otel', 'go_uber_org/zap',
    'golang_org/x/crypto', 'golang_org/x/time', 'google_golang_org/grpc', 'google_golang_org/protobuf',
    'k8s_io/api', 'k8s_io/apimachinery', 'k8s_io/apiserver', 'k8s_io/component_base', 'k8s_io/klog',
    'k8s_io/utils/clock', 'k8s_io/utils/trace',
)
# the scanned axioms' count may not fall below this (a tree or package gone, or the layout's
# mapping broken, would move axioms out of the scan): when axioms are added and the count rises,
# raise it to the count `reader-slot: ok (...)` prints; lower it only with a reason in the commit
MIN_SCANNED = 200


def under(a, prefix):
    return a == prefix or a.startswith(prefix + '/')
LOCK_OPS = {'RLock', 'RUnlock', 'Lock', 'Unlock', 'TryLock', 'TryRLock'}


# ---------------------------------------------------------------------------------------------
# Go sources

def blank(src):
    """`src` with string, rune and comment contents replaced by spaces (newlines kept)."""
    out = list(src)
    i, n = 0, len(src)
    while i < n:
        c = src[i]
        if c == '/' and i + 1 < n and src[i + 1] == '/':
            j = src.find('\n', i)
            j = n if j < 0 else j
            for k in range(i, j):
                out[k] = ' '
            i = j
        elif c == '/' and i + 1 < n and src[i + 1] == '*':
            j = src.find('*/', i + 2)
            j = n if j < 0 else j + 2
            for k in range(i, j):
                if out[k] != '\n':
                    out[k] = ' '
            i = j
        elif c in '"\'`':
            q = c
            j = i + 1
            while j < n and src[j] != q:
                if q != '`' and src[j] == '\\':
                    j += 1
                elif q != '`' and src[j] == '\n':
                    break
                j += 1
            for k in range(i + 1, min(j, n)):
                if out[k] != '\n':
                    out[k] = ' '
            i = j + 1
        else:
            i += 1
    return ''.join(out)


FUNC = re.compile(r'^func\s*(?:\(\s*(?:(\w+)\s+)?\*?\s*(\w+)(?:\[[^\]]*\])?\s*\)\s*)?(\w+)\s*(?:\[[^\]]*\])?\s*\(',
                  re.M)
IMPORT_BLOCK = re.compile(r'^import\s*\(([^)]*)\)', re.M)
IMPORT_ONE = re.compile(r'^import\s+(\w+\s+|\.\s+|_\s+)?"([^"]+)"', re.M)
IMPORT_LINE = re.compile(r'^\s*(\w+|\.|_)?\s*"([^"]+)"', re.M)


def body_start(b, i):
    """The index of the body's `{` of the function whose parameters start at `b[i] == '('`."""
    depth = 0
    n = len(b)
    while i < n:
        c = b[i]
        if c in '([':
            depth += 1
        elif c in ')]':
            depth -= 1
        elif c == '{' and depth == 0:
            pre = b[max(0, i - 10):i].rstrip()
            if pre.endswith('interface') or pre.endswith('struct'):
                i = match_brace(b, i) + 1
                continue
            return i
        elif c == '\n' and depth == 0 and b[i - 1] != ',':
            # a declaration without a body (assembly)
            k = i + 1
            while k < n and b[k] in ' \t':
                k += 1
            if k < n and b[k] != '{':
                return -1
        i += 1
    return -1


def match_brace(b, i):
    depth = 0
    for j in range(i, len(b)):
        if b[j] == '{':
            depth += 1
        elif b[j] == '}':
            depth -= 1
            if depth == 0:
                return j
    return len(b) - 1


class Func:
    def __init__(self, pkg, recvname, recv, name, params, rtype, body, imports, file, line):
        self.pkg, self.recvname, self.recv, self.name, self.body = pkg, recvname, recv, name, body
        self.params, self.rtype = params, rtype
        self.imports, self.file, self.line = imports, file, line
        self.key = (pkg, f'{recv}.{name}' if recv else name)

    def __repr__(self):
        return f'{self.pkg}.{self.key[1]}'


# the struct types' fields: (pkg, T) -> {field: (type text, the file's imports)}; embedded fields
# are also listed under '' as [(type text, imports)]
STRUCTS = {}
STRUCT = re.compile(r'^(?:type[ \t]+|\t)(\w+)\s*(?:\[[^\]]*\])?[ \t]+struct\s*\{', re.M)


def split_top(t):
    """`t` split at its top-level commas."""
    out, depth, cur = [], 0, ''
    for c in t:
        if c in '([{':
            depth += 1
        elif c in ')]}':
            depth -= 1
        if c == ',' and depth == 0:
            out.append(cur)
            cur = ''
        else:
            cur += c
    if cur.strip():
        out.append(cur)
    return [x.strip() for x in out if x.strip()]


def parse_params(t):
    """`a, b int, c *T` -> [('a', 'int'), ('b', 'int'), ('c', '*T')] (names None if unnamed)."""
    parts = split_top(t)
    out, cur = [], None
    for part in reversed(parts):
        bits = part.split(None, 1)
        if len(bits) == 2 and re.fullmatch(r'\w+', bits[0]):
            cur = bits[1]
            out.append((bits[0], bits[1]))
        elif cur is not None and re.fullmatch(r'\w+', part):
            out.append((part, cur))
        else:
            out.append((None, part))
    return list(reversed(out))


def read_structs(path, b, imports):
    for m in STRUCT.finditer(b):
        o = b.index('{', m.end() - 1)
        e = match_brace(b, o)
        fields, depth, line = {'': []}, 0, ''
        for c in b[o + 1:e]:
            if c == '{':
                depth += 1
            elif c == '}':
                depth -= 1
            if c == '\n':
                line = line.strip()
                if line:
                    em = re.fullmatch(r'\*?([\w.]+)', line.split()[0]) if len(line.split()) == 1 else None
                    if em:
                        fields[em.group(1).rsplit('.', 1)[-1]] = (line, imports)
                        fields[''].append((line, imports))
                    else:
                        nm = re.match(r'([\w, ]+?)\s+(\S.*)$', line)
                        if nm:
                            for n in nm.group(1).split(','):
                                if n.strip():
                                    fields[n.strip()] = (nm.group(2), imports)
                line = ''
            elif depth == 0 and c not in '{}':
                line += c
        STRUCTS[(path, m.group(1))] = fields


def read_package(path, d):
    funcs = []
    try:
        names = sorted(os.listdir(d))
    except OSError:
        return None
    gofiles = [x for x in names if x.endswith('.go') and not x.endswith('_test.go')]
    if not gofiles:
        return None
    for x in gofiles:
        f = os.path.join(d, x)
        try:
            src = open(f, encoding='utf-8', errors='replace').read()
        except OSError:
            continue
        if re.search(r'^package\s+main\b', src, re.M) and path:
            pass
        imports = {}
        for blk in IMPORT_BLOCK.findall(src):
            for alias, p in IMPORT_LINE.findall(blk):
                imports[alias or p.rsplit('/', 1)[-1]] = p
        for alias, p in IMPORT_ONE.findall(src):
            alias = alias.strip()
            imports[alias or p.rsplit('/', 1)[-1]] = p
        # a versioned path's package name is the element before `/vN`
        for a, p in list(imports.items()):
            if re.fullmatch(r'v\d+', a):
                imports[p.rsplit('/', 2)[-2].replace('-', '_')] = p
        b = blank(src)
        read_structs(path, b, imports)
        for m in FUNC.finditer(b):
            s = body_start(b, m.end() - 1)
            if s < 0:
                continue
            pe = match_paren(b, m.end() - 1)
            params = parse_params(b[m.end():pe])
            res = b[pe + 1:s].strip()
            if res.startswith('('):
                rs = parse_params(res[1:match_paren(res, 0)])
                rtype = rs[0][1] if rs else None
            else:
                rtype = res or None
            e = match_brace(b, s)
            funcs.append(Func(path, m.group(1), m.group(2), m.group(3), params, rtype, b[s:e + 1],
                              imports, f, b.count('\n', 0, m.start()) + 1))
    return funcs


def match_paren(b, i):
    depth = 0
    for j in range(i, len(b)):
        if b[j] in '([':
            depth += 1
        elif b[j] in ')]':
            depth -= 1
            if depth == 0:
                return j
    return len(b) - 1


def mangle(p):
    return p.replace('.', '_').replace('-', '_')


class Sources:
    def __init__(self):
        self.mods = []          # (module path, dir, tree)
        trees = []
        if GOOSE.is_dir():
            for t in sorted(GOOSE.iterdir()):
                if t.is_dir() and t.name not in ('bin', 'perennial') and not t.name.endswith('.proph'):
                    trees.append((t.name, t))
        trees.append(('', ROOT))
        self.trees = dict(trees)
        for name, t in trees:
            for dp, dns, fns in os.walk(t):
                rel = os.path.relpath(dp, ROOT)
                dns[:] = [x for x in dns if x not in ('vendor', 'testdata', '.git', 'node_modules')
                          and not (name == '' and dp == str(ROOT) and x in ('.lake', 'old'))]
                if 'go.mod' in fns:
                    m = re.search(r'^module\s+(\S+)', open(os.path.join(dp, 'go.mod')).read(), re.M)
                    if m:
                        self.mods.append((m.group(1), dp, name))
        self.goroot = None
        try:
            r = subprocess.run(['go', 'env', 'GOROOT'], capture_output=True, text=True, timeout=120)
            if r.returncode == 0 and r.stdout.strip():
                self.goroot = pathlib.Path(r.stdout.strip()) / 'src'
        except (OSError, subprocess.TimeoutExpired):
            pass
        if self.goroot is None:
            # without the toolchain's sources every standard-library axiom would go unscanned and
            # the check would pass on less; refuse instead (etc/gates.sh puts go on PATH)
            sys.exit('reader-slot: `go env GOROOT` failed: put go on PATH '
                     '(export PATH=$PATH:/usr/local/go/bin)')
        self.pkgs = {}          # import path -> [Func] or None

    def std(self, p):
        return '.' not in p.split('/', 1)[0]

    def find_dir(self, p, prefer=()):
        if self.std(p):
            if self.goroot and (self.goroot / p).is_dir():
                return str(self.goroot / p)
            return None
        best = None
        for mp, d, tree in self.mods:
            if p == mp or p.startswith(mp + '/'):
                rank = (tree in prefer, len(mp))
                if best is None or rank > best[0]:
                    best = (rank, os.path.join(d, p[len(mp) + 1:]) if p != mp else d)
        return best[1] if best and os.path.isdir(best[1]) else None

    def from_mangled(self, a, prefer=()):
        """The Go import path of the Lean package directory `a`, if its source is here."""
        if self.goroot and (self.goroot / a).is_dir() and '_' not in a.split('/', 1)[0]:
            return a
        best = None
        for mp, d, tree in self.mods:
            mm = mangle(mp)
            if a == mm or a.startswith(mm + '/'):
                p = mp + a[len(mm):]
                rank = (tree in prefer, len(mp))
                if (best is None or rank > best[0]) and self.find_dir(p, prefer):
                    best = (rank, p)
        return best[1] if best else None

    def load(self, p, prefer=()):
        if p not in self.pkgs:
            d = self.find_dir(p, prefer)
            self.pkgs[p] = read_package(p, d) if d else None
        return self.pkgs[p]


# ---------------------------------------------------------------------------------------------
# holders and releasers

LOCKOP = re.compile(r'([\w\.\[\]]+)\.(RLock|RUnlock)\(\)')
CALL = re.compile(r'(?<![\w.)\]])((?:\w+(?:\(\))?\.)*)(\w+)\s*\(')


def depths(body):
    """The block depth at every index, and whether the innermost block there is a `defer func`."""
    d, stack, dep, dfr = 0, [], [0] * len(body), [False] * len(body)
    for i, c in enumerate(body):
        if c == '{':
            line_start = body.rfind('\n', 0, i) + 1
            stack.append('defer' in body[line_start:i] or (bool(stack) and stack[-1]))
            d += 1
        dep[i] = d
        dfr[i] = bool(stack) and stack[-1]
        if c == '}':
            d -= 1
            if stack:
                stack.pop()
    return dep, dfr


def lock_facts(f, ident):
    """`f`'s locks held at its return ({lock: [positions of the RLocks]}) and its unmatched
    releases, each lock identified by `ident(f, expr)`: (package, owner type, field)."""
    ops = [(m.start(), m.group(1), m.group(2)) for m in LOCKOP.finditer(f.body)]
    if not ops:
        return {}, set()
    dep, dfr = depths(f.body)
    held, rel = {}, set()
    for k, (i, e, op) in enumerate(ops):
        line = f.body[f.body.rfind('\n', 0, i) + 1:i]
        deferred = 'defer' in line or dfr[i]
        if op == 'RLock':
            if any(op2 == 'RUnlock' and e2 == e and
                   (dep[j] <= dep[i] or 'defer' in f.body[f.body.rfind('\n', 0, j) + 1:j] or dfr[j])
                   for j, e2, op2 in ops[k + 1:]):
                continue
            if any(op2 == 'RUnlock' and e2 == e and
                   ('defer' in f.body[f.body.rfind('\n', 0, j) + 1:j] or dfr[j])
                   for j, e2, op2 in ops[:k]):
                continue
            held.setdefault(ident(f, e), []).append(i)
        elif not any(op2 == 'RLock' and e2 == e for j, e2, op2 in ops[:k]) and not deferred:
            rel.add(ident(f, e))
    return held, rel


def lock_name(lk):
    """`go.etcd.io/bbolt.DB.mmaplock` (an unresolved owner type is `?`)."""
    pkg, t, x = lk
    return f'{pkg}.{t}.{x}'


class Graph:
    """The loaded packages' functions with typed call resolution: a method call `x.f.M(...)` is
    resolved only when the type of `x.f` is known (a receiver, a parameter, a composite literal,
    a call's first result, a struct field, through embedded fields), never by the method's name
    alone; a call of a function value or through an interface is not resolved."""

    def __init__(self, funcs):
        self.funcs = funcs
        self.by_name = {}
        for f in funcs:
            self.by_name.setdefault((f.pkg, f.name), []).append(f)
        self.locals = {}
        self.locs = {}          # id(f) -> its local variables' types (the final map)
        self.unresolved_locks = set()

    def norm(self, texpr, pkg, imports):
        """The named type `(pkg, T)` a type expression denotes, if any."""
        if not texpr:
            return None
        m = re.match(r'^\s*[*&]?\s*(\w+)(?:\.(\w+))?\s*(?:\[[^\]]*\])?\s*$', texpr)
        if not m:
            return None
        if m.group(2):
            q = imports.get(m.group(1))
            return (q, m.group(2)) if q else None
        return (pkg, m.group(1))

    def methods(self, t, name, depth=0):
        pkg, T = t
        out = [g for g in self.by_name.get((pkg, name), []) if g.recv == T]
        if out or depth > 2:
            return out
        for texpr, imps in STRUCTS.get(t, {}).get('', []):
            et = self.norm(texpr, pkg, imps)
            if et:
                out += self.methods(et, name, depth + 1)
        return out

    def field(self, t, name, depth=0):
        fs = STRUCTS.get(t)
        if not fs:
            return None
        if name in fs:
            texpr, imps = fs[name]
            return self.norm(texpr, t[0], imps)
        if depth > 2:
            return None
        for texpr, imps in fs.get('', []):
            et = self.norm(texpr, t[0], imps)
            if et:
                r = self.field(et, name, depth + 1)
                if r:
                    return r
        return None

    def field_owner(self, t, name, depth=0):
        """The struct type that declares field `name` of `t` (`t` itself, or a type embedded in it)."""
        fs = STRUCTS.get(t)
        if not fs:
            return None
        if name in fs:
            return t
        if depth > 2:
            return None
        for texpr, imps in fs.get('', []):
            et = self.norm(texpr, t[0], imps)
            if et:
                r = self.field_owner(et, name, depth + 1)
                if r:
                    return r
        return None

    def lock_ident(self, f, e):
        """The lock `e.RLock()` takes in `f`: (package, owner type, field), the field's declaring
        struct type resolved from `e`'s prefix (`db.mmaplock`: `bbolt.DB`'s `mmaplock`); a variable
        of a struct type embedding the mutex (`s.RLock()`) is that type's `RWMutex`. When the owner
        is not resolved, (f's package, `?`, field): it never matches a resolved lock, so a holder
        whose release is not resolved stays a holder (`-v` lists them)."""
        self.calls(f)
        loc = self.locs[id(f)]
        elems = [x for x in e.split('.') if x]
        if '[' in e or not elems:
            self.unresolved_locks.add((repr(f), e))
            return (f.pkg, '?', elems[-1] if elems else e)
        if len(elems) == 1:
            t = loc.get(elems[0])
            if t and t != ('sync', 'RWMutex'):
                return (t[0], t[1], 'RWMutex')
            self.unresolved_locks.add((repr(f), e))
            return (f.pkg, '?', elems[0])
        t = self.chain_type(f, elems[:-1], loc)
        o = self.field_owner(t, elems[-1]) if t else None
        if o is None:
            self.unresolved_locks.add((repr(f), e))
            return (f.pkg, '?', elems[-1])
        return (o[0], o[1], elems[-1])

    def chain_type(self, f, elems, loc):
        """The type of `e0.e1...` (an element `g()` is a call without arguments)."""
        if not elems:
            return None
        e0 = elems[0]
        if e0 in loc:
            t = loc[e0]
            rest = elems[1:]
        elif e0 in f.imports and len(elems) >= 2 and elems[1].endswith('()'):
            gs = [g for g in self.by_name.get((f.imports[e0], elems[1][:-2]), []) if not g.recv]
            if len(gs) != 1:
                return None
            t = self.norm(gs[0].rtype, gs[0].pkg, gs[0].imports)
            rest = elems[2:]
        elif e0.endswith('()'):
            gs = [g for g in self.by_name.get((f.pkg, e0[:-2]), []) if not g.recv]
            if len(gs) != 1:
                return None
            t = self.norm(gs[0].rtype, gs[0].pkg, gs[0].imports)
            rest = elems[1:]
        else:
            return None
        for e in rest:
            if t is None:
                return None
            if e.endswith('()'):
                gs = self.methods(t, e[:-2])
                if len(gs) != 1:
                    return None
                t = self.norm(gs[0].rtype, gs[0].pkg, gs[0].imports)
            else:
                t = self.field(t, e)
        return t

    def resolve(self, f, chain, name, loc):
        if name in LOCK_OPS:
            return []
        elems = [e for e in chain.split('.') if e] if chain else []
        if not elems:
            return [g for g in self.by_name.get((f.pkg, name), []) if not g.recv and g is not f]
        if len(elems) == 1 and elems[0] in f.imports and elems[0] not in loc:
            return [g for g in self.by_name.get((f.imports[elems[0]], name), []) if not g.recv]
        t = self.chain_type(f, elems, loc)
        return [g for g in self.methods(t, name) if g is not f] if t else []

    def calls(self, f):
        """`f`'s resolved calls: [(position, callee, args text, the call's line prefix)], and the
        local variables' types, built in order."""
        if id(f) in self.locals:
            return self.locals[id(f)]
        loc = {}
        if f.recvname and f.recv:
            loc[f.recvname] = (f.pkg, f.recv)
        for n, texpr in f.params:
            t = self.norm(texpr, f.pkg, f.imports) if n else None
            if t:
                loc[n] = t
        out = []
        b = f.body
        events = []
        for m in DECL.finditer(b):
            events.append((m.start(), 'decl', m))
        for m in CALL.finditer(b):
            events.append((m.start(), 'call', m))
        events.sort(key=lambda x: (x[0], x[1] != 'decl'))
        for pos, kind, m in events:
            if kind == 'decl':
                t = self.norm(m.group(2), f.pkg, f.imports)
                if t:
                    loc[m.group(1)] = t
                continue
            chain, name = m.group(1) or '', m.group(2)
            if not chain and name in ('func', 'if', 'for', 'switch', 'return', 'make', 'new', 'len',
                                      'append', 'cap', 'panic', 'copy', 'delete', 'close'):
                continue
            gs = self.resolve(f, chain.rstrip('.'), name, loc)
            ae = match_paren(b, m.end() - 1)
            args = split_top(b[m.end():ae])
            line = b[b.rfind('\n', 0, m.start()) + 1:m.start()]
            for g in gs:
                out.append((m.start(), g, args, line, chain.rstrip('.')))
            am = re.match(r'\s*(?:if\s+)?(\w+)\s*(?:,\s*\w+\s*)*:?=\s*$', line)
            if am and len(gs) == 1:
                t = self.norm(gs[0].rtype, gs[0].pkg, gs[0].imports)
                if t:
                    loc[am.group(1)] = t
        self.locals[id(f)] = out
        self.locs[id(f)] = loc
        return out


DECL = re.compile(r'\b(\w+)\s*(?::=|=)\s*&?([\w.]+)\s*\{')


def excluded(g, args):
    """The ranges of `g`'s body not run under the call's literal `true`/`false` arguments (a
    branch on a `bool` parameter: `DB.Begin(writable)`'s `if writable { return ... }`)."""
    out = []
    for k, (p, texpr) in enumerate(g.params):
        if p is None or texpr.strip() != 'bool' or k >= len(args) or args[k] not in ('true', 'false'):
            continue
        val = args[k] == 'true'
        for m in re.finditer(r'\bif\s+(!?)\s*' + re.escape(p) + r'\s*\{', g.body):
            o = m.end() - 1
            e = match_brace(g.body, o)
            pos = (m.group(1) == '')
            if pos != val:
                out.append((o, e))
            elif re.search(r'\breturn\b', g.body[o:e]):
                # the branch taken returns: what follows it is not run
                out.append((e + 1, len(g.body)))
    return out


# the destination of a call's result, from the statement before it: `v :=`, `v, err =`,
# `a.b.c =`, also after `if ` (`if tx, err := ...; ...`)
DEST = re.compile(r'\s*(?:if\s+)?([\w.]+)\s*(?:,\s*\w+\s*)*:?=\s*$')


def analyze(src, roots):
    """The holders: {func key: {lock: [positions]}}; the releasers: {key: locks}; a lock is
    (package, owner type, field)."""
    todo = list(roots)
    while todo:
        p, prefer = todo.pop()
        fs = src.load(p, prefer)
        if not fs or src.std(p):
            continue
        for f in fs:
            for q in set(f.imports.values()):
                if q not in src.pkgs and not src.std(q):
                    todo.append((q, prefer))
    funcs = [f for fs in src.pkgs.values() if fs for f in fs]
    G = Graph(funcs)
    calls = {f.key: G.calls(f) for f in funcs}
    holds, releases = {}, {}
    for f in funcs:
        h, r = lock_facts(f, G.lock_ident)
        if h:
            holds[f.key] = h
        if r:
            releases[f.key] = set(r)
    fkey = {f.key: f for f in funcs}

    def held_by(g, args):
        hs = holds.get(g.key, {})
        if not hs:
            return set()
        ex = excluded(g, args)
        return {lk for lk, ps in hs.items() if any(not any(a <= x <= b for a, b in ex) for x in ps)}

    # the releasers first, to their fixed point (they do not depend on the holders)
    changed = True
    while changed:
        changed = False
        for f in funcs:
            for i, g, args, line, _ in calls[f.key]:
                new = releases.get(g.key, set()) - releases.get(f.key, set())
                if new:
                    releases.setdefault(f.key, set()).update(new)
                    changed = True
    changed = True
    while changed:
        changed = False
        for f in funcs:
            for i, g, args, line, _ in calls[f.key]:
                gh = held_by(g, args)
                if not gh:
                    continue
                # the result's destination: only a result bound to a variable or a field (`v`,
                # `a.b.c`) can be released, by a later call of a releaser on it; a result that is
                # returned, discarded (`_`), unbound (an expression statement, an argument, a channel
                # send, `go`, `defer`) is held (see the docstring, 1.)
                m = DEST.match(line)
                v = m.group(1) if m and m.group(1) not in ('_', 'return') else None
                for lk in gh:
                    if i in holds.get(f.key, {}).get(lk, []):
                        continue
                    # released by a later resolved call of a releaser of the lock that does not
                    # also hold it (`unsafeCommit` rolls the old read transaction back and begins a
                    # new one: a holder), on the destination or with it as an argument
                    def releaser(h):
                        return lk in releases.get(h.key, set()) and lk not in holds.get(h.key, {})
                    if v and any(releaser(h) and (c == v or c.startswith(v + '.') or v in a)
                                 for j, h, a, _, c in calls[f.key] if j > i):
                        continue
                    holds.setdefault(f.key, {}).setdefault(lk, []).append(i)
                    changed = True
    return holds, releases, fkey, calls, G


def callees(fkey, calls, k):
    """The keys of the functions `k` reaches by resolved calls, `k` included."""
    seen, todo = {k}, [k]
    while todo:
        x = todo.pop()
        for _, g, _, _, _ in calls.get(x, []):
            if g.key not in seen:
                seen.add(g.key)
                todo.append(g.key)
    return seen


def go_key(k):
    return f'{k[0]}.{k[1]}'


# ---------------------------------------------------------------------------------------------
# the axioms

# any Lean name (`zap.Int'` too): a name the pattern missed would be silently unchecked
AXIOM = re.compile(r'^axiom\s+(\S+?)\.wp_proof\b', re.M)


def strip_lean_comments(s):
    out, i, depth = [], 0, 0
    while i < len(s):
        if s.startswith('/-', i):
            depth += 1
            i += 2
        elif depth and s.startswith('-/', i):
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif s.startswith('--', i):
            j = s.find('\n', i)
            i = len(s) if j < 0 else j
        else:
            out.append(s[i])
            i += 1
    return ''.join(out)


OPEN, CLOSE = '([{⟨⌜', ')]}⟩⌝'


def top_split(t, sep):
    """`t` split at the occurrences of `sep` outside brackets."""
    out, depth, start, i = [], 0, 0, 0
    while i < len(t):
        c = t[i]
        if c in OPEN:
            depth += 1
        elif c in CLOSE:
            depth -= 1
        elif depth == 0 and t.startswith(sep, i):
            out.append(t[start:i])
            i += len(sep)
            start = i
            continue
        i += 1
    out.append(t[start:])
    return [x.strip() for x in out]


def unwrap(t):
    """`t` without enclosing parentheses, `iprop(...)` and a leading `∃ x y,`."""
    while True:
        t = t.strip()
        m = re.match(r'iprop\s*\(', t)
        if m and match_paren(t, m.end() - 1) == len(t) - 1:
            t = t[m.end():-1]
        elif t.startswith('(') and match_paren(t, 0) == len(t) - 1:
            t = t[1:-1]
        elif t.startswith('∃') and len(top_split(t, ',')) > 1:
            t = t[t.index(top_split(t, ',')[0]) + len(top_split(t, ',')[0]) + 1:]
        else:
            return t


def gives_token(t, branches='any'):
    """Whether the assertion `t` holds a token (`TOKENS`) as a separating conjunct: a conjunct whose
    head is a token, in every disjunct of a `∨`, in a branch of an `if c then A else B` (any branch
    for a pre, `branches='any'`: `Begin_kv`'s `if w then wrTok γ else threadTok`, whose read
    branch is the slot holder's; every branch for a post, `'all'`). A token under a wand, a `□`, a
    pure `⌜⌝`, a nested triple or any other connective does not count."""
    t = unwrap(t)
    conj = top_split(t, '∗')
    if len(conj) > 1:
        return any(gives_token(c, branches) for c in conj)
    disj = top_split(t, '∨')
    if len(disj) > 1:
        return all(gives_token(d, branches) for d in disj)
    m = re.match(r'if\s', t)
    if m:
        th = top_split(t, ' then ')
        if len(th) == 2:
            el = top_split(th[1], ' else ')
            if len(el) == 2:
                bs = [gives_token(x, branches) for x in el]
                return any(bs) if branches == 'any' else all(bs)
        return False
    hm = re.match(r'(\w+)', t)
    return bool(hm and TOKENS.fullmatch(hm.group(1)) and
                re.fullmatch(r'\w+(\s+[\w.\']+)*', t) is not None)


def spec_triple(path, name):
    """The pre and the post (after `RET v;`) of the one triple `abbrev <name>.spec : Prop := ∀ ...,
    {{ pre }} e {{ binders, RET v; post }}` in the spec file `path`, from that declaration only
    (comments and docstrings stripped), or a string saying why it cannot be read."""
    if not path.exists():
        return f'no spec file {path.relative_to(ROOT)}'
    text = strip_lean_comments(path.read_text())
    m = re.search(r'^(?:@\[[^\]]*\]\s*)?(?:abbrev|def)\s+' + re.escape(name + '.spec') + r'\s*:', text, re.M)
    if not m:
        return f'{path.relative_to(ROOT)} declares no `{name}.spec`'
    end = re.compile(r'^\S', re.M).search(text, m.end())
    decl = text[m.end():end.start() if end else len(text)]
    parts, depth, i = [], 0, 0
    while i < len(decl):
        c = decl[i]
        if c in OPEN:
            if depth == 0 and decl.startswith('{{', i):
                parts.append([i + 2, None])
            depth += 1
        elif c in CLOSE:
            depth -= 1
            if depth == 0 and parts and parts[-1][1] is None and c == '}' and decl[i - 1] == '}':
                parts[-1][1] = i - 1
        i += 1
    if len(parts) != 2 or any(e is None for _, e in parts):
        return f'`{name}.spec` is not one triple `{{{{ pre }}}} e {{{{ post }}}}` ({len(parts)} top-level `{{{{`)'
    pre = decl[parts[0][0]:parts[0][1]]
    post = decl[parts[1][0]:parts[1][1]]
    r = top_split(post, 'RET')
    if len(r) != 2 or len(top_split(r[1], ';')) < 2:
        return f'`{name}.spec`\'s post has no `RET v;`'
    body = r[1][r[1].index(top_split(r[1], ';')[0]) + len(top_split(r[1], ';')[0]) + 1:]
    return pre, body


def axiom_states(base, rel, name):
    """Whether `axiom <name>.wp_proof` in its proof file states `<name>.spec`."""
    t = strip_lean_comments((base / 'Proof' / rel).read_text())
    m = re.search(r'^axiom\s+' + re.escape(name) + r'\.wp_proof\s*:\s*(\S+)', t, re.M)
    return bool(m and m.group(1) == name + '.spec')


def axioms():
    """Every `axiom <F>.wp_proof` in every file, as [(name, base, rel)]: a name may occur in several
    files (a part's copies of main-tree modules, `k8s.io/api`'s two `Resource`s), each checked."""
    res = []
    for base in [ROOT] + [ROOT / p for p in PARTS]:
        pd = base / 'Proof'
        if not pd.is_dir():
            continue
        for f in sorted(pd.rglob('*.lean')):
            s = f.read_text()
            for m in AXIOM.finditer(s):
                res.append((m.group(1), base, f.relative_to(pd)))
    return res


def read_list(p):
    out = {}
    if p.exists():
        for line in p.read_text().splitlines():
            line = line.split('#', 1)[0].strip()
            if line:
                parts = line.split()
                out[parts[0]] = parts[1:]
    return out


def go_candidates(stem):
    """`T__M_kv` -> [('T', 'M_kv'), ('T', 'M')]; `F_x` -> [(None, 'F_x'), (None, 'F')]."""
    t, _, m = stem.rpartition('__')
    t = t or None
    out = [(t, m)]
    while '_' in m.strip('_'):
        m = m.rsplit('_', 1)[0]
        out.append((t, m))
    return out


def label(name, base):
    return name if base == ROOT else f'{base.name}:{name}'


def main():
    verbose = '-v' in sys.argv
    src = Sources()
    ax = axioms()
    by_name = {}
    for name, base, rel in ax:
        by_name.setdefault(name, []).append((base, rel))
    pairs = read_list(PAIRS)
    allow, bad = {}, []
    if ALLOW.exists():
        for line in ALLOW.read_text().splitlines():
            entry, _, why = line.partition('#')
            if not entry.strip():
                continue
            words = entry.split()
            locks = [w[5:] for w in words[1:] if w.startswith('lock=')]
            closer = [w[7:] for w in words[1:] if w.startswith('closer=')]
            life = [w[17:] for w in words[1:] if w.startswith('held-for-life-by=')]
            other = [w for w in words[1:] if not w.startswith(('lock=', 'closer=', 'held-for-life-by='))]
            if not locks or len(closer) + len(life) != 1 or other or not why.strip():
                bad.append(f'{ALLOW.name}: `{entry.strip()}` must be `NAME lock=PKG.TYPE.FIELD... '
                           f'(closer=AXIOM | held-for-life-by=PKG.[TYPE.]FUNC)  # why`')
                continue
            allow[words[0]] = (set(locks), closer[0] if closer else None, life[0] if life else None,
                               why.strip())
    # each axiom's Go package, and the source tree it must come from
    missing = []                # the reasons the check cannot run: a tree or package gone
    need = {t: 'always' for t in ALWAYS}
    where = []
    unscanned = {}
    for name, base, rel in ax:
        part = '' if base == ROOT else base.name
        prefer = tuple(PARTS.get(part, ()))
        a = str(rel.parent)
        proj = next((t for pre, t in PROJECTS.get(part, {}).items() if under(a, pre)), None)
        if proj:
            need.setdefault(proj, f'{label(name, base)} ({a})')
            prefer = (proj,) + prefer
        p = src.from_mangled(a, prefer)
        if p is None:
            if proj is not None:
                missing.append(f'no Go source for {label(name, base)}: package {a} not found in '
                               f'project {proj or "(this repository)"}')
            elif any(under(a, t) for t in THIRD_PARTY):
                unscanned.setdefault('no Go source here, third-party: ' + a, []).append(label(name, base))
            elif '_' not in a.split('/', 1)[0] and '.' not in a.split('/', 1)[0]:
                missing.append(f'no Go source for {label(name, base)}: standard-library package {a} '
                               f'not in GOROOT ({src.goroot})')
            else:
                missing.append(f'no Go source for {label(name, base)}: package {a} is neither in a '
                               f'project of PROJECTS nor in THIRD_PARTY')
            continue
        if proj is not None and not src.std(p):
            d = pathlib.Path(src.find_dir(p, prefer)).resolve()
            t = src.trees.get(proj)
            if t is None or not d.is_relative_to(pathlib.Path(t).resolve()):
                missing.append(f'{label(name, base)}: package {p} found in {d}, not in project '
                               f'{proj or "(this repository)"}')
                continue
        where.append((name, base, rel, p, prefer))
    gone = [f'Go source tree {GOOSE / t} is missing or has no go.mod '
            f'({"always needed" if why == "always" else "needed by " + why}; '
            f'`etc/goose.py --project {t}` fetches it)'
            for t, why in sorted(need.items()) if t and not any(tree == t for _, _, tree in src.mods)]
    missing = gone + missing
    if missing:
        for m in missing:
            print(f'reader-slot: {m}', file=sys.stderr)
        print(f'reader-slot: FAILED: {len(missing)} axioms or trees without their Go sources',
              file=sys.stderr)
        return 1
    holders = []
    # each tree separately: a part's packages have the main tree's Go paths (RaftWitness's
    # `go.etcd.io/raft/v3`), which the package cache and the call graph key on
    # (the struct table too: each tree's axioms are matched before the next tree is loaded)
    cur, G_unres = None, set()
    for name, base, rel, p, prefer in sorted(where, key=lambda x: (str(x[1]), x[0], str(x[2]))):
        if base != cur:
            cur = base
            src.pkgs = {}
            STRUCTS.clear()
            holds, releases, fkey, calls, G = analyze(
                src, {(p2, pr2) for _, b2, _, p2, pr2 in where if b2 == base})
            G_unres |= G.unresolved_locks
        lb = label(name, base)
        fn = None
        for t, m in go_candidates(rel.stem):
            k = (p, f'{t}.{m}' if t else m)
            if k in fkey:
                fn = k
                break
            gs = G.methods((p, t), m) if t else []
            if len(gs) == 1:
                # a method promoted from an embedded field (`snapshot.Size`, `*bolt.Tx`'s)
                fn = gs[0].key
                break
        if fn is None:
            unscanned.setdefault('no Go function of the name in ' + p, []).append(lb)
            continue
        if fn not in holds:
            continue
        hl = set(holds[fn])
        locks = ', '.join(sorted(lock_name(x) for x in hl))
        holders.append(lb)

        def closer_ok(closer, need_token):
            """The closer of the same tree (a part's copy pairs with the part's copy): an axiom
            stating its spec, whose Go function releases every lock the holder holds, and (when
            `need_token`) whose post gives a token back."""
            cs = [(cb, crel) for cb, crel in by_name.get(closer, []) if cb == base]
            if not cs:
                return [f'{lb}: its closer {closer} is not an axiom of the same tree']
            out = []
            for cb, crel in cs:
                cl = label(closer, cb)
                if not axiom_states(cb, crel, closer):
                    out.append(f'{lb}: its closer {cl}\'s axiom does not state `{closer}.spec`')
                    continue
                ck = next((k for t, m in go_candidates(crel.stem)
                           for k in [(src.from_mangled(str(crel.parent), prefer), f'{t}.{m}' if t else m)]
                           if k in fkey), None)
                if ck is None:
                    gs = [g for t, m in go_candidates(crel.stem) if t
                          for g in G.methods((src.from_mangled(str(crel.parent), prefer), t), m)]
                    ck = gs[0].key if len(gs) == 1 else None
                if ck is None:
                    out.append(f'{lb}: its closer {cl} maps to no Go function')
                    continue
                miss = hl - releases.get(ck, set())
                if miss:
                    out.append(f'{lb}: its closer {cl} (Go {go_key(ck)}) does not release '
                               f'{", ".join(sorted(lock_name(x) for x in miss))}')
                if need_token:
                    tr = spec_triple(cb / 'Spec' / crel, closer)
                    if isinstance(tr, str):
                        out.append(f'{lb}: its closer {cl}: {tr}')
                    elif not gives_token(tr[1], 'all'):
                        out.append(f'{lb}: its closer {cl} gives no token back (no token conjunct '
                                   f'in its post, after `RET v;`)')
            return out

        if name in allow:
            alocks, acloser, alife, why = allow[name]
            have = {lock_name(x) for x in hl}
            if alocks != have:
                bad.append(f'{lb} holds {locks}, but its allow entry names {", ".join(sorted(alocks))}')
                continue
            if acloser:
                errs = closer_ok(acloser, False)
                if errs:
                    bad += errs
                    continue
                pairing = f'closed by {acloser}'
            else:
                gk = next((k for k in fkey if go_key(k) == alife), None)
                if gk is None:
                    bad.append(f'{lb}: its allow entry\'s goroutine {alife} is no Go function here')
                    continue
                reach = callees(fkey, calls, fn)
                forks = [go_key(k) for k in sorted(reach)
                         for _, g, _, line, _ in calls.get(k, [])
                         if g.key == gk and re.fullmatch(r'\s*go\s*', line)]
                if not forks:
                    bad.append(f'{lb}: its allow entry\'s goroutine {alife} is not started (`go`) by '
                               f'any function {go_key(fn)} reaches')
                    continue
                touch = hl - (set(holds.get(gk, {})) | releases.get(gk, set()))
                if touch:
                    bad.append(f'{lb}: its allow entry\'s goroutine {alife} neither holds nor releases '
                               f'{", ".join(sorted(lock_name(x) for x in touch))}')
                    continue
                pairing = f'held for life by {alife}, started in {forks[0]}'
            print(f'reader-slot: {lb} holds {locks}: allowed, {pairing} ({why[:60]}...)')
            continue
        if not axiom_states(base, rel, name):
            bad.append(f'{lb}: its axiom does not state `{name}.spec`')
            continue
        spec = base / 'Spec' / rel
        tr = spec_triple(spec, name)
        if isinstance(tr, str):
            bad.append(f'{lb} (Go {go_key(fn)}) returns holding a reader slot of {locks}: {tr}')
            continue
        if not gives_token(tr[0], 'any'):
            bad.append(f'{lb} (Go {go_key(fn)}) returns holding a reader slot of {locks}, '
                       f'and its spec\'s pre ({spec.relative_to(ROOT)}) consumes no token')
            continue
        if name not in pairs or not pairs[name]:
            bad.append(f'{lb} holds a reader slot of {locks}: no closer in {PAIRS.relative_to(ROOT)}')
            continue
        errs = closer_ok(pairs[name][0], True)
        bad += errs
        if not errs:
            print(f'reader-slot: {lb} holds {locks}: paid (a token in its pre), closed by '
                  f'{pairs[name][0]} (releases it, a token in its post)')
    hnames = {h.rsplit(':', 1)[-1] for h in holders}
    for k in pairs:
        if k not in hnames:
            print(f'reader-slot: note: {k} is in {PAIRS.name} but is not found to hold a slot')
    if verbose:
        for fname, e in sorted(G_unres):
            print(f'reader-slot: lock with an unresolved owner type: {e} in {fname}')
        for why, names in sorted(unscanned.items()):
            print(f'reader-slot: unscanned ({why}): {" ".join(sorted(names))}')
    for b in bad:
        print(f'reader-slot: {b}', file=sys.stderr)
    nun = sum(len(v) for v in unscanned.values())
    nthird = sum(len(v) for k, v in unscanned.items() if k.startswith('no Go source'))
    nscan = len(ax) - nun
    if bad:
        print(f'reader-slot: FAILED ({len(bad)} of {len(holders)} slot-holding axioms)', file=sys.stderr)
        return 1
    if nscan < MIN_SCANNED:
        print(f'reader-slot: FAILED: {nscan} axioms scanned, below the floor MIN_SCANNED = {MIN_SCANNED} '
              f'(-v lists the unscanned)', file=sys.stderr)
        return 1
    print(f'reader-slot: ok ({len(holders)} slot-holding axioms, each paid and paired, or allowed: '
          f'{" ".join(sorted(holders))}; {len(ax)} axioms in {len({(b, r) for _, b, r in ax})} files: '
          f'{nscan} scanned (floor {MIN_SCANNED}), {nun} unscanned ({nthird} third-party, '
          f'{nun - nthird} with no Go function of the name))')
    return 0


if __name__ == '__main__':
    sys.exit(main())
