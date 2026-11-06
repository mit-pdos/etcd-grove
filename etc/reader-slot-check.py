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
   - a function holds a slot when an `E.RLock()` in it is followed by no `E.RUnlock()` at the same
     or an outer block depth and by no deferred `E.RUnlock()` (an `RUnlock` in an inner block is an
     error path's: `beginTx`'s `if !db.opened { ...RUnlock(); return }`);
   - a function releases one when it has an `E.RUnlock()` with no `E.RLock()` before it
     (`removeTx`), or calls a releaser of the same package (`close`, `Rollback`);
   - a function holds one too when it calls a holder (by name, in its own package or one its file
     imports, resolved by type, below) and keeps what the call returns: the result is returned, discarded, or bound to `v`
     and not passed to a releaser (`v.Rollback()`), a fixed point across packages (`DB.Begin`, and
     through it `backend.Snapshot`).
2. The axioms: every `axiom <F>.wp_proof` under `Proof/` (and a part's `<root>/Proof/`) maps to its
   Go function by the layout (`Spec/<pkg>/<T>__<M>[_variant].lean`). If it is a holder, its spec's
   text (comments stripped) must mention a token (`TOKENS`).
3. The closers: `etc/reader-slot-pairs.txt` lists each holder axiom with its closer axiom; the
   closer's post (its text after `RET`) must mention a token. A holder axiom with no pair fails.
4. Exceptions: `etc/reader-slot-allow.txt`, `NAME  # why`.

Calls are resolved by type, not only by name: a method call's receiver type comes from the
function's receiver, parameters, composite literals (`v := &T{...}`), struct fields (embedded ones
promoted) and the results of resolved calls, so `h.Write(...)` on a `hash.Hash32` is not mvcc's
`store.Write`. A call with a literal `bool` argument is specialised on it: the branches of an
`if p { ... return }` / `if !p { ... }` the argument rules out are skipped (`Begin(true)` takes the
writer's `rwlock`, not a reader slot of `mmaplock`). Unresolved calls are not followed.

Limits (the gate's reach):
- Unscanned axioms (`-v` lists them): 190 of the axioms on 2026-11-06. 164 have no Go source here
  (names-only dependencies), by package: grpc 30 (and credentials/insecure 1, grpclog 1, health 2,
  grpc_health_v1 2, metadata 4, peer 1, status 4), protobuf `proto` 22, zap 21 (zapcore 1),
  prometheus client_golang 7 and grpc_ecosystem's 5, k8s.io/utils clock 7 and trace 2, k8s
  apimachinery/apiserver/api/component-base 29 (apps/v1 2, core/v1 3, errors 2, meta/v1 1,
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
- A name-level check of the sources, not a proof, as `errorf-wrap-check.py` is.

usage: etc/reader-slot-check.py [-v]   (exit 1 on an unpaid holder axiom, a missing pair, or a
                                        closer without the token)
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
        goose = ROOT / '.lake' / 'goose'
        trees = []
        if goose.is_dir():
            for t in sorted(goose.iterdir()):
                if t.is_dir() and t.name not in ('bin', 'perennial') and not t.name.endswith('.proph'):
                    trees.append((t.name, t))
        trees.append(('', ROOT))
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


def lock_facts(f):
    """`f`'s locks held at its return ({field: [positions of the RLocks]}) and its unmatched
    releases, by lock field name."""
    ops = [(m.start(), m.group(1), m.group(2)) for m in LOCKOP.finditer(f.body)]
    if not ops:
        return {}, set()
    dep, dfr = depths(f.body)
    held, rel = {}, set()
    for k, (i, e, op) in enumerate(ops):
        line = f.body[f.body.rfind('\n', 0, i) + 1:i]
        deferred = 'defer' in line or dfr[i]
        field = e.rsplit('.', 1)[-1]
        if op == 'RLock':
            if any(op2 == 'RUnlock' and e2 == e and
                   (dep[j] <= dep[i] or 'defer' in f.body[f.body.rfind('\n', 0, j) + 1:j] or dfr[j])
                   for j, e2, op2 in ops[k + 1:]):
                continue
            if any(op2 == 'RUnlock' and e2 == e and
                   ('defer' in f.body[f.body.rfind('\n', 0, j) + 1:j] or dfr[j])
                   for j, e2, op2 in ops[:k]):
                continue
            held.setdefault(field, []).append(i)
        elif not any(op2 == 'RLock' and e2 == e for j, e2, op2 in ops[:k]) and not deferred:
            rel.add(field)
    return held, rel


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
            am = re.match(r'\s*(\w+)\s*(?:,\s*\w+\s*)*:?=\s*$', line)
            if am and len(gs) == 1:
                t = self.norm(gs[0].rtype, gs[0].pkg, gs[0].imports)
                if t:
                    loc[am.group(1)] = t
        self.locals[id(f)] = out
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


def analyze(src, roots):
    """The holders: {func key: {lock (pkg, field): [positions]}}; the releasers: {key: locks}."""
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
    holds, releases = {}, {}
    for f in funcs:
        h, r = lock_facts(f)
        if h:
            holds[f.key] = {(f.pkg, x): ps for x, ps in h.items()}
        if r:
            releases[f.key] = {(f.pkg, x) for x in r}
    fkey = {f.key: f for f in funcs}
    calls = {f.key: G.calls(f) for f in funcs}

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
                if not gh or re.match(r'\s*defer\b', line):
                    continue
                m = re.match(r'\s*(\w+)\s*(?:,\s*\w+\s*)*:?=\s*$', line)
                for lk in gh:
                    if i in holds.get(f.key, {}).get(lk, []):
                        continue
                    # released by a later resolved call of a releaser of the lock that does not
                    # also hold it (`unsafeCommit` rolls the old read transaction back and begins a
                    # new one: a holder), on the variable the result is bound to if it is bound
                    def releaser(h):
                        return lk in releases.get(h.key, set()) and lk not in holds.get(h.key, {})
                    if m and m.group(1) != '_':
                        v = m.group(1)
                        if any(releaser(h) and (c == v or c.startswith(v + '.'))
                               for j, h, _, _, c in calls[f.key] if j > i):
                            continue
                    elif not re.match(r'\s*return\b', line) and m is None:
                        if any(releaser(h) for j, h, _, _, c in calls[f.key] if j > i):
                            continue
                    holds.setdefault(f.key, {}).setdefault(lk, []).append(i)
                    changed = True
    return holds, releases, fkey, calls, G



# ---------------------------------------------------------------------------------------------
# the axioms

AXIOM = re.compile(r'^axiom\s+([\w\.«»]+)\.wp_proof\b', re.M)


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


def axioms():
    res = {}
    for base in [ROOT] + [ROOT / p for p in PARTS]:
        pd = base / 'Proof'
        if not pd.is_dir():
            continue
        for f in sorted(pd.rglob('*.lean')):
            s = f.read_text()
            for m in AXIOM.finditer(s):
                rel = f.relative_to(pd)
                res[m.group(1)] = (base, rel)
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


def main():
    verbose = '-v' in sys.argv
    src = Sources()
    ax = axioms()
    pairs = read_list(PAIRS)
    allow = {}
    if ALLOW.exists():
        for line in ALLOW.read_text().splitlines():
            name, _, why = line.partition('#')
            if name.strip():
                allow[name.split()[0]] = why.strip()
    # each axiom's Go package
    where = {}
    roots = set()
    for name, (base, rel) in ax.items():
        prefer = tuple(PARTS.get(base.name, ())) if base != ROOT else ()
        a = str(rel.parent)
        p = src.from_mangled(a, prefer)
        where[name] = (base, rel, p, prefer)
        if p:
            roots.add((p, prefer))
    holds, releases, fkey, calls, G = analyze(src, roots)
    bad, holders, unscanned = [], [], {}
    for name, (base, rel, p, prefer) in sorted(ax.items(), key=lambda x: x[0]) if False else sorted(where.items()):
        if not p:
            unscanned.setdefault('no source: ' + str(rel.parent), []).append(name)
            continue
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
            unscanned.setdefault('not found in ' + p, []).append(name)
            continue
        if fn not in holds:
            continue
        locks = ', '.join(sorted(f'{q}.{x}' for q, x in holds[fn]))
        holders.append(name)
        if name in allow:
            print(f'reader-slot: {name} holds {locks}: allowed ({allow[name][:80]}...)')
            continue
        spec = base / 'Spec' / rel
        stext = strip_lean_comments(spec.read_text()) if spec.exists() else ''
        if not TOKENS.search(stext):
            bad.append(f'{name} (Go {fn[0]}.{fn[1]}) returns holding a reader slot of {locks}, '
                       f'and its spec ({spec.relative_to(ROOT)}) takes no token')
            continue
        if name not in pairs or not pairs[name]:
            bad.append(f'{name} holds a reader slot of {locks}: no closer in {PAIRS.relative_to(ROOT)}')
            continue
        closer = pairs[name][0]
        if closer not in ax:
            bad.append(f'{name}: its closer {closer} is not an axiom')
            continue
        cb, crel = ax[closer]
        ctext = strip_lean_comments((cb / 'Spec' / crel).read_text())
        post = ctext.split('RET', 1)[1] if 'RET' in ctext else ''
        if not TOKENS.search(post):
            bad.append(f'{name}: its closer {closer} gives no token back (its post, after RET)')
    for k, v in pairs.items():
        if k not in holders:
            print(f'reader-slot: note: {k} is in {PAIRS.name} but is not found to hold a slot')
    if verbose:
        for why, names in sorted(unscanned.items()):
            print(f'reader-slot: unscanned ({why}): {" ".join(sorted(names))}')
    for b in bad:
        print(f'reader-slot: {b}', file=sys.stderr)
    nun = sum(len(v) for v in unscanned.values())
    if bad:
        print(f'reader-slot: FAILED ({len(bad)} of {len(holders)} slot-holding axioms)', file=sys.stderr)
        return 1
    print(f'reader-slot: ok ({len(holders)} slot-holding axioms, each paid and paired, or allowed: '
          f'{" ".join(sorted(holders))}; {len(ax) - nun} axioms scanned, {nun} unscanned)')
    return 0


if __name__ == '__main__':
    sys.exit(main())
