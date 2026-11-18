#!/usr/bin/env python3
"""Generate a comparator challenge: the trusted part of one theorem, as a Lake package of its own.

  challenge/tools/gen.py NAME THEOREM MODULE [--solution DIR] [--packages-from DIR] [--rounds N]

writes challenge/NAME/ from this repository's checkout DIR (default: the one this script is in),
which must be built (`lake build MODULE`; this script only reads it):

* the repository's modules that declare a constant the comparator compares for THEOREM (declared
  in MODULE): every constant reached from its statement and from the statement of every axiom it
  depends on, through statements, values and inductive types (challenge/tools/Closure.lean), each a
  copy of the module's file with every other declaration removed and the imports of removed
  modules replaced by what those imported; THEOREM's own proof is `sorry`;
* lakefile.toml, lean-toolchain and lake-manifest.json: the repository's toolchain and
  dependencies, at the revisions it pins;
* comparator.json: the comparator's configuration, THEOREM and its axioms, every one of them
  (Lean's, the dependencies', the repository's), permitted;
* AXIOMS.md: those axioms, by where each is declared.

A declaration removed can still be needed to elaborate one kept, not by its term but during
elaboration (an instance found and unfolded away, a name in a context command): gen.py builds the
package (`lake build`; --packages-from DIR copies DIR/.lake/packages first when the package has
none, to reuse built dependencies) and, while it fails with an unknown name or an instance not
found, keeps the declaration that provides it (with everything it reaches) and regenerates, at
most N rounds (default 8). These are listed in comparator-extra.txt (kept, not compared).

challenge/check.sh NAME runs the comparator's check of the result against the repository.
"""
import argparse, json, os, re, shutil, subprocess, sys, collections

HERE = os.path.dirname(os.path.abspath(__file__))
REPO_DIRS = ['Code', 'TrustedCode', 'GeneratedProof', 'ManualProof', 'Spec', 'Proof', 'GooseLang']

ap = argparse.ArgumentParser()
ap.add_argument('name'); ap.add_argument('theorem'); ap.add_argument('module')
ap.add_argument('--solution', default=os.path.dirname(os.path.dirname(HERE)))
ap.add_argument('--packages-from')
ap.add_argument('--rounds', type=int, default=8)
args = ap.parse_args()
SOL = os.path.abspath(args.solution)
OUT = os.path.join(os.path.dirname(HERE), args.name)
WORK = os.path.join(OUT, '.lake', 'gen'); os.makedirs(WORK, exist_ok=True)

def norm(m): return m.replace('«', '').replace('»', '')
def path_of(root, m): return os.path.join(root, norm(m).replace('.', '/') + '.lean')
def is_repo(m): return norm(m).split('.')[0] in REPO_DIRS and os.path.exists(path_of(SOL, m))

# ---------------------------------------------------------------- the analysis (Closure.lean)

def analyze(extra, force_mods):
    src = os.path.join(WORK, 'Closure.lean')
    with open(src, 'w') as f:
        f.write(f'import {args.module}\n' + open(os.path.join(HERE, 'Closure.lean')).read())
    ex = os.path.join(WORK, 'extra.txt')
    open(ex, 'w').write(''.join(n + '\n' for n in sorted(extra)))
    out = os.path.join(WORK, 'closure.txt')
    env = dict(os.environ, THEOREM=args.theorem, OUT=out, REPO=SOL, REPO_DIRS=':'.join(REPO_DIRS),
               EXTRA=ex, FORCE_MODS=','.join(sorted(force_mods)))
    r = subprocess.run(['lake', 'env', 'lean', src], cwd=SOL, env=env, capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit(f'Closure.lean failed:\n{r.stdout[-3000:]}{r.stderr[-3000:]}')
    print(' ', r.stdout.strip().splitlines()[-1].split(': ', 1)[-1])
    axioms = []; decls = collections.defaultdict(list); insts = []; sorries = {args.theorem}
    for l in open(out):
        p = l.split()
        if p[0] == 'AXIOM': axioms.append((p[1], p[2]))
        elif p[0] == 'SORRY': sorries.add(p[1])
        elif p[0] == 'DECL': decls[p[2]].append((p[1] == 'keep', p[3], *map(int, p[4:8])))
        elif p[0] == 'INST': insts.append((p[1], p[2], p[3:]))
        elif p[0] == 'NORANGE': sys.exit(f'no declaration range for {p[1]} ({p[2]})')
    return axioms, decls, insts, sorries

# ---------------------------------------------------------------- trimming

IMPORT = re.compile(r'^((?:public\s+)?(?:meta\s+)?import(?:\s+all)?)\s+(\S+)\s*$')
def header(text):
    """(end offset, [(keyword, module)]) of the header: `module`, comments, imports."""
    off = 0; imps = []; in_c = False; end = 0
    for line in text.split('\n'):
        s = line.strip()
        if in_c:
            if '-/' in s: in_c = False
        elif s.startswith('/-'):
            in_c = '-/' not in s[2:]
        elif s == '' or s.startswith('--') or s == 'module':
            pass
        elif IMPORT.match(s):
            imps.append(IMPORT.match(s).groups()); end = off + len(line) + 1
        else:
            break
        off += len(line) + 1
    return end, imps

_imports = {}
def imports(m):
    if m not in _imports: _imports[m] = header(open(path_of(SOL, m)).read())[1]
    return _imports[m]

def new_imports(m, mods):
    """m's imports, but for a removed repository module what it imported, recursively: the
    environment outside the repository stays the same."""
    res = []; seen = set()
    def go(mm, top):
        for kw, x in imports(mm):
            # the module's own imports as written (`public import X` and `import all X` both);
            # through a removed module, each module once
            key = (kw, norm(x)) if top and (not is_repo(x) or norm(x) in mods) else norm(x)
            if key in seen: continue
            seen.add(key)
            if not is_repo(x) or norm(x) in mods:
                res.append((kw if top else 'public import', x))
            else:
                go(x, False)
    go(m, True)
    return res

# a removed declaration takes its command modifiers with it (`open X in`, `omit h in`, ...)
PREFIX = re.compile(r'^(open|set_option|variable|omit|include|attribute)\b.*\bin\s*$')
# only these are removed; notation, macros, syntax and elaborators stay (later text may use them)
DECL_KW = re.compile(r'(def|theorem|lemma|abbrev|instance|structure|inductive|class|axiom|opaque|'
                     r'coinductive|example)\b')
MODIFIERS = re.compile(r'(private|protected|noncomputable|partial|unsafe|nonrec|public|meta|'
                       r'scoped|local)\b\s*')
def is_decl_command(s):
    s = s.lstrip()
    if s.startswith('/--'):
        e = s.find('-/'); s = s[e + 2:].lstrip() if e >= 0 else s
    while s.startswith('@['):
        d = 0
        for i, c in enumerate(s):
            if c == '[': d += 1
            elif c == ']':
                d -= 1
                if d == 0: s = s[i + 1:].lstrip(); break
        else: return False
    while MODIFIERS.match(s): s = s[MODIFIERS.match(s).end():]
    return bool(DECL_KW.match(s))

CMD0 = re.compile(r'^(example|#print|#check|#eval|#guard_msgs|#guard|#exit|#lint)\b')
def drop_leftovers(text):
    """`example`s and `#print`/`#check`/`#eval`: each up to the next line at column 0."""
    out = []; skipping = False
    for line in text.split('\n'):
        if line and not line[0].isspace(): skipping = bool(CMD0.match(line))
        if not skipping: out.append(line)
    return '\n'.join(out)

ATTR = re.compile(r'^((?:local\s+|scoped\s+)?attribute\s*\[[^\]]*\])(.*)$', re.S)
def filter_attributes(text, kept_sfx, dropped_sfx):
    """`attribute [a] x y ...` commands (not `... in`): without the names of removed declarations
    (a name of no kept declaration that is a removed one's); the command goes when none is left."""
    out = []; lines = text.split('\n'); i = 0
    while i < len(lines):
        m = ATTR.match(lines[i])
        if not m or re.search(r'\bin\s*$', lines[i]):
            out.append(lines[i]); i += 1; continue
        j = i + 1
        while j < len(lines) and lines[j].startswith((' ', '\t')) and lines[j].strip(): j += 1
        cmd = ATTR.match('\n'.join(lines[i:j]))
        names = cmd.group(2).split()
        left = [x for x in names
                if x.removeprefix('_root_.') in kept_sfx or x.removeprefix('_root_.') not in dropped_sfx]
        if left == names: out.extend(lines[i:j])
        elif left: out.append(cmd.group(1) + ' ' + ' '.join(left))
        i = j
    return '\n'.join(out)

def sorry_body(decl):
    """`decl` with what follows its first `:=` outside brackets replaced by `sorry`."""
    d = 0; i = 0
    while i < len(decl) - 1:
        c = decl[i]
        if decl.startswith('--', i): i = decl.find('\n', i); i = len(decl) if i < 0 else i; continue
        if decl.startswith('/-', i): i = decl.find('-/', i) + 2; continue
        if c in '([{⟨': d += 1
        elif c in ')]}⟩': d -= 1
        elif d == 0 and decl.startswith(':=', i): return decl[:i] + ':=\n  sorry'
        elif d == 0 and re.match(r'\bwhere\b', decl[i:]) and (i == 0 or not decl[i - 1].isalnum()):
            return decl[:i].rstrip() + ' :=\n  sorry'
        i += 1
    return None

def trim(decls, sorries, force_mods, noopen=frozenset()):
    """Write the trimmed modules; `sorries`: kept declarations whose proof becomes `sorry` (the
    theorem, and proofs reached only for elaboration); `force_mods`: modules kept even with no
    declaration kept (what they register: an attribute, a simp set)."""
    mods = {norm(m) for m, ds in decls.items() if any(k for k, *_ in ds)} | force_mods
    for d in REPO_DIRS: shutil.rmtree(os.path.join(OUT, d), ignore_errors=True)
    def suffixes(ns):
        out = set()
        for n in ns:
            parts = n.split('.')
            out |= {'.'.join(parts[i:]) for i in range(len(parts))}
        return out
    kept_sfx = suffixes(n for ds in decls.values() for k, n, *_ in ds if k)
    dropped_sfx = suffixes(n for ds in decls.values() for k, n, *_ in ds if not k)
    kept_names = [n for ds in decls.values() for k, n, *_ in ds if k]
    noopen = {x for x in noopen if not any(('.' + x + '.') in ('.' + n) for n in kept_names)}
    allmods = {norm(m): m for m in decls}
    for fm in force_mods: allmods.setdefault(fm, fm)
    for nm in sorted(mods):
        m = allmods[nm]
        text = open(path_of(SOL, m)).read()
        st = [0] + [i + 1 for i, c in enumerate(text) if c == '\n']
        def off(l, c): return st[l - 1] + c
        keep = [(off(sl, sc), off(el, ec)) for k, _, sl, sc, el, ec in decls[m] if k]
        drop = []
        sorry_ranges = []; thm_range = None
        for k, n, sl, sc, el, ec in decls[m]:
            a, b = off(sl, sc), off(el, ec)
            if k and n in sorries: sorry_ranges.append((a, b))
            if n == args.theorem: thm_range = (a, b)
            if k or not is_decl_command(text[a:b]): continue
            if any(not (b <= ka or kb <= a) for ka, kb in keep): continue
            while sc == 0 and sl > 1 and PREFIX.match(text[st[sl - 2]:st[sl - 1]].rstrip('\n')):
                sl -= 1; a = st[sl - 1]
            drop.append((a, b))
        drop.sort(); merged = []
        for a, b in drop:
            if merged and a <= merged[-1][1]: merged[-1] = (merged[-1][0], max(b, merged[-1][1]))
            else: merged.append((a, b))
        hend, _ = header(text)
        body = []; pos = hend
        for a, b in merged:
            if a < hend: continue
            body.append(text[pos:a])
            pos = b
            while pos < len(text) and text[pos] in ' \t': pos += 1
            if pos < len(text) and text[pos] == '\n': pos += 1
        body.append(text[pos:])
        body = ''.join(body)
        for a, b in sorry_ranges:  # the statement, its proof `sorry`
            t = text[a:b]; s = sorry_body(t)
            if s is None or body.count(t) != 1:
                if (a, b) == thm_range:
                    sys.exit('the theorem: no `:=`, or not once in its trimmed module')
                continue  # an elaboration-only proof left whole
            body = body.replace(t, s)
        body = re.sub(r'(?m)^mutual\s*\nend[ \t]*$\n?', '', body)  # every declaration removed
        if noopen:  # namespaces left with no declaration (still none kept): out of `open` lines
            def fix_open(mo):
                ws = [w for w in mo.group(1).split() if w not in noopen]
                return 'open ' + ' '.join(ws) + (mo.group(2) or '') if ws else ''
            body = re.sub(r'(?m)^open ([^\n]*?)(\s+in)?$', fix_open, body)
        body = re.sub(r'\n{3,}', '\n\n', filter_attributes(drop_leftovers(body), kept_sfx, dropped_sfx))
        pre = [l for l in text[:hend].split('\n') if not IMPORT.match(l.strip())]
        while pre and pre[-1].strip() == '': pre.pop()
        imps = '\n'.join(f'{kw} {x}' for kw, x in new_imports(m, mods))
        dst = path_of(OUT, m)
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        open(dst, 'w').write('\n'.join(pre) + '\n\n' + imps + '\n' + body)
    return mods

# ---------------------------------------------------------------- the package's other files

def package_files(axioms, mods, extra, force_mods, noopen):
    tops = sorted({m.split('.')[0] for m in mods})
    rev = next(p['rev'] for p in json.load(open(os.path.join(SOL, 'lake-manifest.json')))['packages']
               if p['name'] == 'perennial')
    with open(os.path.join(OUT, 'lakefile.toml'), 'w') as f:
        f.write(f'''name = "{args.name}Challenge"
defaultTargets = ["Challenge"]

# Generated by challenge/tools/gen.py (README.md): the trusted part of `{args.theorem}`.
# The repository's Perennial (its lakefile.toml), and its dependencies at the repository's revisions
# (lake-manifest.json).
[[require]]
name = "perennial"
git = "https://github.com/mit-pdos/perennial"
rev = "{rev}"

[[lean_lib]]
name = "Challenge"
globs = ["Challenge", {", ".join(f'"{t}.+"' for t in tops)}]

[leanOptions]
linter.unusedSectionVars = false
''')
    shutil.copy(os.path.join(SOL, 'lean-toolchain'), OUT)
    man = json.load(open(os.path.join(SOL, 'lake-manifest.json')))
    man['name'] = f'{args.name}Challenge'
    json.dump(man, open(os.path.join(OUT, 'lake-manifest.json'), 'w'), indent=1)
    open(os.path.join(OUT, 'lake-manifest.json'), 'a').write('\n')
    # the challenge's root: the theorem's module and every module of this directory that declares
    # one of its axioms (the statement does not import them all; the solution's proof does)
    axmods = sorted({m for _, m in axioms if is_repo(m)})
    with open(os.path.join(OUT, 'Challenge.lean'), 'w') as f:
        f.write(f'/- The challenge\'s root (generated by challenge/tools/gen.py): `{args.theorem}` and '
                f'every axiom it depends on that this directory declares. -/\nmodule\n\n'
                + ''.join(f'public import {m}\n' for m in [args.module] + axmods))
    names = sorted(a for a, _ in axioms)
    json.dump({'challenge_module': 'Challenge', 'solution_module': args.module,
               'theorem_names': [args.theorem], 'permitted_axioms': names},
              open(os.path.join(OUT, 'comparator.json'), 'w'), indent=1)
    open(os.path.join(OUT, 'comparator-extra.txt'), 'w').write(
        '# Kept for elaboration only (challenge/tools/gen.py), not compared: declarations (with\n'
        '# what they reach, proofs `sorry`) and, `module M`, modules kept for what they register.\n'
        + ''.join(n + '\n' for n in sorted(extra))
        + ''.join(f'module {m}\n' for m in sorted(force_mods))
        + ''.join(f'noopen {x}\n' for x in sorted(noopen)))
    by = collections.defaultdict(list)
    for a, m in axioms:
        by[m].append(a)
    lean = [m for m in by if m.split('.')[0] in ('Init', 'Std', 'Lean')]
    repo = [m for m in by if is_repo(m)]
    dep = [m for m in by if m not in lean and m not in repo]
    with open(os.path.join(OUT, 'AXIOMS.md'), 'w') as f:
        f.write(f'# The axioms of `{args.theorem}`\n\n'
                f'Every axiom the theorem depends on ({len(axioms)}), all of them the permitted axioms '
                f'of comparator.json (generated by challenge/tools/gen.py).\n\n')
        for title, ms in (("Lean's", lean), (f'Declared in this directory ({sum(len(by[m]) for m in repo)})', repo),
                          (f"Declared by the dependencies, at lakefile.toml's revisions ({sum(len(by[m]) for m in dep)})", dep)):
            f.write(f'## {title}\n\n')
            for m in sorted(ms):
                f.write(f'### `{m}` ({len(by[m])})\n\n' + ''.join(f'- `{a}`\n' for a in sorted(by[m])) + '\n')

# ---------------------------------------------------------------- build, and what it lacks

ERR = re.compile(r'^error: ([^:]+\.lean):(\d+):(\d+): (.*)$')
def build():
    if not os.path.isdir(os.path.join(OUT, '.lake', 'packages')) and args.packages_from:
        print('  copying', os.path.join(args.packages_from, '.lake', 'packages'))
        shutil.copytree(os.path.join(args.packages_from, '.lake', 'packages'),
                        os.path.join(OUT, '.lake', 'packages'), symlinks=True)
    r = subprocess.run(['lake', 'build', 'Challenge'], cwd=OUT, capture_output=True, text=True)
    log = r.stdout + r.stderr
    open(os.path.join(WORK, 'build.log'), 'w').write(log)
    errs = []; lines = log.split('\n')
    for i, l in enumerate(lines):
        mm = ERR.match(l)
        if mm:
            msg = mm.group(4); j = i + 1
            while j < len(lines) and lines[j].startswith('  '): msg += '\n' + lines[j]; j += 1
            errs.append((mm.group(1), msg))
    return r.returncode == 0, errs

IDENT = re.compile(r"[A-Za-z_«][\w.'«»!?]*")
def wanted(errs, decls, insts):
    """The dropped declarations the build's errors ask for."""
    dropped = {n for ds in decls.values() for k, n, *_ in ds if not k}
    kept = {n for ds in decls.values() for k, n, *_ in ds if k}
    by_suffix = collections.defaultdict(set)
    for n in dropped:
        parts = n.split('.')
        for i in range(len(parts)): by_suffix['.'.join(parts[i:])].add(n)
    want = set(); unresolved = []
    # a namespace of removed declarations only: `open` it no more (the failed `open` opened
    # nothing, so the file's other errors follow from it: this round, only these)
    ns = {re.match(r'unknown namespace `([^`]+)`', msg).group(1) for f, msg in errs
          if re.match(r'unknown namespace `', msg)}
    if ns: return {'noopen ' + x for x in ns}, []
    for f, msg in errs:
        m = (re.match(r'Unknown (?:constant|identifier) `([^`]+)`', msg)
             # a removed name used as a function in a binder is auto-bound, then applied
             or re.match(r'Function expected at\n\s+([A-Za-z_][\w.\']*)\s*$', msg)
             # ... or as a type, then a `.ctor` of it is looked up
             or re.match(r'Invalid dotted identifier notation: The expected type of `[^`]+`\n\s+'
                         r'([A-Za-z_][\w.\']*)\s*$', msg))
        if m:
            x = m.group(1).removeprefix('_root_.')
            # not declared in a module the challenge has: Closure.lean resolves it by suffix
            want |= by_suffix.get(x) or {x}
            continue
        m = re.match(r'failed to synthesize(?: instance of type class)?\n\s+(.*)', msg)
        if m:
            toks = IDENT.findall(m.group(1))
            if not toks: unresolved.append((f, msg)); continue
            cls, rest = toks[0].split('.')[-1], toks[1:]
            # a goal with no named argument says too little (every instance of the class would do)
            if not rest: unresolved.append((f, msg)); continue
            hit = [i for i, c, a in insts if i not in kept and c.split('.')[-1] == cls
                   and all(any(x == t or x.endswith('.' + t) for x in a) for t in rest)]
            if not hit:
                # a dependency's instance for a type former (`TypedPointsto (Pointer T)`) needing one
                # for an argument of the repository's: instances declared in an argument type's
                # namespace (Goose's `T.T_typed_pointsto`), of the same class if any
                for t in reversed(rest):
                    ns = {x for _, _, a in insts for x in a if x == t or x.endswith('.' + t)}
                    cand = [(i, c) for i, c, _ in insts if i not in kept
                            and any(i.startswith(x + '.') for x in ns)]
                    hit = [i for i, c in cand if c.split('.')[-1] == cls] or [i for i, _ in cand]
                    if hit: break
            if hit: want |= set(hit)
            else: unresolved.append((f, msg))
            continue
        m = re.match(r'Unknown attribute `\[([^\]\s]+)', msg)
        if m:  # registered by a module none of whose declarations is kept: keep the module
            reg = registrar(m.group(1))
            if reg: want.add('module ' + reg)
            else: unresolved.append((f, msg))
            continue
        if 'bad import' in msg or 'has metavariables' in msg: continue
        unresolved.append((f, msg))
    return want, unresolved

REGISTER = r'^\s*(?:register_\w+|declare_\w+)\s+{}\b'
def registrar(attr):
    """The repository module that registers attribute `attr` (`register_simp_attr attr`, ...)."""
    pat = re.compile(REGISTER.format(re.escape(attr)), re.M)
    for d in REPO_DIRS:
        for root, _, files in os.walk(os.path.join(SOL, d)):
            for fn in files:
                if fn.endswith('.lean'):
                    fp = os.path.join(root, fn)
                    if pat.search(open(fp, errors='replace').read()):
                        return os.path.relpath(fp, SOL)[:-5].replace('/', '.')
    return None

extra = set()
p = os.path.join(OUT, 'comparator-extra.txt')
if os.path.exists(p):
    extra = {l.strip() for l in open(p) if l.strip() and not l.startswith('#')}
for rnd in range(1, args.rounds + 1):
    force_mods = {x.split()[1] for x in extra if x.startswith('module ')}
    noopen = {x.split()[1] for x in extra if x.startswith('noopen ')}
    names = {x for x in extra if ' ' not in x}
    print(f'round {rnd}: {len(names)} declarations and {len(force_mods)} modules kept for elaboration')
    axioms, decls, insts, sorries = analyze(names, force_mods)
    mods = trim(decls, sorries, force_mods, noopen)
    package_files(axioms, mods, names, force_mods, noopen)
    ok, errs = build()
    if ok:
        print(f'built: {len(mods)} modules, {len(axioms)} axioms; challenge/{args.name}')
        sys.exit(0)
    want, unresolved = wanted(errs, decls, insts)
    print(f'  {len(errs)} errors: {len(want - extra)} declarations to keep, {len(unresolved)} not understood')
    for f, msg in unresolved[:20]: print(f'    {f}: {msg.splitlines()[0][:160]}')
    if not want - extra:
        sys.exit('the build fails and no removed declaration would help (.lake/gen/build.log)')
    extra |= want
sys.exit(f'still failing after {args.rounds} rounds (.lake/gen/build.log)')
