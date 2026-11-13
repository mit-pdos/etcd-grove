#!/usr/bin/env python3
"""Generate the part `LinuxFs/`'s copies of main-tree modules (`notes/wal-fsext-plan.md`, §8, "part copies").

A module of the part that imports the part's own translations (its `os`, `io/fs`, raft's root package,
`walpb`, ...) cannot import a main module that reaches the main tree's translations of the same packages:
both declare the same names. The real WAL's proofs live in the part and are stated in the main tree's
WAL vocabulary (`WalHist`, `WalEncRecs`, `WalEncFold`, `WalReadAllPost`, the abstract disk `AbsDisk`, ...),
which reaches the main raft root (`StorContents.base : entryID`). So the part gets copies of those
modules, at `LinuxFs/<path>`, declaring the same names (nothing outside the part imports them), generated
here from the main modules so that no copy is kept by hand. They go when the part's `os` becomes the main
tree's (the `os` promotion dissolves the part).

Two kinds of copy (`COPIES`):

- `Whole(path)`: the module word for word, but its imports: an import of a copied module or of a module
  the part translates itself (`LinuxFs/{Code,GeneratedProof,TrustedCode,ManualProof}/...`) points to
  the part's (`LinuxFs.<module>`); `drop` removes imports, `add` adds part imports after the rest.
- `Extract(path, names, ...)`: the named top-level declarations of a module that mixes them with heavy
  imports (the raft vocabulary in `NodeApiVocab`, `CommitWit`, the server's `WalRecs`), verbatim (with
  their docstrings and attributes), in a frame of the given imports, `open`s and `variable`s. A main-tree
  split would rebuild thousands of modules (`etc/importers.py --count`); an extract rebuilds none.

Each copy starts with a comment saying it is generated and from what. The script also checks that no
copy's main-tree import reaches, directly or not, a main module the part declares again (a module `X`
with a `LinuxFs/X.lean`): that would be the clash the copies are for.

  etc/gen-part-copies.py            regenerate every copy
  etc/gen-part-copies.py --check    exit 1 if a copy differs from what would be generated (or clashes)
"""
import os, re, sys, textwrap

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(ROOT)
PART = 'LinuxFs'
# the part's own translations: an import of the main module of the same name goes to the part's
PART_TRANSLATED = ('Code.', 'GeneratedProof.', 'TrustedCode.', 'ManualProof.')


class Whole:
    def __init__(self, path, drop=(), add=()):
        self.path, self.drop, self.add = path, list(drop), list(add)


class Extract:
    def __init__(self, path, names, imports, opens, variables=('variable [GooseExts]',), options=()):
        self.path, self.names, self.imports = path, list(names), list(imports)
        self.opens, self.variables, self.options = list(opens), list(variables), list(options)


STOR = 'Proof/go_etcd_io/etcd/server/v3/storage/'
COPIES = [
    # raft's protobuf records (`EntryM`, `HardStateM`, ...): over raftpb, but the module imports the raft root
    Whole('Proof/go_etcd_io/raft/v3/PbModel.lean'),
    # the storage contents the WAL's records are (`StorContents`, its base an `entryID`)
    Extract('Proof/go_etcd_io/raft/v3/NodeApiVocab.lean',
            ['StorContents', 'StorContents.b', 'StorContents.last', 'StorContents.commit'],
            imports=['Proof.go_etcd_io.raft.v3.PbModel'], opens=['Iris Iris.BI go_etcd_io.raft.v3']),
    # a `Save`'s hard state (`phsNext`, `hsZero`)
    Extract('Proof/go_etcd_io/raft/v3/Protocol/CommitWit.lean',
            ['hardStateM_countable', 'hsZero', 'phsNext', 'phsNext_empty', 'phsNext_ne', 'phsNext_zero'],
            imports=['Proof.go_etcd_io.raft.v3.PbModel'], opens=['Iris Iris.BI GMap go_etcd_io.raft.v3'],
            options=['set_option autoImplicit false']),
    # the WAL records' pure model (the rest of `WalRecs` is the server's ghost state and trust boundary)
    Extract(STOR + 'WalRecs.lean',
            ['walFresh', 'walSaveSnap', 'walSaveSnap_base_ge'],
            imports=['Proof.go_etcd_io.raft.v3.NodeApiVocab', 'Proof.go_etcd_io.raft.v3.Protocol.CommitWit'],
            opens=['Iris Iris.BI go_etcd_io.raft.v3']),
    # the abstract disk (its histories, states and ghost state, which the W1 layer reuses)
    Whole('GooseLang/Ext/AbsDisk/Impl.lean'),
    Whole('GooseLang/Ext/AbsDisk/Specs.lean'),
    # the WAL vocabulary and the encoding/fold layer over it
    Whole(STOR + 'WalHist.lean'),
    Whole(STOR + 'WalDisk.lean'),
    Whole(STOR + 'WalHistLemmas.lean'),
    Whole(STOR + 'WalViews.lean'),
    Whole(STOR + 'WalEncRecs.lean'),
    Whole(STOR + 'WalEncSegs.lean'),
    Whole(STOR + 'WalEncSegsImg.lean'),
    Whole(STOR + 'WalEncSuffix.lean'),
    Whole(STOR + 'WalEncFold.lean'),
    Whole(STOR + 'WalReadAllPost.lean'),
    # the generic protobuf vocabulary, without raft's `Base` (the main raft root), and the specs and
    # trust-boundary axioms of `proto.Size`/`Marshal`/`Unmarshal` over it and the part's `proto` instance
    # (`LinuxFs/Proof/google_golang_org/protobuf/proto/PkgInit.lean`, hand-written)
    Whole('Proof/google_golang_org/protobuf/proto/InvProto.lean', drop=['Proof.go_etcd_io.raft.v3.Base']),
    Whole('Spec/google_golang_org/protobuf/proto/SizePb.lean',
          add=['LinuxFs.Proof.google_golang_org.protobuf.proto.PkgInit']),
    Whole('Spec/google_golang_org/protobuf/proto/MarshalPb.lean',
          add=['LinuxFs.Proof.google_golang_org.protobuf.proto.PkgInit']),
    Whole('Spec/google_golang_org/protobuf/proto/UnmarshalPb.lean',
          add=['LinuxFs.Proof.google_golang_org.protobuf.proto.PkgInit']),
    Whole('Proof/google_golang_org/protobuf/proto/SizePb.lean'),
    Whole('Proof/google_golang_org/protobuf/proto/MarshalPb.lean'),
    Whole('Proof/google_golang_org/protobuf/proto/UnmarshalPb.lean'),
    # `time.Duration.Seconds`'s spec (the WAL encoder's `write` observes a duration; its main module
    # imports the server's `BaseApply` for nothing but the frame)
    Whole('Spec/time/Duration__Seconds.lean',
          drop=['Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply'], add=['Perennial.Proof.time']),
    # its pointer-receiver form (`sync`'s `took.Seconds()` on an addressable `took`)
    Whole('Spec/time/Duration__Seconds_ptr.lean',
          drop=['Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply'], add=['Perennial.Proof.time']),
    # zap's trust-boundary specs the WAL's logging calls need (`sync`'s slow-fdatasync warning, `Create`'s
    # warnings): their main modules import the cache's `Base` for its package-initialization instances,
    # which the part gives in `wal/DepsPkgInit.lean`
] + [
    Whole(f'Spec/go_uber_org/zap/{n}.lean', drop=['Proof.go_etcd_io.etcd.cache.v3.Base'],
          add=['LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.DepsPkgInit'])
    for n in ['Logger__Warn', 'Duration', 'String', 'Error', 'Int64']
]

IMPORT_RE = re.compile(r'^((?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?)(\S+)(.*)$')


def mod_of(path):
    return path[:-len('.lean')].replace('/', '.')


def path_of(mod):
    return mod.replace('.', '/') + '.lean'


COPIED = {mod_of(c.path) for c in COPIES}


def target(mod):
    """Where a copy's import of the main module `mod` points."""
    if mod in COPIED:
        return PART + '.' + mod
    if mod.startswith(PART_TRANSLATED) and os.path.exists(os.path.join(PART, path_of(mod))):
        return PART + '.' + mod
    return mod


def header(c, kind):
    text = (f'GENERATED by `etc/gen-part-copies.py` from `{c.path}`: do not edit, regenerate '
            f'(`--check` compares). {kind} for the part `{PART}/`, which cannot import the original (it '
            'reaches the main tree\'s translations of packages the part translates itself); the same '
            'names. Goes with the `os` promotion (`notes/wal-fsext-plan.md`, §8, "part copies").')
    return '/-\n' + textwrap.fill(text, 100, break_on_hyphens=False) + '\n-/\n'


def gen_whole(c):
    src = open(c.path).read().split('\n')
    out, last_import = [], None
    for line in src:
        m = IMPORT_RE.match(line)
        if m and m.group(2) in c.drop:
            last_import = len(out) - 1  # an added import may take a dropped one's place
            continue
        if m:
            line = m.group(1) + target(m.group(2)) + m.group(3)
            last_import = len(out)
        out.append(line)
    missing = [d for d in c.drop if not any(IMPORT_RE.match(l) and IMPORT_RE.match(l).group(2) == d for l in src)]
    if missing:
        sys.exit(f'{c.path}: no import of {missing} to drop')
    if c.add:
        if last_import is None:
            sys.exit(f'{c.path}: no import to add after')
        out[last_import + 1:last_import + 1] = ['public import ' + a for a in c.add]
    kind = 'A copy, word for word but its imports,'
    if c.drop or c.add:
        kind = 'A copy, word for word but its imports (dropped: ' + (', '.join(c.drop) or 'none') + \
            '; added: ' + (', '.join(c.add) or 'none') + '),'
    return header(c, kind) + '\n'.join(out)


def chunks(lines):
    """Split the lines after the module's imports into top-level commands: a command starts at a line
    at column 0 outside a block comment; a docstring or an attribute line joins the command after it."""
    raw, depth, cur = [], 0, None
    for line in lines:
        starts = depth == 0 and line[:1] not in ('', ' ', '\t')
        if starts:
            if cur is not None:
                raw.append(cur)
            cur = [line]
        elif cur is not None:
            cur.append(line)
        depth += len(re.findall(r'/-', line)) - len(re.findall(r'-/', line))
    if cur is not None:
        raw.append(cur)
    merged, pend = [], []
    for ch in raw:
        if ch[0].startswith('/--') or re.match(r'^@\[[^\]]*\]\s*$', ch[0]):
            pend += ch
            continue
        merged.append(pend + ch)
        pend = []
    return merged


DECL_RE = re.compile(r'^(?:@\[[^\]]*\]\s*)*(?:(?:noncomputable|private|protected|partial|unsafe)\s+)*'
                     r'(def|theorem|lemma|abbrev|instance|structure|inductive|class|opaque|axiom)\s+([^\s:({\[]+)')


def decl_name(ch):
    i = 0
    if ch[0].startswith('/--'):
        depth = 0
        while True:
            depth += len(re.findall(r'/-', ch[i])) - len(re.findall(r'-/', ch[i]))
            i += 1
            if depth <= 0:
                break
    text = ' '.join(l.strip() for l in ch[i:i + 3])
    m = DECL_RE.match(text)
    return m.group(2) if m else None


def gen_extract(c):
    src = open(c.path).read().split('\n')
    try:
        start = next(i for i, l in enumerate(src) if l.startswith('@[expose] public section')) + 1
    except StopIteration:
        sys.exit(f'{c.path}: no `@[expose] public section`')
    found = {}
    order = {}
    for k, ch in enumerate(chunks(src[start:])):
        n = decl_name(ch)
        order[n] = k
        if n in c.names:
            if n in found:
                sys.exit(f'{c.path}: `{n}` declared twice')
            while ch and ch[-1].strip() == '':
                ch = ch[:-1]
            found[n] = ch
    missing = [n for n in c.names if n not in found]
    if missing:
        sys.exit(f'{c.path}: declarations not found: {missing}')
    out = ['module', '']
    out += ['public import ' + target(i) for i in c.imports]
    out += ['', '@[expose] public section', '']
    out += c.options + ([''] if c.options else [])
    out += ['noncomputable section', '', 'namespace Perennial', 'namespace EtcdGrove', '']
    out += ['open ' + o for o in c.opens] + ['']
    out += ['section extract'] + list(c.variables) + ['']
    # in the source's order
    for n in sorted(found, key=lambda n: order[n]):
        out += found[n] + ['']
    out += ['end extract', '', 'end EtcdGrove', 'end Perennial', '']
    kind = 'An extract (the declarations ' + ', '.join(f'`{n}`' for n in c.names) + \
        ', verbatim, in a frame of the part\'s imports),'
    return header(c, kind) + '\n'.join(out)


def generate():
    files = {}
    for c in COPIES:
        files[os.path.join(PART, c.path)] = gen_whole(c) if isinstance(c, Whole) else gen_extract(c)
    return files


def check_clash(files):
    """No copy's main-tree import reaches a main module the part declares again."""
    imp = {}

    def imports(mod):
        if mod not in imp:
            p = path_of(mod)
            imp[mod] = [m.group(2) for l in open(p) for m in [IMPORT_RE.match(l)] if m] \
                if os.path.exists(p) else []
        return imp[mod]

    def redeclared(mod):
        return os.path.exists(path_of(mod)) and os.path.exists(os.path.join(PART, path_of(mod)))
    bad_memo = {}

    def reach(mod):
        if mod not in bad_memo:
            bad_memo[mod] = None
            if redeclared(mod):
                bad_memo[mod] = [mod]
            else:
                for d in imports(mod):
                    r = reach(d)
                    if r:
                        bad_memo[mod] = [mod] + r
                        break
        return bad_memo[mod]
    errs = []
    for f, text in files.items():
        for l in text.split('\n'):
            m = IMPORT_RE.match(l)
            if m and not m.group(2).startswith(PART + '.'):
                r = reach(m.group(2))
                if r:
                    errs.append(f'{f}: imports {" <- ".join(reversed(r))}')
    return errs


def main(argv):
    check = '--check' in argv
    files = generate()
    errs = check_clash(files)
    for e in errs:
        print('clash:', e, file=sys.stderr)
    differ = []
    for f, text in files.items():
        old = open(f).read() if os.path.exists(f) else None
        if old != text:
            differ.append(f)
            if not check:
                os.makedirs(os.path.dirname(f), exist_ok=True)
                with open(f, 'w') as h:
                    h.write(text)
    if check:
        for f in differ:
            print('differs:', f, file=sys.stderr)
        sys.exit(1 if differ or errs else 0)
    for f in differ:
        print('wrote', f)
    sys.exit(1 if errs else 0)


if __name__ == '__main__':
    main(sys.argv[1:])
