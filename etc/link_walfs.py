"""`etc/gen-link.py --walfs`: Proof/go_etcd_io/etcd/server/v3/storage/wal/Link.lean, etcd's
real WAL over the per-byte Linux file extension (`notes/wal-fsext-plan.md`, section 8, "Links"),
every proof applied to its callees' results.

As `--bbolt` (`etc/link_bbolt.py`, whose scanner this reuses), the callees are read off each proof's
binders, not from a list: the WAL's proofs are many, several prove a second spec of a function
(`WAL.sync.specC`, `os.File.Truncate.specWalTail`: the theorem's conclusion says which), and the
binders are the one record of what each proof takes. Unlike bbolt's, the WAL's specs are stated
over **model parameters** (`(P : WalPbIn GF)`, the client's protobuf model; `(Mr : WalMarshal)`, the
records' encoding; `C`, `U`, `HsO`): a spec is `<T>.<M>.spec<S> (W := W) P Mr`, so a result is
generic in them and a callee's are instantiated from the caller's binder.

The rules:

- **The results.** Every `theorem`/`axiom` of the proofs under `PROOF_DIRS` whose conclusion
  is a spec applied to arguments (`<T>.<M>.spec<S> (W := W) a ...`), and whose explicit binders are
  all callee specs, model parameters (`PARAMS`) or premises (`PREMISES`), proves that spec (a
  proof generic in more, as `wp_core`'s `(h : WalHS)`, is a lemma of another proof). A spec proved
  twice is linked once: by the theorem named `<T>.<M>.wp_proof<S>` if there is one, else by the one
  with the fewest binders. The roots are the proofs of `ROOT_DIRS` (the WAL, `walpb`, `fileutil`);
  the results their binders reach are linked too, whatever their package (`os`, `syscall`,
  `ioutil`, `crc`, ...: the part's proofs, the result's name says the package).
- **A result** `<T>.wp_<M><S>` (namespace `EtcdGrove.walfs`) takes the proof's model parameters
  (same names, same order), then those of its callees (transitively) that their conclusions do not
  mention and the proof has not (`ValidSnapshotEntries`' `P U HsO`, from `validSnapshotEntries.specPinned`), then one hypothesis `h_<name>` for each spec with no proof and each
  premise its proof or a callee's (transitively) takes, and states the proof's conclusion. The
  results with a hypothesis are in `section links_pending` (`etc/proof_roots.py`'s pending roots).
- **The callees** are the proof's explicit binders, in order: a spec with a result is given it, its
  model parameters matched against the binder's arguments (a parameter the callee's conclusion
  does not mention is the caller's of the same name); Perennial's linked results
  (`Perennial/Proof/<pkg>/Link.lean`) are used as they are; a spec with no proof is a hypothesis.
- **Premises** (`PREMISES`: the laws of the client's protobuf model `P`, the decoder's environment
  supply) are hypotheses: they are facts about the parameters, which the WAL's client discharges.
- Instance binders (the packages' `Assumptions`) are section
  variables, collected from the linked proofs' own and their modules' `variable` lines.

A binder of a kind none of these covers makes the theorem a lemma, not a result; a root proof with
one is reported on stderr. `--check` compares the output with the committed file.

`etc/gen-link.py --durable` is the same generator over `examples/lib/durable`'s proofs in the part
`WalTester/` (`DURABLE`: its roots, output, namespace `EtcdGrove.durable`, no `WalGS`), W4c U2. (Until
2026-11-15 the WAL and the durable library were in the part `LinuxFs/`, whose own copies of specs took
precedence over the main tree's; the WAL is the main tree's now: notes/wal-lean-integration.md.)

`etc/gen-link.py --wal-tester` (`TESTER`, W4c U5): the WAL tester's proofs (`examples/etcd/wal`), whose
callees include the WAL's and `durable`'s specs. Those are given their **linked results as they are**
(the theorems of `EXT_LINKS`, preferred over any other proof of the spec, not re-emitted): each is
applied to its own binders in order, its hypotheses becoming the caller's. A binder `∀ W : WalGS GF, S
(W := W) ...` (the WAL's specs at every generation's ghost names) is given `fun W : WalGS GF => ...`,
and a hypothesis reached through it that mentions `(W := W)` becomes `∀ W : WalGS GF, ...`, passed as
`(h W)`.
A binder that instantiates the no-I/O-error set (`(Sio := ioNone)`, wal-link L1a) instantiates it in the
result's hypotheses too, and a hypothesis that is then a no-error spec (one whose statement starts with
the coverage premise `(∀ st i, Sio.ino st i) →`) at `ioNone` holds vacuously: it is given `noErr_ioNone`
(`HandleShared.lean`), not taken.
"""
import os
import re
import sys
import textwrap

sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import link_bbolt  # noqa: E402  (its comment-stripping and declaration scanner)

NS = "Perennial.EtcdGrove.walfs"
OUT = "Proof/go_etcd_io/etcd/server/v3/storage/wal/Link.lean"
# the proofs whose results are the roots (module prefixes)
ROOT_DIRS = ["Proof.go_etcd_io.etcd.server.v3.storage.wal.",
             "Proof.go_etcd_io.etcd.client.pkg.v3.fileutil."]
# the main tree's proof directories whose theorems are candidate results (the WAL's and what it calls;
# until 2026-11-15 the part LinuxFs/'s proofs)
PROOF_DIRS = ["os", "syscall", "golang_org/x/sys/unix", "io", "internal", "bufio", "path/filepath", "hash",
              "errors", "fmt", "strings", "time", "encoding/binary", "runtime", "go_uber_org/zap",
              "google_golang_org/protobuf/proto", "go_etcd_io/etcd/client/pkg/v3",
              "go_etcd_io/etcd/pkg/v3/crc", "go_etcd_io/etcd/pkg/v3/ioutil", "go_etcd_io/etcd/pkg/v3/pbutil",
              "go_etcd_io/etcd/server/v3/storage/wal", "go_etcd_io/raft/v3/raftpb",
              "github_com/Masterminds", "github_com/prometheus"]
# the proofs' module prefixes (the main tree's, the part WalTester's)
PROOF_PFX = ("Proof.", "WalTester.Proof.")
# model parameters: binder types a spec is applied to
PARAMS = [r"WalPbIn GF", r"WalMarshal", r"WalCodec", r"WalUnmarshal", r"Loc → HardStateM → IProp GF"]
# premises (type pattern -> hypothesis name stem): facts about the model parameters, hypotheses
PREMISES = [
    (r"WalPbIn\.(\w+)(?: \((?:GF|hG) := \w+\))* P(?: \w+)*", lambda m: "WalPbIn_" + m.group(1)),
    (r"U\.Ok Mr", lambda m: "U_Ok"),
    (r"U\.SnapCoh", lambda m: "U_SnapCoh"),
    (r"WalHsOwn P U HsO", lambda m: "WalHsOwn"),
    (r"WalDecEnvSupply(?: \(GF := GF\))?", lambda m: "WalDecEnvSupply"),
]
# the section variables every result is stated under (the WAL's), before the collected instances
SEC_VARS = """variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
"""
# instance binders not collected (the section's own)
OWN_INSTS = {"GooseExts", "GooseSemantics", "GooseInterp", "ExtSemantics Fs.fsExt", "Fs.FsSemOk",
             "HasExt Fs.fsExt", "GoGlobalContext", "go.BasicIntoValInj", "HeapGS HasLC.hasLC GF",
             "HeapGS hlc GF", "WalGS GF", "go.Semantics", "ExtSemantics fsExt", "FsSemOk", "HasExt fsExt"}
# instance binders of the modules' other sections (the laws', at a program step), not the proofs'
OTHER_INSTS = re.compile(r"\bhlc\b|GooseGlobalGS|GooseLocalGS")
OPENS = "open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode\nopen Fs WalEnc WalFs\n"
# `--durable`: `examples/lib/durable` over `fsExt` (W4c U2), the same rules
DUR_DIR = "github_com/mit_pdos/etcd_grove/examples/lib/durable"
DURABLE = {
    "flag": "--durable",
    "lns": "durable",
    "NS": "Perennial.EtcdGrove.durable",
    "OUT": "WalTester/Proof/" + DUR_DIR + "/Link.lean",
    "ROOT_DIRS": ["WalTester.Proof." + DUR_DIR.replace("/", ".") + "."],
    "SEC_VARS": """variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
""",
    "OPENS": "open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode\nopen Fs DurFs\n",
    "what": ("`examples/lib/durable` over the per-byte Linux file extension (the part `WalTester/`: its "
             "`Read`, `Write` and their attempts, and the `os`, `filepath` they call; "
             "`notes/wal-fsext-w4c-plan.md`, W4c U2), every proof instantiated with its callees' "
             "results. The callees are read off each proof's binders (`etc/link_walfs.py`'s "
             "docstring). Generated by `etc/gen-link.py --durable` -- do not edit by hand."),
}
# the laws a client reasons with (entailments, not specs: no callee to link), restated in `section laws`
# so that they are roots of the trust-base report (unit `locks`, session 3)
WALFS_LAWS = [
    "Perennial.EtcdGrove.fileutil.lockKind_agree",
    "Perennial.EtcdGrove.fileutil.lockPost_held",
    "Perennial.EtcdGrove.fdLocks_excl",
]
WALFS = {
    "flag": "--walfs", "lns": "walfs", "NS": NS, "OUT": OUT, "ROOT_DIRS": ROOT_DIRS,
    "LAWS": WALFS_LAWS,
    "SEC_VARS": SEC_VARS, "OPENS": OPENS,
    "what": ("etcd's WAL over the per-byte Linux file extension (`wal`, `walpb`, "
             "`fileutil` and the `os`, `syscall`, `ioutil`, `crc`, ... they call; "
             "`notes/wal-fsext-plan.md`, section 8, \"Links\"), every proof instantiated with its callees' "
             "results. The callees are read off each proof's binders (`etc/link_walfs.py`'s docstring); a "
             "result is generic in the proof's model parameters (`P`, `Mr`, ...). Generated by "
             "`etc/gen-link.py --walfs` -- do not edit by hand."),
}
# `--wal-tester`: the WAL tester (`examples/etcd/wal`, W4c U5) over the WAL's and `durable`'s Links
TESTER_DIR = "github_com/mit_pdos/etcd_grove/examples/etcd/wal"
TESTER = {
    "flag": "--wal-tester",
    "lns": "walTester",
    "NS": "Perennial.EtcdGrove.walTester",
    "OUT": "WalTester/Proof/" + TESTER_DIR + "/Link.lean",
    "ROOT_DIRS": ["WalTester.Proof." + TESTER_DIR.replace("/", ".") + "."],
    # the Links whose results the tester's proofs are given (as they are, not re-linked)
    "EXT_LINKS": ["Proof.go_etcd_io.etcd.server.v3.storage.wal.Link",
                  "WalTester.Proof." + DUR_DIR.replace("/", ".") + ".Link"],
    "SEC_VARS": """variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
""",
    "OPENS": ("open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode\n"
              "open github_com.mit_pdos.etcd_grove.examples.etcd.wal Fs WalEnc WalFs\n"),
    "what": ("The WAL tester (`examples/etcd/wal`, the part `WalTester/`; `notes/wal-fsext-w4c-plan.md`, W4c "
             "U5), every proof instantiated with its callees' results: the tester's own, and the WAL's and "
             "`durable`'s linked results (their `Link.lean`s, used as they are). The callees are read off "
             "each proof's binders (`etc/link_walfs.py`'s docstring); a binder `∀ W : WalGS GF, S (W := W) "
             "...` (the WAL's specs at every generation's ghost names) is given `fun W => ...`, and a "
             "hypothesis of the WAL's result that mentions `W` becomes `∀ W : WalGS GF, ...`. Generated by "
             "`etc/gen-link.py --wal-tester` -- do not edit by hand."),
}
# the project directories of link_bbolt (unused here since 2026-11-15: every main-tree spec is scanned)
PROJECT_DIRS = link_bbolt.PROJECT_DIRS


def toks(s):
    """Top-level space-separated tokens of `s` (parenthesized groups kept whole)."""
    out, cur, depth = [], "", 0
    for ch in s:
        if ch in "([{" :
            depth += 1
        elif ch in ")]}":
            depth -= 1
        if ch == " " and depth == 0:
            if cur:
                out.append(cur)
            cur = ""
        else:
            cur += ch
    if cur:
        out.append(cur)
    return out


NAMED = re.compile(r"\((GF|hG|W|hlc) := [\w.]+\)$")


def parse_app(ty):
    """`X.spec<S> (GF := GF) a b` -> (name, [named args], [args]) or None."""
    ts = toks(ty.strip())
    if not ts or not re.fullmatch(r"(?:_root_\.)?[\w.«»']+\.spec[\w']*", ts[0]):
        return None
    named = [t for t in ts[1:] if NAMED.fullmatch(t)]
    args = [t for t in ts[1:] if not NAMED.fullmatch(t)]
    return ts[0], named, args


def scan(root, perennial, cfg=None):
    decls, varlines = [], {}
    ext_links = set((cfg or {}).get("EXT_LINKS", []))

    def walk(base, prefix, dirs_ok, want_all, only_link=False):
        if not os.path.isdir(base):
            return
        for dp, dns, fs in os.walk(base):
            rel = os.path.relpath(dp, base)
            if rel != "." and not dirs_ok(rel):
                dns[:] = []
                continue
            for f in sorted(fs):
                if not f.endswith(".lean") or (only_link and f != "Link.lean"):
                    continue
                p = os.path.join(dp, f)
                mod = prefix + os.path.relpath(p, base)[:-5].replace(os.sep, ".")
                if f == "Link.lean" and prefix.startswith(PROOF_PFX) and mod not in ext_links:
                    continue  # generated links (this generator's output, bboltfs's, ...) but the linked results given as they are
                n0 = len(decls)
                link_bbolt.scan_file(p, mod, decls, want_all or f == "Link.lean")
                if prefix.startswith(PROOF_PFX) and len(decls) > n0:
                    src = link_bbolt.strip_comments(open(p, encoding="utf-8").read())
                    varlines[mod] = re.findall(r"^variable (.*)$", src, re.M)

    def under(dirs):
        ds = [d.replace("/", os.sep) for d in dirs]
        return lambda r: any((r + os.sep).startswith(d + os.sep) or (d + os.sep).startswith(r + os.sep)
                             for d in ds)

    if cfg is not None and cfg.get("flag") in ("--durable", "--wal-tester"):
        # the part's specs first: they take the place of the main tree's (`durable`'s, trusted)
        walk(os.path.join(root, "WalTester", "Spec"), "WalTester.Spec.", lambda r: True, False)
        walk(os.path.join(root, "WalTester", "Proof"), "WalTester.Proof.", lambda r: True, True)
    walk(os.path.join(root, "Spec"), "Spec.", lambda r: True, False)
    walk(os.path.join(root, "Proof"), "Proof.", under(PROOF_DIRS), True)
    walk(os.path.join(perennial, "Perennial", "Spec"), "Perennial.Spec.", lambda r: True, False)
    walk(os.path.join(perennial, "Perennial", "Proof"), "Perennial.Proof.", lambda r: True, True,
         only_link=True)
    return decls, varlines


def main(root, perennial, argv0, check=False, cfg=None):
    global NS, OUT, ROOT_DIRS, SEC_VARS, OPENS
    cfg = cfg or WALFS
    NS, OUT, ROOT_DIRS, SEC_VARS, OPENS = (cfg["NS"], cfg["OUT"], cfg["ROOT_DIRS"], cfg["SEC_VARS"],
                                           cfg["OPENS"])
    flag, lns = cfg["flag"], cfg["lns"]
    decls, varlines = scan(root, perennial, cfg)
    ext_links = set(cfg.get("EXT_LINKS", []))
    specs = {}
    for x in decls:
        if x["kind"] in ("abbrev", "def") and re.search(r"\.spec[\w']*$", x["name"]):
            # the first found is kept (WalTester's, scanned first for --durable)
            specs.setdefault(x["name"], x)

    def resolve(a, ns):
        if a.startswith("_root_."):
            return a[7:] if a[7:] in specs else None
        parts = ns.split(".") if ns else []
        for k in range(len(parts), -1, -1):
            c = ".".join(parts[:k] + [a])
            if c in specs:
                return c
        return None

    def classify(h, ns):
        """A binder: [('param', name, ty) | ('spec', name, spec, named, args) | ('premise', name,
        ty, stem)] (one per name), [] to skip, or None (not a result's)."""
        if h.startswith(("{", "⦃", "[")):
            return []
        m = re.match(r"\(\s*([\w']+(?:\s+[\w']+)*)\s*:\s*(.*)\)$", h)
        if not m:
            return None
        names, ty = m.group(1).split(), " ".join(m.group(2).split())
        fw = False
        mw = re.fullmatch(r"∀ W : WalGS GF, (.*)", ty)
        if mw:
            fw, ty = True, mw.group(1)
        out = []
        for n in names:
            if any(re.fullmatch(p, ty) for p in PARAMS):
                out.append(("param", n, ty))
                continue
            app = parse_app(ty)
            if app:
                r = resolve(app[0], ns)
                if not r:
                    return None
                out.append(("spec", n, r, app[1], app[2], fw))
                continue
            if fw:
                return None
            for pat, stem in PREMISES:
                pm = re.fullmatch(pat, ty)
                if pm:
                    # one text per proposition: a law of `P` leaves the heap's names to
                    # elaboration (`P`'s type fixes `GF`)
                    if ty.startswith("WalPbIn."):
                        ty = re.sub(r" \((?:GF|hG) := \w+\)", "", ty)
                    out.append(("premise", n, ty, stem(pm)))
                    break
            else:
                return None
        return out

    def concl(x):
        app = parse_app(x["concl"])
        if not app:
            return None
        r = resolve(app[0], x["ns"])
        return (r, app[1], app[2]) if r else None

    # Perennial's linked results: spec -> (term, module)
    linked = {}
    for x in decls:
        if x["mod"].startswith("Perennial.Proof.") and x["mod"].endswith(".Link") \
                and x["kind"] == "theorem":
            c = concl(x)
            if c and not c[2] and c[0] not in linked:
                linked[c[0]] = ("_root_." + x["name"], x["mod"])

    # the part's proofs of specs: spec -> candidates
    cands, rejected = {}, []
    for x in decls:
        if not x["mod"].startswith(PROOF_PFX) or x["kind"] not in ("theorem", "axiom"):
            continue
        c = concl(x)
        if not c:
            continue
        bs = [classify(h, x["ns"]) for h in x["hyps"]]
        if any(b is None for b in bs):
            if x["mod"].startswith(tuple(ROOT_DIRS)) and re.search(r"\.wp_proof[\w']*$", x["name"]):
                rejected.append(x["name"])
            continue
        x["binders"] = [b for bl in bs for b in bl]
        params = [b for b in x["binders"] if b[0] == "param"]
        # the conclusion's arguments are parameters or closed terms
        x["spec"], x["named"], x["args"] = c
        x["params"] = params
        x["ext"] = x["mod"] in ext_links
        cands.setdefault(c[0], []).append(x)

    # the specs a non-linked proof takes under `∀ W : WalGS GF` (the WAL's at every generation): a
    # linked result (`EXT_LINKS`) is generic in its section's `[W : WalGS GF]`, so it can be given only
    # there; elsewhere (a `walpb` getter's spec, which no `W` is in scope for) the spec is re-linked
    fw_specs = {b[2] for xs in cands.values() for x in xs if not x["ext"]
                for b in x["binders"] if b[0] == "spec" and b[5]}

    def pick(s, xs):
        base, suf = re.match(r"(.*)\.spec([\w']*)$", s).groups()
        ext = [x for x in xs if x["ext"]]
        rest = [x for x in xs if not x["ext"]]
        if ext and (s in fw_specs or not rest):
            return ext[0]
        xs = rest
        named = [x for x in xs if x["name"] == f"{base}.wp_proof{suf}"]
        return named[0] if named else min(xs, key=lambda x: (len(x["binders"]), x["name"]))

    proofs = {s: pick(s, xs) for s, xs in cands.items()}

    # what each spec is given
    how = {}

    def visit(s):
        if s in how:
            return
        if s in proofs:
            how[s] = ("result", proofs[s])
            for b in proofs[s]["binders"]:
                if b[0] == "spec":
                    visit(b[2])
        elif s in linked:
            how[s] = ("linked",) + linked[s]
        else:
            how[s] = ("pending",)

    roots = sorted(s for s, x in proofs.items() if x["mod"].startswith(tuple(ROOT_DIRS)))
    for s in roots:
        visit(s)

    def strip_ns(base):
        for p in (NS + ".", "Perennial.EtcdGrove.", "Perennial."):
            if base.startswith(p):
                return base[len(p):]
        return base

    def short(s):
        base, suf = re.match(r"(.*)\.spec([\w']*)$", s).groups()
        *q, last = strip_ns(base).split(".")
        return ".".join(q + [f"wp_{last.strip('«»')}{suf}"])

    def spec_hyp_stem(s):
        base, suf = re.match(r"(.*)\.spec([\w']*)$", s).groups()
        b = strip_ns(base)
        for p in ("go_etcd_io.etcd.server.v3.storage.", "go_etcd_io.etcd.client.pkg.v3.",
                  "go_etcd_io.etcd.pkg.v3.", "go_etcd_io.etcd."):
            if b.startswith(p):
                b = b[len(p):]
                break
        return b.replace(".", "_").replace("«", "").replace("»", "") + suf

    def norm(t):
        return " ".join(t.split())

    def subst(t, sub):
        if not sub:
            return t
        pat = re.compile(r"(?<![\w.'])(" + "|".join(re.escape(k) for k in sub) + r")(?![\w'])")
        return pat.sub(lambda m: sub[m.group(1)], t)

    # hypotheses: type text -> name (global, so that callers pass their own by type)
    hyp_names, hyp_types, hyp_types_stem = {}, {}, {}

    def hyp_name(ty, stem):
        ty = norm(ty)
        if ty in hyp_names:
            return hyp_names[ty]
        n, k = "h_" + stem, 2
        while n in hyp_types:
            n, k = f"h_{stem}_{k}", k + 1
        hyp_names[ty], hyp_types[n], hyp_types_stem[n] = n, ty, stem
        return n

    def wrapW(ty, fw):
        """A hypothesis under a binder `∀ W : WalGS GF, ...`: quantified if it mentions `W`."""
        return f"∀ W : WalGS GF, {ty}" if fw and "(W := W)" in ty else ty

    def spec_ty(s, named, args):
        return norm(" ".join([f"_root_.{s}"] + named + args))

    # each result's hypotheses (type texts, in its own parameters' terms), memoized
    hyps_of = {}

    def inst(callee, b):
        """The callee's parameter instantiation from the caller's binder `b`."""
        x = how[callee][1]
        sub = {}
        cargs = x["args"]
        if len(cargs) != len(b[4]):
            sys.exit(f"gen-link.py {flag}: {x['name']}'s conclusion and a binder of {b[2]} differ "
                     f"in arity: {cargs} vs {b[4]}")
        for ca, ba in zip(cargs, b[4]):
            if any(p[1] == ca for p in x["params"]):
                sub[ca] = ba
            elif ca != ba:
                # an implicit section variable named in the conclusion (`(Sio := Sio)` of `{Sio : IoSet}`,
                # wal-link L1a): the binder's instance (`(Sio := ioNone)`) is Lean's to unify
                m = re.fullmatch(r"\(([\w']+) := \1\)", ca)
                if not (m and re.fullmatch(r"\(" + re.escape(m.group(1)) + r" := .+\)", ba)):
                    sys.exit(f"gen-link.py {flag}: {x['name']} proves {callee} at {ca}, a binder needs {ba}")
                # ... and the callee's hypotheses that name it are at the binder's instance
                sub[ca] = ba
        for p in x["params"]:
            sub.setdefault(p[1], p[1])
        return sub

    # the model parameters a result takes beyond its proof's own: a callee's parameter its conclusion
    # does not mention (so the caller's of the same name) that the caller has not (as
    # `validSnapshotEntries.specPinned`'s `P U HsO` under `ValidSnapshotEntries`, whose spec takes `Mr` only)
    extras_of = {}

    def extras(s):
        if s in extras_of:
            return extras_of[s]
        extras_of[s] = []
        x = how[s][1]
        names = {p[1] for p in x["params"]}
        out = []
        for b in x["binders"]:
            if b[0] != "spec" or how[b[2]][0] != "result":
                continue
            cx = how[b[2]][1]
            sub = inst(b[2], b)
            for p in [q for q in cx["params"] if sub[q[1]] == q[1]] + extras(b[2]):
                if p[1] not in names:
                    names.add(p[1])
                    out.append(p)
        extras_of[s] = out
        return out

    # a no-error spec (`<T>.<M>.spec…` whose statement starts with the coverage premise
    # `(∀ st i, Sio.ino st i) →`, wal-link L1a) at `(Sio := ioNone)` holds vacuously (`noErr_ioNone`,
    # `HandleShared.lean`): a hypothesis of that type is discharged, not taken
    cov_of = {}

    def covers_premise(spec):
        if spec not in cov_of:
            x = specs.get(spec)
            ok = False
            if x is not None:
                path = os.path.join(root, *x["mod"].split(".")) + ".lean"
                try:
                    src = link_bbolt.strip_comments(open(path, encoding="utf-8").read())
                except OSError:
                    src = ""
                short_name = spec[len(x["ns"]) + 1:] if x["ns"] and spec.startswith(x["ns"] + ".") else spec
                m = re.search(r"\babbrev\s+(?:_root_\.)?" + re.escape(short_name) + r"\b.*?:=\s*", src, re.S)
                ok = bool(m) and re.match(r"\(∀ st i, Sio\.ino st i\) →", src[m.end():]) is not None
            cov_of[spec] = ok
        return cov_of[spec]

    def vacuous(ty):
        app = parse_app(norm(ty))
        if not app or not ({"(Sio := ioNone)", "(Sio := WalFs.ioNone)"} & set(app[2])):
            return False
        name = app[0][len("_root_."):] if app[0].startswith("_root_.") else app[0]
        return covers_premise(name)

    def hyps(s):
        if s in hyps_of:
            return hyps_of[s]
        hyps_of[s] = []  # (a cycle is an error of the proofs; it shows as missing hypotheses)
        x = how[s][1]
        out = []

        def add(ty, stem, fw=False):
            if vacuous(ty):
                return
            n = hyp_name(wrapW(norm(ty), fw), stem)
            if n not in out:
                out.append(n)
        for b in x["binders"]:
            if b[0] == "premise":
                add(b[2], b[3])
            elif b[0] == "spec":
                h = how[b[2]]
                fw = len(b) > 5 and b[5]
                if h[0] == "pending":
                    add(spec_ty(b[2], b[3], b[4]), spec_hyp_stem(b[2]), fw)
                elif h[0] == "result":
                    sub = inst(b[2], b)
                    for ty, stem in raw_hyps(b[2]):
                        add(subst(ty, {k: v for k, v in sub.items() if k != v}), stem, fw)
        hyps_of[s] = sorted(out)
        return hyps_of[s]

    def raw_hyps(s):
        """A result's hypotheses as (type, stem): a linked result's (`EXT_LINKS`) read off its binders,
        not named here (its caller names them, in its own parameters' terms)."""
        x = how[s][1]
        if not x["ext"]:
            return [(hyp_types[n], hyp_types_stem[n]) for n in hyps(s)]
        out = []
        for b in x["binders"]:
            if b[0] == "premise":
                out.append((norm(b[2]), b[3]))
            elif b[0] == "spec":
                if how[b[2]][0] != "pending":
                    sys.exit(f"gen-link.py {flag}: {x['name']}'s binder {b[1]} has a proof")
                out.append((spec_ty(b[2], b[3], b[4]), spec_hyp_stem(b[2])))
        return out

    order, seen = [], set()

    def topo(s):
        if s in seen:
            return
        seen.add(s)
        if how[s][0] == "result":
            for b in how[s][1]["binders"]:
                if b[0] == "spec":
                    topo(b[2])
            if not how[s][1]["ext"]:
                order.append(s)

    for s in sorted(how):
        topo(s)
    for s in order:
        hyps(s)

    def term(b):
        fw = len(b) > 5 and b[5]
        t = term0(b, fw)
        return f"(fun W : WalGS GF => {t})" if fw else t

    def hyp_arg(ty, fw):
        ty = norm(ty)
        if vacuous(ty):
            return "noErr_ioNone"
        n = hyp_names[wrapW(ty, fw)]
        return f"({n} W)" if wrapW(ty, fw) != ty else n

    def term0(b, fw):
        h = how[b[2]]
        if h[0] == "linked":
            return h[1]
        if h[0] == "pending":
            return hyp_arg(spec_ty(b[2], b[3], b[4]), fw)
        x = h[1]
        sub = inst(b[2], b)
        if x["ext"]:
            # a linked result used as it is: its own binders, in order
            args = []
            sb = {k: v for k, v in sub.items() if k != v}
            for cb in x["binders"]:
                if cb[0] == "param":
                    args.append(sub[cb[1]])
                elif cb[0] == "premise":
                    args.append(hyp_arg(subst(cb[2], sb), fw))
                else:
                    args.append(hyp_arg(subst(spec_ty(cb[2], cb[3], cb[4]), sb), fw))
            r = f"_root_.{x['name']}"
            return f"({r} {' '.join(args)})" if args else r
        args = [sub[p[1]] for p in x["params"]] + [p[1] for p in extras(b[2])]
        hs = []
        for n in hyps_of[b[2]]:
            ty = norm(subst(hyp_types[n], {k: v for k, v in sub.items() if k != v}))
            hs.append(hyp_arg(ty, fw))
        r = f"_root_.{NS}.{short(b[2])}"
        return f"({r} {' '.join(args + hs)})" if args or hs else r

    def emit(s):
        x = how[s][1]
        binders = [f"({p[1]} : {p[2]})" for p in x["params"] + extras(s)] + \
            [f"({n} : {hyp_types[n]})" for n in hyps_of[s]]
        args = []
        for b in x["binders"]:
            if b[0] == "param":
                args.append(b[1])
            elif b[0] == "premise":
                args.append(hyp_names[norm(b[2])])
            else:
                args.append(term(b))
        head = f"theorem {short(s)}"
        bl = textwrap.wrap(" ".join(binders), 92, break_on_hyphens=False, break_long_words=False)
        stmt = head + ("\n    " + "\n    ".join(bl) if bl else "") + " :\n    " + \
            spec_ty(s, x["named"], x["args"]) + " :=\n"
        body = textwrap.wrap(" ".join([f"_root_.{x['name']}"] + args), 94, break_on_hyphens=False,
                             break_long_words=False)
        return stmt + "  " + "\n    ".join(body) + "\n"

    names = [short(s) for s in order]
    dup = {n for n in names if names.count(n) > 1}
    if dup:
        sys.exit(f"gen-link.py {flag}: two results named {sorted(dup)}")

    # the section's instances: the linked proofs' own and their modules' `variable` lines
    insts = []
    # implicit section variables an instance names (`{Sio : IoSet}` of `[FsStepSat (NoIoErr Sio)]`,
    # unit `noioerr`): emitted before the instances, those of `SEC_VARS` left out
    imps = []
    exts = sorted(s for s, h in how.items() if h[0] == "result" and h[1]["ext"])
    for s in order + exts:
        x = how[s][1]
        groups = [h for h in x["hyps"] if h.startswith("[")]
        for line in varlines.get(x["mod"], []):
            groups += re.findall(r"\[[^\]]*\]", line)
            for g in re.findall(r"\{[^\}]*\}", line):
                g = " ".join(g.split())
                if g not in SEC_VARS and g not in imps:
                    imps.append(g)
        for g in groups:
            cls = " ".join(re.sub(r"^\[\s*(?:[\w']+\s*:\s*)?", "", g)[:-1].split())
            if cls not in OWN_INSTS and not OTHER_INSTS.search(cls) and cls not in insts:
                insts.append(cls)

    imps = [g for g in imps
            if any(re.search(r"\b" + re.escape(v) + r"\b", c) for c in insts
                   for v in g[1:-1].split(":")[0].split())]

    # the laws (`cfg["LAWS"]`): their declarations, restated (`emit_law`)
    laws = []
    for ln in cfg.get("LAWS", []):
        xs = [x for x in decls if x["name"] == ln[len("Perennial."):] or x["name"] == ln]
        if not xs:
            sys.exit(f"gen-link.py {flag}: law {ln} not found")
        laws.append(xs[0])

    def emit_law(x):
        args = []
        for h in x["hyps"]:
            m = re.match(r"\(\s*([\w']+(?:\s+[\w']+)*)\s*:", h)
            if m:
                args.extend(m.group(1).split())
        nm = x["name"].split(".")[-1]
        bl = textwrap.wrap(" ".join(x["hyps"]), 92, break_on_hyphens=False, break_long_words=False)
        stmt = f"theorem law_{nm}" + ("\n    " + "\n    ".join(bl) if bl else "") + " :\n    " + \
            "\n    ".join(textwrap.wrap(x["concl"], 96, break_on_hyphens=False,
                                         break_long_words=False)) + " :=\n"
        body = textwrap.wrap(" ".join([f"_root_.Perennial.{x['name']}" if not x["name"].startswith(
            "Perennial.") else f"_root_.{x['name']}"] + args), 94, break_on_hyphens=False,
            break_long_words=False)
        return stmt + "  " + "\n    ".join(body) + "\n"

    for x in laws:
        for line in varlines.get(x["mod"], []):
            for g in re.findall(r"\[[^\]]*\]", line):
                cls = " ".join(re.sub(r"^\[\s*(?:[\w']+\s*:\s*)?", "", g)[:-1].split())
                if cls not in OWN_INSTS and not OTHER_INSTS.search(cls) and cls not in insts:
                    insts.append(cls)

    imports = set(x["mod"] for x in laws)
    for s, h in how.items():
        if h[0] == "result":
            imports.add(h[1]["mod"])
        elif h[0] == "linked":
            imports.add(h[2])
        else:
            imports.add(specs[s]["mod"])
    # a module another imported one imports is left out by Lean anyway; keep the list complete

    pend = sorted(hyp_types)
    reach = {n: sum(1 for s in order if n in hyps_of[s]) for n in pend}
    closed = [s for s in order if not hyps_of[s]]
    header = ("/-\n" + textwrap.fill(cfg["what"], 100, break_on_hyphens=False)
        + "\n\n" + textwrap.fill(
            f"{len(order)} results, {len(closed)} of them with no hypothesis. The others take, as "
            "hypotheses `h_<name>`, the specs with no proof and the premises on the model "
            "parameters (the client's protobuf laws, ...) they reach: "
            + ", ".join(f"`{n}` ({reach[n]})" for n in pend) + ".", 100, break_on_hyphens=False)
        + "\n\n`#print axioms` on a result is its trust base (`etc/tcb-report.py`).\n-/")
    out = [header, "module", ""]
    out.extend(f"public import {m}" for m in sorted(imports))
    out.append("""
@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace """ + lns + """

""" + OPENS + """
section links
""" + SEC_VARS + "".join(f"variable {g}\n" for g in imps) + "".join(f"variable [{c}]\n" for c in insts))
    out.extend(emit(s) for s in order if not hyps_of[s])
    out.append("end links\n")
    out.append("""/-! The results that reach a spec with no proof or a premise on the model parameters: each takes
them as hypotheses (`h_<name>`, explicit binders). -/
section links_pending
""" + SEC_VARS + "".join(f"variable {g}\n" for g in imps) + "".join(f"variable [{c}]\n" for c in insts))
    out.extend(emit(s) for s in order if hyps_of[s])
    out.append("end links_pending\n")
    if laws:
        out.append("""/-! The laws a client of these results reasons with (entailments, restated from their proofs:
each is its proof applied to its explicit binders). -/
section laws
""" + SEC_VARS + "".join(f"variable {g}\n" for g in imps) + "".join(f"variable [{c}]\n" for c in insts))
        out.extend(emit_law(x) for x in laws)
        out.append("end laws\n")
    out.append("end " + lns + "\nend EtcdGrove\nend Perennial")
    text = "\n".join(out) + "\n"
    if rejected:
        print(f"gen-link.py {flag}: root proofs with a binder of no known kind (not linked): "
              + ", ".join(sorted(rejected)), file=sys.stderr)
    if check:
        cur = open(os.path.join(root, OUT), encoding="utf-8").read() if os.path.exists(
            os.path.join(root, OUT)) else ""
        if cur != text:
            print(f"gen-link.py {flag}: {OUT} differs from the generated file", file=sys.stderr)
            sys.exit(1)
        return
    sys.stdout.write(text)
