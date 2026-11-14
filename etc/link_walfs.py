"""`etc/gen-link.py --walfs`: LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/Link.lean, etcd's
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

- **The results.** Every `theorem`/`axiom` of the part's proofs (`LinuxFs/Proof/`) whose conclusion
  is a spec applied to arguments (`<T>.<M>.spec<S> (W := W) a ...`), and whose explicit binders are
  all callee specs, model parameters (`PARAMS`) or premises (`PREMISES`), proves that spec (a
  proof generic in more, as `wp_core`'s `(h : WalHS)`, is a lemma of another proof). A spec proved
  twice is linked once: by the theorem named `<T>.<M>.wp_proof<S>` if there is one, else by the one
  with the fewest binders. The roots are the proofs of `ROOT_DIRS` (the WAL, `walpb`, `fileutil`);
  the results their binders reach are linked too, whatever their package (`os`, `syscall`,
  `ioutil`, `crc`, ...: the part's proofs, the result's name says the package).
- **A result** `<T>.wp_<M><S>` (namespace `EtcdGrove.walfs`) takes the proof's model parameters
  (same names, same order), then one hypothesis `h_<name>` for each spec with no proof and each
  premise its proof or a callee's (transitively) takes, and states the proof's conclusion. The
  results with a hypothesis are in `section links_pending` (`etc/proof_roots.py`'s pending roots).
- **The callees** are the proof's explicit binders, in order: a spec with a result is given it, its
  model parameters matched against the binder's arguments (a parameter the callee's conclusion
  does not mention is the caller's of the same name); Perennial's linked results
  (`Perennial/Proof/<pkg>/Link.lean`) are used as they are; a spec with no proof is a hypothesis.
- **Premises** (`PREMISES`: the laws of the client's protobuf model `P`, the decoder's environment
  supply) are hypotheses: they are facts about the parameters, which the WAL's client discharges.
- Instance binders (`[os.file.FieldAssumptions]`, the packages' `Assumptions`) are section
  variables, collected from the linked proofs' own and their modules' `variable` lines.

A binder of a kind none of these covers makes the theorem a lemma, not a result; a root proof with
one is reported on stderr. `--check` compares the output with the committed file.
"""
import os
import re
import sys
import textwrap

sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import link_bbolt  # noqa: E402  (its comment-stripping and declaration scanner)

NS = "Perennial.EtcdGrove.walfs"
OUT = "LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/Link.lean"
# the proofs whose results are the roots (module prefixes)
ROOT_DIRS = ["LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.",
             "LinuxFs.Proof.go_etcd_io.etcd.client.pkg.v3.fileutil."]
# model parameters: binder types a spec is applied to
PARAMS = [r"WalPbIn GF", r"WalMarshal", r"WalCodec", r"WalUnmarshal", r"Loc → HardStateM → IProp GF"]
# premises (type pattern -> hypothesis name stem): facts about the model parameters, hypotheses
PREMISES = [
    (r"WalPbIn\.(\w+)(?: \((?:GF|hG) := \w+\))* P(?: \w+)*", lambda m: "WalPbIn_" + m.group(1)),
    (r"U\.Ok Mr", lambda m: "U_Ok"),
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
# the main tree's and Perennial's directories scanned for specs (the part's copies take precedence)
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


def scan(root, perennial):
    decls, varlines = [], {}

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
                if f == "Link.lean" and prefix.startswith("LinuxFs."):
                    continue  # this generator's output, bboltfs's
                p = os.path.join(dp, f)
                mod = prefix + os.path.relpath(p, base)[:-5].replace(os.sep, ".")
                n0 = len(decls)
                link_bbolt.scan_file(p, mod, decls, want_all or f == "Link.lean")
                if prefix.startswith("LinuxFs.Proof.") and len(decls) > n0:
                    src = link_bbolt.strip_comments(open(p, encoding="utf-8").read())
                    varlines[mod] = re.findall(r"^variable (.*)$", src, re.M)

    def std(rel):
        return rel.split(os.sep)[0] not in PROJECT_DIRS or rel.split(os.sep)[0] == "go_uber_org"

    walk(os.path.join(root, "LinuxFs", "Spec"), "LinuxFs.Spec.", lambda r: True, False)
    walk(os.path.join(root, "LinuxFs", "Proof"), "LinuxFs.Proof.",
         lambda r: not r.startswith("github_com" + os.sep + "mit_pdos"), True)
    walk(os.path.join(root, "Spec"), "Spec.", std, False)
    walk(os.path.join(perennial, "Perennial", "Spec"), "Perennial.Spec.", lambda r: True, False)
    walk(os.path.join(perennial, "Perennial", "Proof"), "Perennial.Proof.", lambda r: True, True,
         only_link=True)
    return decls, varlines


def main(root, perennial, argv0, check=False):
    decls, varlines = scan(root, perennial)
    specs = {}
    for x in decls:
        if x["kind"] in ("abbrev", "def") and re.search(r"\.spec[\w']*$", x["name"]):
            # the part's copy of a spec takes the place of the main tree's (scanned first)
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
                out.append(("spec", n, r, app[1], app[2]))
                continue
            for pat, stem in PREMISES:
                pm = re.fullmatch(pat, ty)
                if pm:
                    # one text per proposition: the heap's names left to elaboration
                    out.append(("premise", n, re.sub(r" \((?:GF|hG) := \w+\)", "", ty), stem(pm)))
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
        if not x["mod"].startswith("LinuxFs.Proof.") or x["kind"] not in ("theorem", "axiom"):
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
        cands.setdefault(c[0], []).append(x)

    def pick(s, xs):
        base, suf = re.match(r"(.*)\.spec([\w']*)$", s).groups()
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
            sys.exit(f"gen-link.py --walfs: {x['name']}'s conclusion and a binder of {b[2]} differ "
                     f"in arity: {cargs} vs {b[4]}")
        for ca, ba in zip(cargs, b[4]):
            if any(p[1] == ca for p in x["params"]):
                sub[ca] = ba
            elif ca != ba:
                sys.exit(f"gen-link.py --walfs: {x['name']} proves {callee} at {ca}, a binder needs {ba}")
        for p in x["params"]:
            sub.setdefault(p[1], p[1])
        return sub

    def hyps(s):
        if s in hyps_of:
            return hyps_of[s]
        hyps_of[s] = []  # (a cycle is an error of the proofs; it shows as missing hypotheses)
        x = how[s][1]
        out = []

        def add(ty, stem):
            n = hyp_name(ty, stem)
            if n not in out:
                out.append(n)
        for b in x["binders"]:
            if b[0] == "premise":
                add(b[2], b[3])
            elif b[0] == "spec":
                h = how[b[2]]
                if h[0] == "pending":
                    add(spec_ty(b[2], b[3], b[4]), spec_hyp_stem(b[2]))
                elif h[0] == "result":
                    sub = inst(b[2], b)
                    for n in hyps(b[2]):
                        add(subst(hyp_types[n], {k: v for k, v in sub.items() if k != v}),
                            hyp_types_stem[n])
        hyps_of[s] = sorted(out)
        return hyps_of[s]

    order, seen = [], set()

    def topo(s):
        if s in seen:
            return
        seen.add(s)
        if how[s][0] == "result":
            for b in how[s][1]["binders"]:
                if b[0] == "spec":
                    topo(b[2])
            order.append(s)

    for s in sorted(how):
        topo(s)
    for s in order:
        hyps(s)

    def term(b):
        h = how[b[2]]
        if h[0] == "linked":
            return h[1]
        if h[0] == "pending":
            return hyp_names[spec_ty(b[2], b[3], b[4])]
        x = h[1]
        sub = inst(b[2], b)
        args = [sub[p[1]] for p in x["params"]]
        hs = []
        for n in hyps_of[b[2]]:
            ty = norm(subst(hyp_types[n], {k: v for k, v in sub.items() if k != v}))
            hs.append(hyp_names[ty])
        r = f"_root_.{NS}.{short(b[2])}"
        return f"({r} {' '.join(args + hs)})" if args or hs else r

    def emit(s):
        x = how[s][1]
        binders = [f"({p[1]} : {p[2]})" for p in x["params"]] + \
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
        sys.exit(f"gen-link.py --walfs: two results named {sorted(dup)}")

    # the section's instances: the linked proofs' own and their modules' `variable` lines
    insts = []
    for s in order:
        x = how[s][1]
        groups = [h for h in x["hyps"] if h.startswith("[")]
        for line in varlines.get(x["mod"], []):
            groups += re.findall(r"\[[^\]]*\]", line)
        for g in groups:
            cls = " ".join(re.sub(r"^\[\s*(?:[\w']+\s*:\s*)?", "", g)[:-1].split())
            if cls not in OWN_INSTS and not OTHER_INSTS.search(cls) and cls not in insts:
                insts.append(cls)

    imports = set()
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
    header = ("/-\n" + textwrap.fill(
        "etcd's WAL over the per-byte Linux file extension (the part `LinuxFs/`: `wal`, `walpb`, "
        "`fileutil` and the part's `os`, `syscall`, `ioutil`, `crc`, ... they call; "
        "`notes/wal-fsext-plan.md`, section 8, \"Links\"), every proof instantiated with its callees' "
        "results. The callees are read off each proof's binders (`etc/link_walfs.py`'s docstring); a "
        "result is generic in the proof's model parameters (`P`, `Mr`, ...). Generated by "
        "`etc/gen-link.py --walfs` -- do not edit by hand.", 100, break_on_hyphens=False)
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
namespace walfs

""" + OPENS + """
section links
""" + SEC_VARS + "".join(f"variable [{c}]\n" for c in insts))
    out.extend(emit(s) for s in order if not hyps_of[s])
    out.append("end links\n")
    out.append("""/-! The results that reach a spec with no proof or a premise on the model parameters: each takes
them as hypotheses (`h_<name>`, explicit binders). -/
section links_pending
""" + SEC_VARS + "".join(f"variable [{c}]\n" for c in insts))
    out.extend(emit(s) for s in order if hyps_of[s])
    out.append("end links_pending\n\nend walfs\nend EtcdGrove\nend Perennial")
    text = "\n".join(out) + "\n"
    if rejected:
        print("gen-link.py --walfs: root proofs with a binder of no known kind (not linked): "
              + ", ".join(sorted(rejected)), file=sys.stderr)
    if check:
        cur = open(os.path.join(root, OUT), encoding="utf-8").read() if os.path.exists(
            os.path.join(root, OUT)) else ""
        if cur != text:
            print(f"gen-link.py --walfs: {OUT} differs from the generated file", file=sys.stderr)
            sys.exit(1)
        return
    sys.stdout.write(text)
