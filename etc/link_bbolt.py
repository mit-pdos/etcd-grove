"""`etc/gen-link.py --bbolt`: Proof/go_etcd_io/bbolt/Link.lean, every bbolt proof applied to its
callees' results.

Unlike the other modes, the callees are not listed in an `etc/link-lean-first-*.txt` file: they
are read off each proof's binders, as `etc/gen-btree-link.py` does. bbolt's proofs are many (about
300, in `internal/common` and `internal/freelist` too), several prove a second spec of a function
(`Cursor.seek_w.specQ`, `DB.close.spec_owned`, `node.rebalance.spec'`: the theorem's conclusion
says which), and the internal specs of the module groups are stated in their proof modules
(`Spill/`, `Commit/`, `Open/`, `Mmap/`), not in `Spec/` files: the binders are the one record
of what each proof takes, and a list would restate them.

The rules:

- **The results.** Every `theorem`/`axiom` under `Proof/go_etcd_io/bbolt/` whose conclusion is a
  spec (`<T>.<M>.spec<S>`, any suffix) and whose explicit binders are all callee specs or the
  premises below (a proof generic in more, as `shared`'s methods over any freelist implementation
  `(I : FLImpl)`, is a lemma of another proof, not a result) proves that spec; its result is
  `<T>.wp_<M><S>` (in the namespace `EtcdGrove.bbolt`). A spec proved twice is linked once: by
  the theorem named `<T>.<M>.wp_proof<S>` if there is one, else by the one with the fewest
  binders.
- **The callees** are the proof's explicit binders, in order: a spec (or `∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt],
  <spec>`, which the result fills, the extension being a section variable) is given its result:
  bbolt's own; Perennial's linked result (`Perennial/Proof/<pkg>/Link.lean`), or
  etcd-grove's shared trust boundary of `fmt`/`context` (`Proof/fmt/Link.lean`: as the `@`
  callees of the other modes); else the result of etcd-grove's own proof of it
  (`Proof/os/`, `Proof/syscall/`, ...: the file-system model's, as minibolt's Link links them),
  linked here too, in the namespace `bbolt` (`bbolt.os.File.wp_Close`).
- **Specs with no proof** (a callee left a hypothesis: `fs.FileMode.String.spec`) and the **premises without proof** (`PREMISES` with no term:
  `PidSetDeleteUnfold`, a Perennial gap) are hypotheses `h_<name>` of a section
  `links_pending`, as a `?` callee of the other modes: every result reaching one is stated
  there, and takes them all.
- **Premises** that are not specs are given by `PREMISES` (type pattern -> term): facts proved
  elsewhere (`errnoErrOk_holds`), a trust-boundary axiom shared with the server
  (`sort.«Sort».wp_anyLess`), and the freelist implementations' contracts
  (`internal.freelist.impl_contract` of the callees `FLCallees` they rest on).
- **The backend's `_kv` axioms** (`bbolt.Open_kv.wp_proof`, ...: the old trust boundary etcd's
  backend still rests on, until the backend switch derives them from the triples) are not
  results: an `axiom` proving a `_kv` spec is skipped, so neither `Link.lean` nor `Results.lean`
  presents it as bbolt's.
- Instance binders (`[sync.Assumptions]`, `[ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]`) are left to instance search: the
  section's `[package_sem : go_etcd_io.bbolt.Assumptions]` includes every imported package's;
  the field assumptions of `os`'s trusted `file` and `fileStat` (`TrustedCode/os.lean`), which
  no package's `Assumptions` include, are section variables too (as in bboltfs's `Link.lean`).

A binder of a kind none of these covers stops the generator, naming it.
"""
import os
import re
import sys
import textwrap

NS = "Perennial.EtcdGrove.bbolt"
PKG = "go_etcd_io/bbolt"

# Non-spec premises: (type pattern, term or None for a hypothesis of `links_pending`, its
# hypothesis name, the module the term is from). `{fc}` is the freelist callees' term.
PREMISES = [
    (r"errnoErrOk \(GF := GF\) \(hG := hG\)", "_root_.Perennial.EtcdGrove.bbolt.errnoErrOk_holds",
     None, "Proof.go_etcd_io.bbolt.Mmap.Infra"),
    (r"errMaxSizeOk \(GF := GF\) \(hG := hG\)",
     "_root_.Perennial.EtcdGrove.bbolt.errMaxSizeOk_holds", None, "Proof.go_etcd_io.bbolt.Mmap.Infra"),
    (r"pagePoolNew \(GF := GF\) \(hG := hG\)",
     "_root_.Perennial.EtcdGrove.bbolt.pagePoolNew_holds", None, "Proof.go_etcd_io.bbolt.Mmap.Infra"),
    # `Open/PageSize.errInvalidStr` is `Mmap/Infra.errInvalid_errorString`'s statement
    (r"errInvalidStr \(GF := GF\) \(hG := hG\)",
     "_root_.Perennial.EtcdGrove.bbolt.errInvalid_errorString", None,
     "Proof.go_etcd_io.bbolt.Mmap.Infra"),
    (r"TxExclWGap \(GF := GF\)", "_root_.Perennial.EtcdGrove.bbolt.txExclWGap_holds", None,
     "Proof.go_etcd_io.bbolt.Tx__Rollback"),
    # `sort.Sort` for any `Less`: the trust-boundary axiom the server's `lessor.Leases` takes too
    (r"sort\.«Sort»\.anyLessSpec \(GF := GF\) \(hG := hG\)",
     "_root_.Perennial.EtcdGrove.sort.«Sort».wp_anyLess", None, "Proof.sort.SortAnyLess"),
    # `delete` at `pidSet` (a defined map type) unfolds as at its underlying type: a gap of
    # Perennial's semantics (`internal/freelist/Lemmas/HashDelete.lean`), not provable here
    (r"PidSetDeleteUnfold \(GF := GF\)", None, "PidSetDeleteUnfold",
     "Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.HashDelete"),
    # the freelist implementations' contracts, from the callees they rest on (`FLCallees`)
    (r"∀ \(I : FLImpl \(GF := GF\)\) a, I\.IsImpl a → I\.FreeCountSpec",
     "(fun I a h => (_root_.Perennial.EtcdGrove.bbolt.internal.freelist.impl_contract {fc} I a h).freeCount)",
     None, "Proof.go_etcd_io.bbolt.internal.freelist.Impl.Impls"),
    (r"∀ \(I : FLImpl \(GF := GF\)\) a, I\.IsImpl a → I\.FreePageIdsSpec",
     "(fun I a h => (_root_.Perennial.EtcdGrove.bbolt.internal.freelist.impl_contract {fc} I a h).freePageIds)",
     None, "Proof.go_etcd_io.bbolt.internal.freelist.Impl.Impls"),
    (r"∀ \(I : FLImpl \(GF := GF\)\) a, I\.IsImpl a → I\.InitSpec",
     "(fun I a h => (_root_.Perennial.EtcdGrove.bbolt.internal.freelist.impl_contract {fc} I a h).init)",
     None, "Proof.go_etcd_io.bbolt.internal.freelist.Impl.Impls"),
    (r"∀ \(I : FLImpl \(GF := GF\)\) a, I\.IsImpl a → I\.MergeSpansSpec",
     "(fun I a h => (_root_.Perennial.EtcdGrove.bbolt.internal.freelist.impl_contract {fc} I a h).mergeSpans)",
     None, "Proof.go_etcd_io.bbolt.internal.freelist.Impl.Impls"),
    (r"∀ \(I : FLImpl \(GF := GF\)\) a, I\.IsImpl a → I\.AllocateSpec",
     "(_root_.Perennial.EtcdGrove.bbolt.internal.freelist.impl_allocate {fc})",
     None, "Proof.go_etcd_io.bbolt.internal.freelist.Impl.Impls"),
]
# The freelist implementations' callees (`internal.freelist.FLCallees`, its fields in order).
FL_CALLEES = [
    "Perennial.EtcdGrove.bbolt.internal.common.Verify.spec",
    "Perennial.EtcdGrove.bbolt.internal.common.Pgids.Merge.spec",
    "Perennial.EtcdGrove.sort.SliceIsSorted.spec",
    "Perennial.EtcdGrove.reflect.DeepEqual.spec_pgidSet",
    "PidSetDeleteUnfold",
]
FL_CALLEES_PREMISE = {"PidSetDeleteUnfold": "Perennial.EtcdGrove.bbolt.PidSetDeleteUnfold (GF := GF)"}
# The shared trust boundaries of this repository whose Links other Links import (`@` callees).
SHARED_LINKS = ["Proof.fmt.Link", "Proof.context.Link"]
# The project directories of `Spec/` and `Proof/` not scanned for a callee's spec (the
# standard-library and `golang.org/x` packages are; bbolt's tree is, besides).
PROJECT_DIRS = {"go_etcd_io", "github_com", "k8s_io", "google_golang_org", "go_uber_org",
                "go_opentelemetry_io"}


def strip_comments(s):
    out, i, depth, n = [], 0, 0, len(s)
    while i < n:
        if s.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and s.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            if s[i] == "\n":
                out.append("\n")
            i += 1
        elif s.startswith("--", i):
            j = s.find("\n", i)
            if j < 0:
                break
            i = j
        else:
            out.append(s[i])
            i += 1
    return "".join(out)


def split_decl(s, start):
    """The binders (top-level bracket groups before the statement's colon) and the statement of
    the declaration whose name ends at `start`."""
    depth, i, parts, cur, concl_start = 0, start, [], "", None
    while i < len(s):
        ch = s[i]
        if depth == 0 and s.startswith(":=", i):
            break
        if depth == 0 and re.match(r"\n(theorem|axiom|def|abbrev|end|section|namespace|@\[|omit|"
                                   r"variable|open|set_option|private|noncomputable|instance)\b",
                                   s[i:i + 16]):
            break
        if ch in "([{⦃":
            if depth == 0 and concl_start is None:
                cur = ""
            depth += 1
            cur += ch
        elif ch in ")]}⦄":
            depth -= 1
            cur += ch
            if depth == 0 and concl_start is None:
                parts.append(" ".join(cur.split()))
                cur = ""
        elif depth == 0 and ch == ":" and concl_start is None:
            concl_start = i + 1
        else:
            cur += ch
        i += 1
    concl = " ".join(s[concl_start:i].split()) if concl_start else ""
    return parts, concl


DECL = re.compile(r"^(namespace|section|end|(?:@\[[^\]]*\]\s*)?(?:private\s+)?(?:noncomputable\s+)?"
                  r"(theorem|axiom|abbrev|def))\b ?([^\s(\[{:]*)", re.M)


def scan_file(path, mod, out, want_all):
    s = strip_comments(open(path, encoding="utf-8").read())
    stack = []
    for m in DECL.finditer(s):
        kw, name = m.group(1), m.group(3)
        if kw == "namespace":
            stack.extend(("ns", c) for c in name.split("."))
        elif kw == "section":
            stack.append(("sec", name))
        elif kw == "end":
            if stack:
                k = len(name.split(".")) if name and stack[-1][0] == "ns" else 1
                del stack[len(stack) - k:]
        else:
            kind = m.group(2)
            ns = ".".join(c for t, c in stack if t == "ns")
            full = name[len("_root_."):] if name.startswith("_root_.") else (
                f"{ns}.{name}" if ns else name)
            is_spec = kind in ("abbrev", "def") and re.search(r"\.spec[\w']*$", full)
            if not (is_spec or (kind in ("theorem", "axiom") and (want_all or re.search(
                    r"\.wp_proof[\w']*$", full)))):
                continue
            parts, concl = split_decl(s, m.end())
            out.append(dict(mod=mod, kind=kind, name=full, ns=ns, hyps=parts, concl=concl))


def scan(root, perennial):
    decls = []

    def walk(base, prefix, dirs_ok, want_all, only_link=False):
        for dp, dns, fs in os.walk(base):
            rel = os.path.relpath(dp, base)
            top = rel.split(os.sep)[0]
            if rel != "." and not dirs_ok(rel):
                dns[:] = []
                continue
            for f in sorted(fs):
                if not f.endswith(".lean") or (only_link and f != "Link.lean"):
                    continue
                p = os.path.join(dp, f)
                mod = prefix + os.path.relpath(p, base)[:-5].replace(os.sep, ".")
                scan_file(p, mod, decls, want_all or f == "Link.lean")

    def std(rel):
        parts = rel.split(os.sep)
        pkg = PKG.split("/")
        return (parts[0] not in PROJECT_DIRS or parts[:len(pkg)] == pkg
                or parts == pkg[:len(parts)])

    walk(os.path.join(root, "Spec"), "Spec.", std, False)
    walk(os.path.join(root, "Proof"), "Proof.", std, False)
    # the premises' terms are theorems of bbolt's tree (`errnoErrOk_holds`)
    walk(os.path.join(root, "Proof", *PKG.split("/")), "Proof.go_etcd_io.bbolt.", lambda r: True,
         True)
    walk(os.path.join(perennial, "Perennial", "Spec"), "Perennial.Spec.", lambda r: True, False)
    walk(os.path.join(perennial, "Perennial", "Proof"), "Perennial.Proof.", lambda r: True, True,
         only_link=True)
    return decls


def main(root, perennial, argv0, results_file=False):
    decls = scan(root, perennial)
    specs = {}
    for x in decls:
        if x["kind"] in ("abbrev", "def") and re.search(r"\.spec[\w']*$", x["name"]):
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

    SPEC_TY = re.compile(r"(∀ \[ExtSemantics fsExt\] \[FsSemOk\] \[HasExt fsExt\],\s*)?([\w.«»']+\.spec[\w']*)"
                         r"( \(GF := GF\))?( \(hG := hG\))?")

    def concl_spec(x):
        m = SPEC_TY.fullmatch(x["concl"])
        return resolve(m.group(2), x["ns"]) if m and not m.group(1) else None

    # the linked results of Perennial and of the shared trust boundaries: spec -> term
    linked = {}
    for x in decls:
        if x["mod"].endswith(".Link") and x["kind"] == "theorem" and (
                x["mod"].startswith("Perennial.Proof.") or x["mod"] in SHARED_LINKS):
            s = concl_spec(x)
            if s and s not in linked:
                linked[s] = ("_root_." + x["name"], x["mod"])

    def classify(h, ns):
        """A binder: ('skip',) | ('spec', name) | ('premise', index) | ('bad', text)."""
        if h.startswith("{") or h.startswith("⦃"):
            return ("skip",)
        if h.startswith("["):
            return ("skip",)
        m = re.match(r"\(\s*[\w']+(?:\s+[\w']+)*\s*:\s*(.*)\)$", h)
        if not m:
            return ("bad", h)
        ty = m.group(1)
        sm = SPEC_TY.fullmatch(ty)
        if sm:
            r = resolve(sm.group(2), ns)
            return ("spec", r) if r else ("bad", h)
        for i, (pat, _, _, _) in enumerate(PREMISES):
            if re.fullmatch(pat, ty):
                return ("premise", i)
        return ("bad", h)

    # bbolt's proofs of specs: spec -> the chosen proof
    cands = {}
    for x in decls:
        if not x["mod"].startswith("Proof.go_etcd_io.bbolt.") or x["kind"] not in ("theorem", "axiom"):
            continue
        if x["mod"].endswith((".Link", ".Results")):
            continue  # this generator's own output (its results are not proofs to link)
        s = concl_spec(x)
        if not s:
            continue
        if x["kind"] == "axiom" and re.search(r"_kv[rw]?\.spec$", s):
            continue  # the backend's legacy `_kv` axioms, not bbolt's results (the backend switch)
        bs = [classify(h, x["ns"]) for h in x["hyps"]]
        if any(b[0] == "bad" for b in bs):
            continue  # a lemma generic in more than callees (`shared`'s methods)
        x["binders"] = [b for b in bs if b[0] != "skip"]
        cands.setdefault(s, []).append(x)

    def pick(s, xs):
        base, suf = re.match(r"(.*)\.spec([\w']*)$", s).groups()
        named = [x for x in xs if x["name"] == f"{base}.wp_proof{suf}"]
        return named[0] if named else min(xs, key=lambda x: (len(x["binders"]), x["name"]))

    proofs = {s: pick(s, xs) for s, xs in cands.items()}

    # etcd-grove's own proofs of the external callees (the file-system model's): linked here
    ext_proofs = {}
    for x in decls:
        if x["mod"].startswith("Proof.") and not x["mod"].startswith("Proof.go_etcd_io.bbolt.") \
                and not x["mod"].endswith(".Link") and x["kind"] in ("theorem", "axiom") \
                and re.search(r"\.wp_proof[\w']*$", x["name"]):
            s = concl_spec(x)
            if s and s not in ext_proofs:
                bs = [classify(h, x["ns"]) for h in x["hyps"]]
                if not any(b[0] == "bad" for b in bs):
                    x["binders"] = [b for b in bs if b[0] != "skip"]
                    ext_proofs[s] = x

    # what each spec is given: ('result', proof) emitted here, ('linked', term, module), or
    # ('pending',) a hypothesis
    how = {}

    def visit(s):
        if s in how:
            return
        if s in proofs:
            how[s] = ("result", proofs[s])
        elif s in linked:
            how[s] = ("linked",) + linked[s]
            return
        elif s in ext_proofs:
            how[s] = ("result", ext_proofs[s])
        else:
            how[s] = ("pending",)
            return
        for b in how[s][1]["binders"]:
            if b[0] == "spec":
                visit(b[1])
            elif b[0] == "premise" and "{fc}" in (PREMISES[b[1]][1] or ""):
                for c in FL_CALLEES:
                    if c in specs:
                        visit(c)

    for s in sorted(proofs):
        visit(s)

    def short(s):
        """`Perennial.EtcdGrove.bbolt.a.T.M.spec<S>` -> `a.T.wp_M<S>`, relative to `EtcdGrove.bbolt`
        (an external spec `Perennial.EtcdGrove.os.File.Close.spec` -> `os.File.wp_Close`)."""
        base, suf = re.match(r"(.*)\.spec([\w']*)$", s).groups()
        for p in (NS + ".", "Perennial.EtcdGrove.", "Perennial."):
            if base.startswith(p):
                base = base[len(p):]
                break
        *q, last = base.split(".")
        return ".".join(q + [f"wp_{last.strip('«»')}{suf}"])

    def hyp_name(s):
        """A pending spec's hypothesis: `h_<T>_<M><S>` (`h_sort_SliceIsSorted`)."""
        base, suf = re.match(r"(.*)\.spec([\w']*)$", s).groups()
        for p in (NS + ".", "Perennial.EtcdGrove.", "Perennial."):
            if base.startswith(p):
                base = base[len(p):]
                break
        return "h_" + base.replace(".", "_").replace("«", "").replace("»", "") + suf

    # the pending hypotheses: specs with no proof, premises with no term
    pending = sorted(s for s, h in how.items() if h[0] == "pending")
    pending_premises = []
    uses_fc = False
    for s, h in how.items():
        if h[0] != "result":
            continue
        for b in h[1]["binders"]:
            if b[0] == "premise":
                pat, term, hn, _ = PREMISES[b[1]]
                if term is None and hn not in pending_premises:
                    pending_premises.append(hn)
                if term and "{fc}" in term:
                    uses_fc = True
    if uses_fc:
        for c in FL_CALLEES:
            if c in FL_CALLEES_PREMISE and c not in pending_premises:
                pending_premises.append(c)
    hyps = [(hyp_name(s), f"_root_.{s} (GF := GF) (hG := hG)") for s in pending] + \
        [("h_" + p, "_root_." + FL_CALLEES_PREMISE.get(p, next(
            "Perennial.EtcdGrove.bbolt." + p + " (GF := GF)" for pat, t, hn, _ in PREMISES
            if hn == p))) for p in sorted(pending_premises)]
    hyp_names = [n for n, _ in hyps]

    # blocked: the results reaching a pending hypothesis
    blocked = set()

    def reaches(s, memo={}):
        if s in memo:
            return memo[s]
        memo[s] = False
        h = how[s]
        r = h[0] == "pending"
        if h[0] == "result":
            for b in h[1]["binders"]:
                if b[0] == "spec" and reaches(b[1]):
                    r = True
                if b[0] == "premise":
                    pat, term, _, _ = PREMISES[b[1]]
                    if term is None or "{fc}" in term:
                        r = True
        memo[s] = r
        return r

    order, seen = [], set()

    def topo(s):
        if s in seen:
            return
        seen.add(s)
        h = how[s]
        if h[0] == "result":
            for b in h[1]["binders"]:
                if b[0] == "spec":
                    topo(b[1])
                elif b[0] == "premise" and "{fc}" in (PREMISES[b[1]][1] or ""):
                    for c in FL_CALLEES:
                        if c in how:
                            topo(c)
            order.append(s)

    for s in sorted(how):
        topo(s)
    blocked = {s for s in order if reaches(s)}

    def term_of(s):
        h = how[s]
        if h[0] == "linked":
            return h[1]
        if h[0] == "pending":
            return hyp_name(s)
        r = f"_root_.{NS}.{short(s)}"
        return f"({r} {' '.join(hyp_names)})" if s in blocked else r

    fc_term = None
    if uses_fc:
        fc_args = [term_of(c) if c in how else "h_" + c for c in FL_CALLEES]
        fc_term = "⟨" + ", ".join(fc_args) + "⟩"

    def arg(b):
        if b[0] == "spec":
            return term_of(b[1])
        pat, term, hn, _ = PREMISES[b[1]]
        if term is None:
            return "h_" + hn
        return term.replace("{fc}", f"(_root_.{NS}.freelistCallees {' '.join(hyp_names)})")

    def emit(s):
        x = how[s][1]
        args = " ".join(arg(b) for b in x["binders"])
        return (f"theorem {short(s)} :\n    _root_.{s} (GF := GF) (hG := hG) :=\n"
                f"  _root_.{x['name']}" + (f" {args}" if args else "") + "\n")

    results = [s for s in order]
    names = [short(s) for s in results]
    dup = {n for n in names if names.count(n) > 1}
    if dup:
        sys.exit(f"gen-link.py --bbolt: two results named {sorted(dup)}")

    imports = set()
    for s in results:
        imports.add(how[s][1]["mod"])
    for s, h in how.items():
        if h[0] == "linked":
            imports.add(h[2])
        if h[0] == "pending":
            imports.add(specs[s]["mod"])
        if h[0] == "result":
            for b in h[1]["binders"]:
                if b[0] == "premise":
                    imports.add(PREMISES[b[1]][3])

    def mod_key(m):
        return (not m.startswith("Proof.go_etcd_io.bbolt."), m)

    generic = [s for s in results if s not in blocked]
    later = [s for s in results if s in blocked]
    header = """/-
bbolt's proofs (`go.etcd.io/bbolt` and its `internal/common` and `internal/freelist`), every proof
instantiated with its callees' results, and the results of etcd-grove's own proofs of the
standard-library functions they call (the file-system model's, `Proof/os/`, `Proof/syscall/`, ...).
The callees are read off each proof's binders (`etc/link_bbolt.py`'s docstring). Generated by
`etc/gen-link.py --bbolt` -- do not edit by hand.

`#print axioms` on a result is its trust base (`Results.lean` prints the public specs').
""" + textwrap.fill("The results reaching a spec with no proof, or a premise with no proof, are "
                    "in `links_pending`, which takes them as hypotheses: "
                    + ", ".join(f"`{n}`" for n in hyp_names) + ".", 96,
                    break_on_hyphens=False) + "\n-/"
    out = [header, "module", ""]
    out.extend(f"public import {m}" for m in sorted(imports, key=mod_key))
    sec_vars = """variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions]
"""
    out.append("""
@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs
open Iris Iris.BI

section links
""" + sec_vars)
    out.extend(emit(s) for s in generic)
    out.append("end links\n")
    if later or uses_fc:
        out.append("""/-! The results that reach a spec or premise with no proof: each takes them as hypotheses
(`h_<name>`). -/
section links_pending
""" + sec_vars + "\n".join(f"variable ({n} : {t})" for n, t in hyps) + f"""
include {' '.join(hyp_names)}
""")
        if uses_fc:
            out.append("/-- The callees the freelist implementations' contracts rest on. -/\n"
                       "theorem freelistCallees :\n"
                       "    _root_.Perennial.EtcdGrove.bbolt.internal.freelist.FLCallees "
                       "(GF := GF) (hG := hG) :=\n"
                       f"  {fc_term}\n")
        out.extend(emit(s) for s in later)
        out.append("end links_pending\n")
    out.append("end bbolt\nend EtcdGrove\nend Perennial")
    if results_file:
        # the public specs: those of the importable `Spec` modules (`etc/api/bbolt.txt`)
        api = open(os.path.join(root, "etc", "api", "bbolt.txt")).read()
        public = set(re.findall(r"^importable (Spec\.\S+)", api, re.M)) - set(
            re.findall(r"^vocab (\S+)", api, re.M))
        pub = [s for s in results if specs.get(s, {}).get("mod") in public]
        print(f"""/-
The trust base of bbolt's public results: `#print axioms` of the result of every spec of an
importable `Spec` module (`etc/api/bbolt.txt`), as `Link.lean` states it. Generated by
`etc/gen-link.py --bbolt --results` -- do not edit by hand. Built with the rest; read its output
to check it. The results of `links_pending` take its hypotheses (`Link.lean`'s header), which
`#print axioms` does not show. The `_kv` specs of etcd's backend are not here: they are still the
backend's axioms, until the backend switch derives them from these results.
-/
module

public import Proof.go_etcd_io.bbolt.Link

@[expose] public section

-- `#print axioms` prints the axioms by their full names (shortening them is slow).
set_option pp.fullNames true
""")
        print("\n".join(f"#print axioms {NS}.{short(s)}" for s in sorted(pub, key=short)))
        return
    print("\n".join(out))
    unlinked = sorted(s for s in specs if s.startswith(NS + ".") and s not in proofs
                      and specs[s]["mod"].startswith(("Spec.go_etcd_io.bbolt", "Proof.go_etcd_io.bbolt")))
    if unlinked:
        print("gen-link.py --bbolt: specs with no linked proof: " + ", ".join(unlinked),
              file=sys.stderr)
