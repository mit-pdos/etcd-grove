#!/usr/bin/env python3
"""Generate `Proof/k8s_io/api/Deep.lean`: the deep values of the Kubernetes API objects the model
API server stores (pods, nodes, daemon sets, controller revisions) and their deep ownership.

usage: etc/gen-k8s-deep.py            write the file
       etc/gen-k8s-deep.py --check    exit 1 if the file differs from what would be generated

An API object is a tree of Go values: structs inline, and pointers, slices and maps to more of
them. Its *deep value* forgets the locations: for every struct type `S` reachable from the roots
(`ROOTS`) a Lean structure `kd.<pkg>.S` with one field per Go field (the Goose projection's name),
whose type is the field's deep value:

  * a basic value (string, integers, bool, a named type of one, `metav1.Time`, `time.Time`): the
    Goose value itself, owned as `⌜v = d⌝` (a `time.Time`'s `*Location` is shared, not owned, as
    the generated `DeepCopy` shares it);
  * a struct: its `kd` structure, owned field by field;
  * a pointer: `Option` of the target's deep value (`ownPtrD`: `none` is `nil`);
  * a slice: `List` of the elements' deep values (`ownSliceD`; nil-ness is not kept);
  * a map with basic keys and values: `Option (GMap K V)` (`ownMapD`: `none` is `nil`; a
    `DeepCopy` keeps nil-ness, and the model reads `Annotations == nil`);
  * an interface (`RawExtension.Object`): `Unit`, owned only if `nil` (`ownNilIfaceD`);
  * an axiomatized Goose type (`intstr.IntOrString`, gap C5; `resource.infDecAmount`), or a struct
    holding one inline (`resource.Quantity`, `HTTPGetAction`, ...), is *opaque*: its typed
    points-to is the translation's `sorry`, so it is never owned. A pointer to one is
    `Option Unit` (`ownOpaquePtrD`: only whether it is `nil`); a slice of one or a map to one is
    `Unit`, owned only if `nil` (`ownNilSliceD`, `ownNilMapD`).

`kd.<pkg>.S.own v dq d` is the deep ownership of the Go value `v : S` at fraction `dq`, with deep
value `d`; `kd.<pkg>.S.zero` is the zero value's deep value and `kd.<pkg>.S.own_zero` proves it.
The restrictions (opaque values nil) are what the specs require of the objects they store; the
generated `DeepCopy` keeps them. The combinators are in `Proof/k8s_io/api/DeepBase.lean`.
"""
import os, re, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(ROOT, "Proof", "k8s_io", "api", "Deep.lean")
CODE = os.path.join(ROOT, "Code")

ROOTS = ["k8s_io.api.core.v1.Pod", "k8s_io.api.core.v1.Node", "k8s_io.api.apps.v1.DaemonSet",
         "k8s_io.api.apps.v1.ControllerRevision",
         # the request options the model reads (by value, with what their pointers reach)
         "k8s_io.apimachinery.pkg.apis.«meta».v1.ListOptions",
         "k8s_io.apimachinery.pkg.apis.«meta».v1.DeleteOptions"]
# The packages whose types are scanned (Lean namespace -> short tag of the deep values' namespace).
PKGS = {
    "k8s_io.api.core.v1": "core",
    "k8s_io.api.apps.v1": "apps",
    "k8s_io.apimachinery.pkg.apis.«meta».v1": "meta",
    "k8s_io.apimachinery.pkg.api.resource": "resource",
    "k8s_io.apimachinery.pkg.util.intstr": "intstr",
    "k8s_io.apimachinery.pkg.runtime": "runtime",
    "k8s_io.apimachinery.pkg.types": "types",
}
# Named types kept as basic values though they are structs (no owned pointers; see the header).
BASE_STRUCTS = {"k8s_io.apimachinery.pkg.apis.«meta».v1.Time",
                "k8s_io.apimachinery.pkg.apis.«meta».v1.MicroTime"}
BASIC = {"go.string": "GoString", "go.bool": "Bool", "go.int": "w64", "go.int64": "w64",
         "go.int32": "w32", "go.int16": "w16", "go.int8": "w8", "go.uint": "w64",
         "go.uint64": "w64", "go.uint32": "w32", "go.uint16": "w16", "go.uint8": "w8",
         "go.byte": "w8"}
PERENNIAL_BASE = {"_root_.Perennial.time.Time.ty": "_root_.Perennial.time.Time"}


def die(msg):
    sys.exit("gen-k8s-deep: " + msg)


# ---------------------------------------------------------------------------------------------
# Scanning the translation

structs = {}   # qualified name -> list of (projection, go type text)
abbrevs = {}   # qualified name -> go underlying type text (named non-struct types)
axioms = set() # qualified names of axiomatized types


def lean_files():
    for ns in PKGS:
        rel = ns.replace("«", "").replace("»", "").replace(".", "/")
        base = os.path.join(CODE, rel)
        if os.path.isfile(base + ".lean"):
            yield ns, base + ".lean"
        if os.path.isdir(base):
            for f in sorted(os.listdir(base)):
                if re.match(r"chunk\d+\.lean$", f):
                    yield ns, os.path.join(base, f)


def split_list(s):
    """Split a Lean list literal's body at top-level commas."""
    out, depth, cur = [], 0, ""
    for c in s:
        if c in "([":
            depth += 1
        elif c in ")]":
            depth -= 1
        if c == "," and depth == 0:
            out.append(cur.strip())
            cur = ""
        else:
            cur += c
    if cur.strip():
        out.append(cur.strip())
    return out


for ns, path in lean_files():
    text = open(path, encoding="utf-8").read()
    for m in re.finditer(r"^@\[reducible\] noncomputable def (\w+)\.fieldsUnsealed \[FfiSyntax\] "
                         r"\[GoGlobalContext\] : List go\.field_decl :=\n  \[(.*?)\]\n\n", text,
                         re.M | re.S):
        name, body = m.group(1), m.group(2)
        fs = []
        for item in split_list(body.replace("\n", " ")):
            fm = re.match(r'\(go\.field_decl\.(?:FieldDecl|EmbeddedField) go!"(\w+)" (.*)\)$', item)
            if not fm:
                die(f"{path}: cannot parse field {item!r} of {name}")
            fs.append((fm.group(1), fm.group(2).strip()))
        structs[ns + "." + name] = fs
    for m in re.finditer(r"^@\[reducible\] noncomputable def (\w+)\.underlying \[FfiSyntax\] "
                         r"\[GoGlobalContext\] : go\.GoType :=\n  (.*)$", text, re.M):
        if not m.group(2).startswith("(go.GoType.StructType"):
            abbrevs[ns + "." + m.group(1)] = m.group(2).strip()
    for m in re.finditer(r"^axiom (\w+) : Type$", text, re.M):
        axioms.add(ns + "." + m.group(1))


# ---------------------------------------------------------------------------------------------
# Go types

def parse_type(s, ns):
    """A Go type expression of the translation, as a tuple."""
    s = s.strip()
    if s.startswith("(") and s.endswith(")"):
        inner = s[1:-1].strip()
        for ctor, n in (("go.GoType.PointerType ", 1), ("go.GoType.SliceType ", 1),
                        ("go.GoType.MapType ", 2)):
            if inner.startswith(ctor):
                args = split_args(inner[len(ctor):])
                if len(args) != n:
                    die(f"bad type {s}")
                kind = ctor.split(".")[2].strip()
                return (kind,) + tuple(parse_type(a, ns) for a in args)
        if inner.startswith("go.GoType.InterfaceType"):
            return ("Iface",)
        die(f"unsupported type {s}")
    if s in BASIC:
        return ("Basic", BASIC[s])
    if s in PERENNIAL_BASE:
        return ("Base", PERENNIAL_BASE[s])
    m = re.match(r"(?:_root_\.Perennial\.)?([\w.«»]+)\.ty$", s)
    if m:
        q = m.group(1)
        if not q.startswith("k8s_io"):
            q = ns + "." + q
        return ("Named", q)
    die(f"unsupported type {s}")


def split_args(s):
    out, depth, cur = [], 0, ""
    for c in s:
        if c in "([":
            depth += 1
        elif c in ")]":
            depth -= 1
        if c == " " and depth == 0:
            if cur:
                out.append(cur)
            cur = ""
        else:
            cur += c
    if cur:
        out.append(cur)
    return out


def ns_of(q):
    return q.rsplit(".", 1)[0]


def lean_name(q):
    return "_root_.Perennial." + q


def kd_name(q):
    ns, n = q.rsplit(".", 1)
    if ns not in PKGS:
        die(f"type {q} of an unscanned package")
    return f"kd.{PKGS[ns]}.{n}"


def lean_ty(t):
    """The Lean type of the Goose values of Go type t."""
    k = t[0]
    if k in ("Basic", "Base"):
        return t[1]
    if k == "Named":
        return lean_name(t[1])
    return {"PointerType": "Loc", "SliceType": "GoSlice", "MapType": "GoMap",
            "Iface": "GoInterface"}[k]


opaque_memo = {}


def opaque(q):
    """A named type whose Goose values cannot be owned (axiomatized, or holding one inline)."""
    if q in opaque_memo:
        return opaque_memo[q]
    opaque_memo[q] = False
    r = False
    if q in axioms:
        r = True
    elif q in structs and q not in BASE_STRUCTS:
        for _, ft in structs[q]:
            t = parse_type(ft, ns_of(q))
            if inline_opaque(t):
                r = True
    elif q in abbrevs:
        t = parse_type(abbrevs[q], ns_of(q))
        r = inline_opaque(t)
    elif q not in structs:
        die(f"unknown type {q}")
    opaque_memo[q] = r
    return r


def inline_opaque(t):
    return t[0] == "Named" and opaque(t[1])


def resolve(t):
    """A named non-struct type's underlying type (named basic types stay named, as basic)."""
    while t[0] == "Named" and t[1] in abbrevs and t[1] not in structs:
        u = parse_type(abbrevs[t[1]], ns_of(t[1]))
        if u[0] in ("Basic", "Base"):
            return ("Basic", lean_name(t[1]))
        if u[0] == "Iface":
            return ("Iface",)
        t = u
    return t


def is_basic(t):
    t = resolve(t)
    return t[0] in ("Basic", "Base") or (t[0] == "Named" and t[1] in BASE_STRUCTS)


used = []      # struct names in dependency order
state = {}


def visit(q):
    if state.get(q) == "done":
        return
    if state.get(q) == "active":
        die(f"recursive type {q}")
    state[q] = "active"
    for _, ft in structs[q]:
        visit_type(parse_type(ft, ns_of(q)))
    state[q] = "done"
    used.append(q)


def visit_type(t):
    t = resolve(t)
    k = t[0]
    if k == "Named":
        q = t[1]
        if q in BASE_STRUCTS or opaque(q):
            return
        if q not in structs:
            die(f"unknown named type {q}")
        visit(q)
    elif k == "PointerType" or k == "SliceType":
        visit_type(t[1])
    elif k == "MapType":
        visit_type(t[1])
        visit_type(t[2])


def dty(t):
    """The deep value type of Go type t."""
    if is_basic(t):
        r = resolve(t)
        return lean_name(r[1]) if r[0] == "Named" else r[1]
    t = resolve(t)
    k = t[0]
    if k == "Named":
        if opaque(t[1]):
            return "Unit"
        return kd_name(t[1])
    if k == "PointerType":
        if inline_opaque(resolve(t[1])):
            return "Option Unit"
        return f"Option ({dty(t[1])})"
    if k == "SliceType":
        if inline_opaque(resolve(t[1])):
            return "Unit"
        return f"List ({dty(t[1])})"
    if k == "MapType":
        if inline_opaque(resolve(t[2])):
            return "Unit"
        if not is_basic(t[1]) or not is_basic(t[2]):
            die(f"map with non-basic key or value {t}")
        return f"Option (GMap ({dty(t[1])}) ({dty(t[2])}))"
    if k == "Iface":
        return "Unit"
    die(f"dty {t}")


def inner(t):
    """The ownership function `V → DFrac → E → IProp GF` of Go type t's values."""
    if is_basic(t):
        return "ownBaseD"
    t = resolve(t)
    k = t[0]
    if k == "Named":
        return f"{kd_name(t[1])}.own"
    if k == "PointerType":
        if inline_opaque(resolve(t[1])):
            return "(fun x _ e => ownOpaquePtrD x e)"
        return f"(ownPtrD (V := {lean_ty(resolve(t[1]))}) {inner(t[1])})"
    if k == "SliceType":
        if inline_opaque(resolve(t[1])):
            return "(fun x _ _ => ownNilSliceD x)"
        return f"(ownSliceD (V := {lean_ty(resolve(t[1]))}) {inner(t[1])})"
    if k == "MapType":
        if inline_opaque(resolve(t[2])):
            return "(fun x _ _ => ownNilMapD x)"
        return f"(ownMapD (K := {dty(t[1])}) (V := {dty(t[2])}))"
    if k == "Iface":
        return "(fun x _ _ => ownNilIfaceD x)"
    die(f"inner {t}")


def own_field(t, v, d):
    """The ownership of a field (value v, deep value d), at fraction dq, and the tactic proving it
    of the zero value's field."""
    if is_basic(t):
        return f"⌜{v} = {d}⌝", "ipureintro; rfl"
    r = resolve(t)
    k = r[0]
    if k == "Named":
        if opaque(r[1]):
            return "True", "itrivial"
        return f"{kd_name(r[1])}.own {v} dq {d}", f"iapply ({kd_name(r[1])}.own_zero_of _ (by rfl) dq)"
    if k == "PointerType" and inline_opaque(resolve(r[1])):
        return f"ownOpaquePtrD {v} {d}", "iapply (ownOpaquePtrD_none_of _ (by rfl))"
    if k == "PointerType":
        return f"{inner(t)} {v} dq {d}", "iapply (ownPtrD_none_of _ _ (by rfl) dq)"
    if k == "SliceType" and inline_opaque(resolve(r[1])):
        return f"ownNilSliceD {v}", "iapply (ownNilSliceD_of _ (by rfl))"
    if k == "SliceType":
        return f"{inner(t)} {v} dq {d}", "iapply (ownSliceD_nil_of _ _ (by rfl) dq)"
    if k == "MapType" and inline_opaque(resolve(r[2])):
        return f"ownNilMapD {v}", "iapply (ownNilMapD_of _ (by rfl))"
    if k == "MapType":
        return f"{inner(t)} {v} dq {d}", "iapply (ownMapD_none_of _ (by rfl) dq)"
    if k == "Iface":
        return f"ownNilIfaceD {v}", "iapply (ownNilIfaceD_of _ (by rfl))"
    die(f"own_field {t}")


def zero_of(t):
    if is_basic(t):
        r = resolve(t)
        ty = lean_name(r[1]) if r[0] == "Named" else r[1]
        return f"(zero_val {ty})"
    t = resolve(t)
    k = t[0]
    if k == "Named":
        return "()" if opaque(t[1]) else f"{kd_name(t[1])}.zero"
    if k == "PointerType":
        return "none"
    if k == "SliceType":
        return "()" if inline_opaque(resolve(t[1])) else "[]"
    if k == "MapType":
        return "()" if inline_opaque(resolve(t[2])) else "none"
    if k == "Iface":
        return "()"
    die(f"zero {t}")


for r in ROOTS:
    if opaque(r):
        die(f"root {r} is opaque")
    visit(r)

# ---------------------------------------------------------------------------------------------
# Output

HEADER = '''/-
GENERATED by `etc/gen-k8s-deep.py` from the Goose translation of `k8s.io/api` and apimachinery;
do not edit. **The deep values of the API objects the model API server stores, and their deep
ownership** (see the script's documentation). Lean-first (no Rocq counterpart).

Roots: {roots}. {n} struct types.
-/
module

public import Proof.k8s_io.api.DeepBase

@[expose] public section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

'''


def gen():
    out = [HEADER.format(roots=", ".join("`" + r.split(".")[-1] + "`" for r in ROOTS), n=len(used))]
    out.append("/-! ## The deep values -/\n")
    out.append("section values\nvariable [FfiSyntax]\n")
    for q in used:
        n = kd_name(q)
        fs = [(p, parse_type(ft, ns_of(q))) for p, ft in structs[q]]
        out.append(f"/-- The deep value of `{q.split('.')[-1]}` (`{ns_of(q)}`). -/")
        out.append(f"structure {n} where")
        out.append("  mk ::")
        for p, t in fs:
            out.append(f"  {p}' : {dty(t)}")
        out.append("")
        enc = ", ".join(f"Pos.Countable.encode x.{p}'" for p, _ in fs)
        unit = [dty(t) == "Unit" for _, t in fs]
        pats = ", ".join("⟨⟩" if u else f"a{i}" for i, u in enumerate(unit))
        patb = ", ".join("⟨⟩" if u else f"b{i}" for i, u in enumerate(unit))
        k = unit.count(False)
        out.append(f"instance {n}.countable : Pos.Countable {n} :=")
        out.append(f"  .ofInjective (fun x => Pos.Countable.encode ([{enc}] : List Pos)) (by")
        out.append(f"    rintro ⟨{pats}⟩ ⟨{patb}⟩ h")
        out.append(f"    simp only [Pos.encode_eq_iff, List.cons.injEq, and_true, true_and] at h")
        if k == 0:
            out.append(f"    rfl)")
        elif k == 1:
            out.append(f"    subst h; rfl)")
        else:
            out.append(f"    obtain ⟨{', '.join('rfl' for _ in range(k))}⟩ := h")
            out.append(f"    rfl)")
        out.append("")
        zs = ", ".join(zero_of(t) for _, t in fs)
        out.append(f"/-- The deep value of the zero `{q.split('.')[-1]}`. -/")
        out.append(f"def {n}.zero : {n} := ⟨{zs}⟩")
        out.append("")
    out.append("end values\n")
    out.append("/-! ## Deep ownership -/\n")
    out.append("section own")
    out.append("variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]")
    out.append("variable [go_gctx : GoGlobalContext]")
    out.append("variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]")
    out.append("variable [sem : go.Semantics]\n")
    for q in used:
        n = kd_name(q)
        fs = [(p, parse_type(ft, ns_of(q))) for p, ft in structs[q]]
        out.append(f"/-- The deep ownership of a `{q.split('.')[-1]}` value with deep value `d`. -/")
        out.append(f"def {n}.own (v : {lean_name(q)}) (dq : DFrac) (d : {n}) : IProp GF :=")
        parts = [f'"{p}" ∷ {own_field(t, "v." + p + chr(39), "d." + p + chr(39))[0]}'
                 for p, t in fs]
        out.append("  iprop(" + " ∗\n    ".join(parts) + ")")
        out.append("")
        out.append(f"/-- The zero `{q.split('.')[-1]}` owns the zero deep value. -/")
        out.append(f"theorem {n}.own_zero_of (v : {lean_name(q)}) (h : v = zero_val {lean_name(q)})")
        out.append(f"    (dq : DFrac) : ⊢ {n}.own (GF := GF) v dq {n}.zero := by")
        out.append(f"  subst h")
        out.append(f"  unfold {n}.own")
        out.append(f"  try unfold {n}.zero")
        for i, (p, t) in enumerate(fs):
            tac = own_field(t, "", "")[1]
            if i < len(fs) - 1:
                out.append(f"  isplitr")
                out.append(f"  · {tac}")
            else:
                out.append(f"  {tac}")
        out.append("")
    out.append("end own\n")
    out.append("end EtcdGrove\nend Perennial\n")
    return "\n".join(out)


def main():
    text = gen()
    if "--check" in sys.argv[1:]:
        old = open(OUT, encoding="utf-8").read() if os.path.exists(OUT) else ""
        if old != text:
            print(f"gen-k8s-deep: {os.path.relpath(OUT, ROOT)} differs from the generated; run "
                  "etc/gen-k8s-deep.py", file=sys.stderr)
            sys.exit(1)
        print("gen-k8s-deep: up to date")
        return
    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    with open(OUT, "w", encoding="utf-8") as f:
        f.write(text)
    print(f"wrote {os.path.relpath(OUT, ROOT)} ({len(used)} struct types)")


if __name__ == "__main__":
    main()
