#!/usr/bin/env python3
"""Generate `Proof/k8s_io/api/Deep.lean`: the deep values of the Kubernetes API objects the model
API server stores (pods, nodes, daemon sets, controller revisions) and their deep ownership.

and the proofs of their deep copies (deepcopy-gen's `DeepCopyInto`, `DeepCopy`, `DeepCopyObject`).

usage: etc/gen-k8s-deep.py            write the files
       etc/gen-k8s-deep.py --check    exit 1 if a file differs from what would be generated
                                      (in etc/gates.sh)
       etc/gen-k8s-deep.py --only=T,U only the deep copies of the types T, U (to try a change)

It writes `Proof/k8s_io/api/Deep.lean`, the modules `Proof/k8s_io/api/DeepCopy/*.lean`, the proof
`Proof/k8s_io/api/<pkg>/<R>__DeepCopyObject.lean` of each proved root, and, between the markers
`# BEGIN/END etc/gen-k8s-deep.py`, the `translate` entries of the Goose configurations
(`Code/k8s_io/{api/core/v1,api/apps/v1,apimachinery/pkg/apis/meta/v1,apimachinery/pkg/runtime}.toml`)
that the proofs need: after a change to those, run `etc/goose.py --project k8s-apiserver`.

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
A pointer to an untranslatable value (`Quantity`, `FieldsV1`, a struct holding one inline) must be
nil (`Unit`, `ownNilPtrD`): its deep copy copies the pointee, which is never owned. A pointer to a
value opaque only through gap C5 (`IntOrString`, `HTTPGetAction`, `TCPSocketAction`: `GAP_TYPES`)
keeps its nil-ness (`Option Unit`), as the model sets `MaxUnavailable`.

**Deep copies.** deepcopy-gen's `DeepCopyInto` for a struct is `*out = *in` followed by one block
per field that the struct copy does not copy deeply, chosen by the field's type (`copy_kind`): a
nested struct's `DeepCopyInto` (`into`), or an assignment for a struct with no pointer (`assign`);
`metav1.Time`'s own `DeepCopyInto`/`DeepCopy` (`time`, `ptr_time`); for a pointer, `if in.F != nil`
then a new cell and `**out = **in` (`ptr_basic`, `ptr_shallow`) or the pointee's `DeepCopyInto`
(`ptr_into`); for a slice, `make` then `copy` (`slice_copy`) or a loop of the elements'
`DeepCopyInto` (`slice_into`); for a map, `make` then a loop (`map_basic`); nothing reachable for a
field that must be nil (`nil`). For each struct `S` the roots' copies reach (`copy_used`), the
script emits `kd.*.S.DeepCopyInto.spec` (from `in ↦{dq} v` with deep value `d`, `out` gets a value
owned whole with `d`) and its proof, one tactic block per field (`gen_copy_proof`), over the
callees' specs and the lemmas of `Proof/k8s_io/api/DeepCopyBase.lean`; the modules group the
structs by their depth in the callee graph (`CHUNK` per module), so that one level's modules
compile in parallel. A struct whose code, or a callee's, goose does not translate is not proved
(`blocked`), and neither is a root that reaches it, whose `DeepCopyObject` stays a trust-boundary
axiom: goose's guard (Perennial `docs/design/unsafe-memory.md`, R4) refuses a copy of a pointer-free
struct between two memory places (`out.DaemonEndpoints = in.DaemonEndpoints` in `NodeStatus`,
`**out = **in` of a `*SleepAction` in `LifecycleHandler`), and a pointer to an `IntOrString` (gap
C5) is never owned.
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
    for m in re.finditer(r"^@\[reducible\] noncomputable def ([\w']+)\.fieldsUnsealed \[(?:FfiSyntax|GooseExts)\] "
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
    for m in re.finditer(r"^@\[reducible\] noncomputable def ([\w']+)\.underlying \[(?:FfiSyntax|GooseExts)\] "
                         r"\[GoGlobalContext\] : go\.GoType :=\n  (.*)$", text, re.M):
        if not m.group(2).startswith("(go.GoType.StructType"):
            abbrevs[ns + "." + m.group(1)] = m.group(2).strip()
    # an untranslated type: the carrier of an opaque nonempty type
    for m in re.finditer(r"^def (\w+) : Type := \1\.nonempty_type\.type$", text, re.M):
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
    m = re.match(r"(?:_root_\.Perennial\.)?([\w.«»']+)\.ty$", s)
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


# The axiomatized types that are translatable but for a Goose gap: gap C5, `IntOrString`'s field
# `Type` of type `Type` (notes/k8s-apimodel-goose.md). A pointer to a value opaque only through them
# keeps its nil-ness (`Option Unit`: the model sets `MaxUnavailable`); a pointer to any other
# opaque value (`Quantity`, `FieldsV1`: not translatable) must be nil, which is what lets a deep
# copy be proved (`DeepCopyInto` copies the pointee, which is never owned).
GAP_TYPES = {"k8s_io.apimachinery.pkg.util.intstr.IntOrString"}
untr_memo = {}


def untranslatable(q):
    """An opaque named type that stays opaque when the `GAP_TYPES` are translated."""
    if q in untr_memo:
        return untr_memo[q]
    untr_memo[q] = False
    r = False
    if q in GAP_TYPES:
        r = False
    elif q in axioms:
        r = True
    elif q in structs and q not in BASE_STRUCTS:
        r = any(t[0] == "Named" and untranslatable(t[1])
                for t in (parse_type(ft, ns_of(q)) for _, ft in structs[q]))
    elif q in abbrevs:
        t = parse_type(abbrevs[q], ns_of(q))
        r = t[0] == "Named" and untranslatable(t[1])
    untr_memo[q] = r
    return r


def nil_ptr(t):
    """A pointer to an untranslatable value: it must be nil."""
    t = resolve(t)
    if t[0] != "PointerType":
        return False
    p = resolve(t[1])
    return p[0] == "Named" and opaque(p[1]) and untranslatable(p[1])


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
        if nil_ptr(t):
            return "Unit"
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
        if nil_ptr(t):
            return "(fun x _ _ => ownNilPtrD x)"
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
    if k == "PointerType" and nil_ptr(r):
        return f"ownNilPtrD {v}", "iapply (ownNilPtrD_of _ (by rfl))"
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


def persist_inner(t):
    """The ownership function of a field whose ownership depends on the fraction (its
    `DeepPersist` instance makes it read-only), or None for a fraction-free one."""
    if is_basic(t):
        return None
    r = resolve(t)
    k = r[0]
    if k == "Named":
        return None if opaque(r[1]) else f"{kd_name(r[1])}.own"
    if k == "PointerType":
        return None if inline_opaque(resolve(r[1])) else inner(t)
    if k == "SliceType":
        return None if inline_opaque(resolve(r[1])) else inner(t)
    if k == "MapType":
        return None if inline_opaque(resolve(r[2])) else inner(t)
    if k == "Iface":
        return None
    die(f"persist_inner {t}")


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
        return "()" if nil_ptr(t) else "none"
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
# Deep copies: the code deepcopy-gen generates for each type, as a function of the type

# The objects whose `DeepCopyObject` is proved (the others' stays a trust-boundary axiom, for the
# reason `blocked` gives).
COPY_ROOTS = ["k8s_io.api.core.v1.Pod", "k8s_io.api.core.v1.Node", "k8s_io.api.apps.v1.DaemonSet",
              "k8s_io.api.apps.v1.ControllerRevision"]
TIME = "k8s_io.apimachinery.pkg.apis.«meta».v1.Time"
# Opaque types whose Go values hold no pointer (deepcopy-gen copies them by assignment).
GO_SHALLOW_OPAQUE = {"k8s_io.apimachinery.pkg.util.intstr.IntOrString"}
shallow_memo = {}


def go_basic(t):
    """A field deepcopy-gen copies with the struct (no pointer, slice, map or interface): a basic
    value or a named basic type; and whether it holds a string (a pointer, for gc's copies)."""
    t = resolve(t)
    return t[0] in ("Basic", "Base") or (t[0] == "Named" and t[1] in abbrevs and t[1] not in structs)


def shallow(q):
    """A struct deepcopy-gen copies by assignment (`out.F = in.F`, `**out = **in`, `copy`): every
    field basic or a shallow struct. `metav1.Time` is not (a `*Location`: its own `DeepCopyInto`)."""
    if q in shallow_memo:
        return shallow_memo[q]
    if q in GO_SHALLOW_OPAQUE:
        return True
    if q == TIME or q not in structs or opaque(q):
        return False
    r = True
    for _, ft in structs[q]:
        t = resolve(parse_type(ft, ns_of(q)))
        if go_basic(t):
            continue
        if t[0] == "Named" and shallow(t[1]):
            continue
        r = False
    shallow_memo[q] = r
    return r


def pointer_free(q):
    """A shallow struct with no string either: gc copies it with a `Move`, and goose's guard
    refuses its copy between two memory places (Perennial `docs/design/unsafe-memory.md`, R4)."""
    if not shallow(q) or q in GO_SHALLOW_OPAQUE:
        return False
    for _, ft in structs[q]:
        t = parse_type(ft, ns_of(q))
        while t[0] == "Named" and t[1] in abbrevs and t[1] not in structs:
            t = parse_type(abbrevs[t[1]], ns_of(t[1]))
        if t[0] == "Basic" and t[1] == "GoString":
            return False
        if t[0] == "Base":
            return False
        if t[0] == "Named" and not pointer_free(t[1]):
            return False
    return True


def copy_kind(t):
    """How `DeepCopyInto` copies a field of type t (deepcopy-gen's cases), as (kind, callee)."""
    if go_basic(t) and not (resolve(t)[0] == "Named" and resolve(t)[1] == TIME):
        return ("none", None)
    r = resolve(t)
    k = r[0]
    if k == "Named":
        q = r[1]
        if q == TIME:
            return ("time", None)
        if shallow(q):
            return ("assign", q)
        if opaque(q):
            die(f"inline opaque non-shallow {q}")
        return ("into", q)
    if k == "PointerType":
        e = resolve(r[1])
        if go_basic(e) and not (e[0] == "Named" and e[1] == TIME):
            return ("ptr_basic", None)
        q = e[1]
        if q == TIME:
            return ("ptr_time", None)
        if nil_ptr(r):
            return ("nil", None)
        if shallow(q):
            return ("ptr_shallow", q)
        if opaque(q):
            return ("ptr_opaque", q)
        return ("ptr_into", q)
    if k == "SliceType":
        e = resolve(r[1])
        if inline_opaque(e):
            return ("nil", None)
        if go_basic(e) or (e[0] == "Named" and shallow(e[1])):
            return ("slice_copy", e[1] if e[0] == "Named" and e[1] in structs else None)
        return ("slice_into", e[1])
    if k == "MapType":
        if inline_opaque(resolve(r[2])):
            return ("nil", None)
        return ("map_basic", None)
    if k == "Iface":
        return ("nil", None)
    die(f"copy_kind {t}")


def copy_fields(q):
    return [(p, parse_type(ft, ns_of(q)), copy_kind(parse_type(ft, ns_of(q)))) for p, ft in structs[q]]


copy_used = []    # the structs whose DeepCopyInto the roots' copies call, callees first
copy_state = {}


def visit_copy(q):
    if copy_state.get(q):
        return
    copy_state[q] = True
    for _, _, (k, c) in copy_fields(q):
        if k in ("into", "ptr_into", "slice_into"):
            visit_copy(c)
    copy_used.append(q)


for r in COPY_ROOTS:
    visit_copy(r)

blocked_memo = {}


def blocked(q):
    """Why the deep copy of q is not proved (None if it is): a Goose limit in its code or a
    callee's."""
    if q in blocked_memo:
        return blocked_memo[q]
    blocked_memo[q] = None
    why = None
    for p, t, (k, c) in copy_fields(q):
        if k == "assign" and pointer_free(c):
            why = f"`out.{p} = in.{p}` copies a `{c.split('.')[-1]}`, a pointer-free struct, between two memory places: goose's guard refuses it (R4)"
        elif k == "ptr_shallow" and pointer_free(c):
            why = f"`**out = **in` for `{p}` copies a `{c.split('.')[-1]}`, a pointer-free struct, between two memory places: goose's guard refuses it (R4)"
        elif k in ("ptr_opaque", "ptr_shallow") and opaque(c):
            why = f"`{p}` points to a `{c.split('.')[-1]}`, untranslated (gap C5): its copy reads a value never owned"
        elif k in ("into", "ptr_into", "slice_into") and blocked(c):
            why = f"`{p}`: `{c.split('.')[-1]}` ({blocked(c)})" if not blocked(c).startswith("via") else f"`{p}`: {blocked(c)}"
            why = f"via `{c.split('.')[-1]}`"
        if why:
            break
    blocked_memo[q] = why
    return why


def block_root_cause(q, seen=()):
    """The chain of types from q to the type whose own code is blocked, and that reason."""
    w = blocked(q)
    if w is None or not w.startswith("via `"):
        return [q.split(".")[-1]], w
    for p, t, (k, c) in copy_fields(q):
        if k in ("into", "ptr_into", "slice_into") and blocked(c):
            chain, why = block_root_cause(c)
            return [q.split(".")[-1]] + chain, why
    return [q.split(".")[-1]], w


proved = [q for q in copy_used if blocked(q) is None]

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
    out.append("section values\nvariable [GooseExts]\n")
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
    out.append("variable [GooseExts] [GooseSemantics] [GooseInterp]")
    out.append("variable [go_gctx : GoGlobalContext]")
    out.append("variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]")
    out.append("variable [sem : go.Semantics]\n")
    for q in used:
        n = kd_name(q)
        fs = [(p, parse_type(ft, ns_of(q))) for p, ft in structs[q]]
        out.append(f"/-- The deep ownership of a `{q.split('.')[-1]}` value with deep value `d`. -/")
        out.append(f"def {n}.own (v : {lean_name(q)}) (dq : DFrac) (d : {n}) : IProp GF :=")
        parts = [f'"{hname(p)}" ∷ {own_field(t, "v." + p + chr(39), "d." + p + chr(39))[0]}'
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
        T, D = lean_name(q), n
        out.append(f"instance {n}.own_timeless (v : {T}) (dq : DFrac) (d : {D}) :")
        out.append(f"    Timeless ({n}.own (GF := GF) v dq d) := by")
        out.append(f"  unfold {n}.own; infer_instance")
        out.append("")
        out.append(f"instance {n}.own_persistent (v : {T}) (d : {D}) :")
        out.append(f"    Persistent ({n}.own (GF := GF) v DFrac.discard d) := by")
        out.append(f"  unfold {n}.own; infer_instance")
        out.append("")
        out.append(f"/-- A `{q.split('.')[-1]}` owned at any fraction can be made read-only. -/")
        out.append(f"instance {n}.own_deepPersist : DeepPersist (GF := GF) {n}.own where")
        out.append(f"  persist := by")
        out.append(f"    intro v dq d")
        out.append(f"    unfold {n}.own")
        names = [f"H{i}" for i in range(len(fs))]
        pat = names[0] if len(names) == 1 else "⟨" + ", ".join(names) + "⟩"
        out.append(f"    iintro {pat}")
        for i, (p, t) in enumerate(fs):
            inn = persist_inner(t)
            if inn is not None:
                out.append(f"    imod (DeepPersist.persist (GF := GF) (inner := {inn}) _ _ _) $$ H{i} with H{i}")
        out.append(f"    imodintro")
        out.append(f"    iframe")
        out.append("")
    out.append("end own\n")
    out.append("end EtcdGrove\nend Perennial\n")
    return "\n".join(out)


# ---------------------------------------------------------------------------------------------
# The deep copies' specs and proofs

DC_DIR = os.path.join(ROOT, "Proof", "k8s_io", "api", "DeepCopy")
DC_MOD = "Proof.k8s_io.api.DeepCopy"
PKG_ASSUMPTIONS = ["k8s_io.api.core.v1", "k8s_io.api.apps.v1", "k8s_io.apimachinery.pkg.apis.«meta».v1",
                   "k8s_io.apimachinery.pkg.runtime"]
# The number of types in one generated module (each module holds the types of one dependency
# level, so that the levels' modules compile in parallel).
CHUNK = 12


LEAN_KEYWORDS = {"Type", "Prop", "Sort", "fun", "at", "from", "have", "show", "by", "do", "then",
                 "else", "if", "let", "in", "match", "with", "where", "end", "open"}


def hname(p):
    """The Iris hypothesis name of field p's ownership (a Lean keyword cannot be one)."""
    return p + "_" if p in LEAN_KEYWORDS else p


def fix_names(line, p):
    """Rename field p's ownership hypotheses (`p`, `p'`) to `hname(p)` in a generated line."""
    h = hname(p)
    line = re.sub(r'(?<![!\w])"' + p + r"('?)\" ∷", lambda m: '"' + h + m.group(1) + '" ∷', line)
    return re.sub(r"(?<![\w.!\"'])" + p + r"(?=['\s,⟩\]]|$)", h, line)


def sname(p):
    """The name `iStructNamed` gives field p (goose quotes a Lean keyword with a prime)."""
    return p + "'" if p in LEAN_KEYWORDS else p


def struct_of(q):
    return lean_name(q)


def field_addr(base, q, p):
    return f'{base}.[{struct_of(q)}, go!"{p}"]'


def own_inner(t):
    """The ownership function of a field (as in `kd.*.own`), for a pointer, slice or map."""
    return inner(t)


def nil_lemma(t):
    """For a field that must be nil: the lemma giving `⌜v.F' = nil⌝` from its ownership."""
    r = resolve(t)
    return {"PointerType": "ownNilPtrD_null", "SliceType": "ownNilSliceD_null",
            "MapType": "ownNilMapD_null", "Iface": "ownNilIfaceD_null"}[r[0]]


def structs_text(q, p):
    return dict(structs[q])[p]


def gen_copy_proof(q):
    """The spec and proof of `(*q).DeepCopyInto`."""
    n, T = kd_name(q), struct_of(q)
    fs = copy_fields(q)
    out = []
    out.append(f"/-- `in.DeepCopyInto(out)` on a `*{go_name(q)}`: `out` gets a value owned whole (fraction 1)")
    out.append(f"with the deep value of `in`'s. -/")
    out.append(f"abbrev {n}.DeepCopyInto.spec : Prop :=")
    out.append(f"  ∀ (i o : Loc) (v w : {T}) (dq : DFrac) (d : {n}),")
    out.append(f"  {{{{ (i ↦{{dq}} v : IProp GF) ∗ {n}.own v dq d ∗ o ↦ w }}}}")
    out.append(f"    (App (Val (i @!! go.GoType.PointerType {T}.ty @!! go!\"DeepCopyInto\")) (Val #o))")
    out.append(f"  {{{{ (v' : {T}), RET #(); i ↦{{dq}} v ∗ {n}.own v dq d ∗ o ↦ v' ∗ {n}.own v' (DFrac.own 1) d }}}}")
    out.append("")
    out.append(f"theorem {n}.wp_DeepCopyInto : {n}.DeepCopyInto.spec (GF := GF) (hG := hG) := by")
    out.append("  intro i o v w dq d")
    out.append("  wp_start as ⟨Hi, Hown, Ho⟩")
    out.append("  icases typedPointsto_not_null_dup _ _ _ $$ Ho with ⟨Ho, %Honn⟩")
    out.append("  icases typedPointsto_not_null_dup _ _ _ $$ Hi with ⟨Hi, %Hinn⟩")
    out.append("  wp_auto")
    out.append('  iStructNamedPrefix Hi "i"')
    out.append('  iStructNamedPrefix Ho "o"')
    out.append("  iNamed Hown")
    for p, t, (k, c) in fs:
        if k == "nil":
            out.append(f"  ihave %h{p} := {nil_lemma(t)} _ $$ {hname(p)}")
            out.append(f"  rw [h{p}]")
    news = []   # (field, the copy's value)
    for p, t, (k, c) in fs:
        iF, oF = field_addr("i", q, p), field_addr("o", q, p)
        if k == "none":
            continue
        start = len(out)
        out.append(f"  -- {p} ({k})")
        if k == "nil":
            out.append("  try wp_auto")
        elif k == "assign":
            out.append("  try wp_auto")
            out.append(f"  icases deepFree_dup _ _ dq (DFrac.own 1) _ $$ {p} with ⟨{p}, {p}'⟩")
        elif k == "time":
            out.append("  try wp_auto")
            out.append(f"  wp_apply metav1Time.wp_DeepCopyInto $$ [i{sname(p)} o{sname(p)}] as ⟨i{sname(p)}, o{sname(p)}⟩")
            out.append("  · iframe")
        elif k == "into":
            out.append("  try wp_auto")
            out.append(f"  wp_apply {kd_name(c)}.wp_DeepCopyInto $$ [i{sname(p)} {p} o{sname(p)}] as %x{p} ⟨i{sname(p)}, {p}, o{sname(p)}, {p}'⟩")
            out.append("  · iframe")
            news.append((p, f"x{p}"))
        elif k in ("ptr_basic", "ptr_shallow", "ptr_into", "ptr_time"):
            inn = own_inner(t)
            out.append(f'  wp_join iprop("in" ∷ in_ptr ↦ i ∗ "out" ∷ out_ptr ↦ o ∗')
            out.append(f'      "i{sname(p)}" ∷ {iF} ↦{{dq}} v.{p}\' ∗ "{p}" ∷ {inn} v.{p}\' dq d.{p}\' ∗')
            out.append(f'      ∃ p\' : Loc, "o{sname(p)}" ∷ {oF} ↦ p\' ∗ "{p}\'" ∷ {inn} p\' (DFrac.own 1) d.{p}\')')
            out.append(f"    at next with [«in» out i{sname(p)} o{sname(p)} {p}] as ⟨«in», out, i{sname(p)}, {p}, %p{p}, o{sname(p)}, {p}'⟩")
            out.append("  · try wp_auto")
            out.append("    wp_if_destruct")
            out.append(f"    · icases ownPtrD_null_dup _ _ _ (DFrac.own 1) _ Hif $$ {p} with ⟨{p}, {p}'⟩")
            out.append("      iframe")
            out.append(f"    · icases ownPtrD_nonnull _ _ _ _ Hif $$ {p} with ⟨%x, %e, %He, Hp, Hx⟩")
            cell = "«$r0»"
            if k in ("ptr_basic", "ptr_shallow"):
                out.append("      try wp_auto")
                out.append("      icases deepFree_dup _ x dq (DFrac.own 1) e $$ Hx with ⟨Hx, Hx'⟩")
            elif k == "ptr_into":
                out.append("      try wp_auto")
                out.append(f"      wp_apply {kd_name(c)}.wp_DeepCopyInto $$ [Hp Hx «$r0»] as %x' ⟨Hp, Hx, «$r0», Hx'⟩")
                out.append("      · iframe")
                out.append("      try wp_auto")
            elif k == "ptr_time":
                out.append("      try wp_auto")
                out.append("      wp_apply metav1Time.wp_DeepCopy $$ [Hp] as %t' ⟨Hp, Ht'⟩")
                out.append("      · iframe")
                out.append("      try wp_auto")
                out.append("      icases deepFree_dup _ x dq (DFrac.own 1) e $$ Hx with ⟨Hx, Hx'⟩")
                cell = "Ht'"
            out.append("      rw [He]")
            out.append(f"      ihave {p} := ownPtrD_some _ _ _ _ _ $$ [Hp Hx]")
            out.append("      · iframe")
            out.append(f"      ihave {p}' := ownPtrD_some _ _ _ _ _ $$ [{cell} Hx']")
            out.append("      · iframe")
            out.append("      wp_join_done")
            news.append((p, f"p{p}"))
        elif k == "slice_copy":
            inn = own_inner(t)
            ev = lean_ty(resolve(resolve(t)[1]))
            out.append(f'  wp_join iprop("in" ∷ in_ptr ↦ i ∗ "out" ∷ out_ptr ↦ o ∗')
            out.append(f'      "i{sname(p)}" ∷ {iF} ↦{{dq}} v.{p}\' ∗ "{p}" ∷ {inn} v.{p}\' dq d.{p}\' ∗')
            out.append(f'      ∃ s\' : GoSlice, "o{sname(p)}" ∷ {oF} ↦ s\' ∗ "{p}\'" ∷ {inn} s\' (DFrac.own 1) d.{p}\')')
            out.append(f"    at next with [«in» out i{sname(p)} o{sname(p)} {p}] as ⟨«in», out, i{sname(p)}, {p}, %p{p}, o{sname(p)}, {p}'⟩")
            out.append("  · try wp_auto")
            out.append("    wp_if_destruct")
            out.append(f"    · icases ownSliceD_nil_dup _ _ _ (DFrac.own 1) _ Hif $$ {p} with ⟨{p}, {p}'⟩")
            out.append("      iframe")
            out.append(f"    · icases ownSliceD_elim _ _ _ _ $$ {p} with ⟨%vs, Hs, Hl⟩")
            out.append("      ihave %Hlen := ownSlice_len _ _ _ $$ Hs")
            out.append("      try wp_auto")
            out.append(f"      wp_apply wp_slice_make2 (V := {ev}) $$ [] as %s' ⟨Hs', -⟩")
            out.append("      · ipureintro; exact Hlen.2")
            out.append("      try wp_auto")
            out.append("      wp_apply wp_slice_copy $$ [Hs' Hs] as %n ⟨-, Hs', Hs⟩")
            out.append("      · iframe")
            out.append("      try wp_auto")
            out.append("      rw [list_copy_replicate vs _ _ Hlen.1]")
            out.append("      icases bigSepL2_deepFree_dup _ dq (DFrac.own 1) _ _ $$ Hl with ⟨Hl, Hl'⟩")
            out.append(f"      ihave {p} := ownSliceD_intro _ _ _ _ _ $$ [Hs Hl]")
            out.append("      · iframe")
            out.append(f"      ihave {p}' := ownSliceD_intro _ _ _ _ _ $$ [Hs' Hl']")
            out.append("      · iframe")
            out.append("      wp_join_done")
            news.append((p, f"p{p}"))
        elif k == "map_basic":
            inn = own_inner(t)
            out.append(f'  wp_join iprop("in" ∷ in_ptr ↦ i ∗ "out" ∷ out_ptr ↦ o ∗')
            out.append(f'      "i{sname(p)}" ∷ {iF} ↦{{dq}} v.{p}\' ∗ "{p}" ∷ {inn} v.{p}\' dq d.{p}\' ∗')
            out.append(f'      ∃ m\' : GoMap, "o{sname(p)}" ∷ {oF} ↦ m\' ∗ "{p}\'" ∷ {inn} m\' (DFrac.own 1) d.{p}\')')
            out.append(f"    at next with [«in» out i{sname(p)} o{sname(p)} {p}] as ⟨«in», out, i{sname(p)}, {p}, %p{p}, o{sname(p)}, {p}'⟩")
            out.append("  · try wp_auto")
            out.append("    wp_if_destruct")
            out.append(f"    · icases ownMapD_null_dup _ _ (DFrac.own 1) _ Hif $$ {p} with ⟨{p}, {p}'⟩")
            out.append("      iframe")
            out.append(f"    · icases ownMapD_nonnull _ _ _ Hif $$ {p} with ⟨%M, %He, Hm⟩")
            kt, vt = split_args(resolve(t) and structs_text(q, p)[len("(go.GoType.MapType "):-1])
            K, V = dty(resolve(t)[1]), dty(resolve(t)[2])
            out.append("      try wp_auto")
            out.append(f"      wp_apply (wp_map_len (K := {K}) (V := {V})) $$ [Hm] as Hm")
            out.append("      · iframe")
            out.append(f"      wp_apply (wp_map_make2 (K := {K}) (V := {V})) as %m' Hm'")
            out.append("      try wp_auto")
            out.append(f"      wp_apply (wp_map_copy_loop (K := {K}) (V := {V}) {kt} {vt}")
            out.append(f"          iprop(out_ptr ↦ {oF} ∗ {oF} ↦ m' ∗")
            out.append(f"            (∃ k : {K}, key_ptr ↦ k) ∗ (∃ x : {V}, val_ptr ↦ x))")
            out.append(f"          _ _ m' M dq) $$ Hm Hm' [out o{sname(p)} key val]")
            out.append("      · iframe")
            out.append("      · imodintro")
            out.append("        iintro %k %x %M' %Hx Hm' ⟨out, oF, ⟨%k0, key⟩, ⟨%x0, val⟩⟩")
            out.append("        wp_auto")
            out.append(f"        wp_apply (wp_mapInsert {kt}) $$ [Hm'] as Hm'")
            out.append("        · iframe")
            out.append("        try wp_auto")
            out.append("        iframe")
            out.append("        ipureintro; rfl")
            out.append("      · iintro Hm Hm' ⟨out, oF, key, val⟩")
            out.append("        rw [He]")
            out.append(f"        ihave {p} := ownMapD_some _ _ _ $$ [Hm]")
            out.append("        · iframe")
            out.append(f"        ihave {p}' := ownMapD_some _ _ _ $$ [Hm']")
            out.append("        · iframe")
            out.append("        wp_join_done")
            news.append((p, f"p{p}"))
        elif k == "slice_into":
            inn = own_inner(t)
            ev = lean_ty(resolve(resolve(t)[1]))
            out.append(f'  wp_join iprop("in" ∷ in_ptr ↦ i ∗ "out" ∷ out_ptr ↦ o ∗')
            out.append(f'      "i{sname(p)}" ∷ {iF} ↦{{dq}} v.{p}\' ∗ "{p}" ∷ {inn} v.{p}\' dq d.{p}\' ∗')
            out.append(f'      ∃ s\' : GoSlice, "o{sname(p)}" ∷ {oF} ↦ s\' ∗ "{p}\'" ∷ {inn} s\' (DFrac.own 1) d.{p}\')')
            out.append(f"    at next with [«in» out i{sname(p)} o{sname(p)} {p}] as ⟨«in», out, i{sname(p)}, {p}, %p{p}, o{sname(p)}, {p}'⟩")
            out.append("  · try wp_auto")
            out.append("    wp_if_destruct")
            out.append(f"    · icases ownSliceD_nil_dup _ _ _ (DFrac.own 1) _ Hif $$ {p} with ⟨{p}, {p}'⟩")
            out.append("      iframe")
            out.append(f"    · icases ownSliceD_elim _ _ _ _ $$ {p} with ⟨%vs, Hs, Hl⟩")
            out.append("      ihave %Hlen := ownSlice_len _ _ _ $$ Hs")
            out.append("      try wp_auto")
            out.append(f"      wp_apply wp_slice_make2 (V := {ev}) $$ [] as %s' ⟨Hs', -⟩")
            out.append("      · ipureintro; exact Hlen.2")
            out.append("      ihave %Hlen' := ownSlice_len _ _ _ $$ Hs'")
            out.append("      simp only [List.length_replicate] at Hlen'")
            out.append("      try wp_auto")
            et = resolve(resolve(t)[1])
            ety, ein = lean_name(et[1]) + ".ty", inner(resolve(t)[1])
            out.append(f"      wp_apply (wp_slice_for_range (V := {ev}) {ety} v.{p}' vs dq _")
            out.append(f"          (fun j => iprop(copyPrefix {ein} s' (sint.nat v.{p}'.len) d.{p}' j ∗")
            out.append(f"            ([∗list] x;e ∈ vs;d.{p}', {ein} x dq e) ∗ in_ptr ↦ {iF} ∗ {iF} ↦{{dq}} v.{p}' ∗")
            out.append(f"            out_ptr ↦ {oF} ∗ {oF} ↦ s' ∗ ∃ k : w64, i_ptr ↦ k))) $$ Hs [Hl Hs' «in» i{sname(p)} out o{sname(p)} i]")
            out.append(f"      · ihave Hc := copyPrefix_init {ein} _ _ d.{p}' $$ Hs'")
            out.append("        iframe")
            out.append("      · imodintro")
            out.append(f"        iintro %j %x %hx ⟨Hc, Hl, «in», i{sname(p)}, out, o{sname(p)}, %k, i⟩ Hs")
            out.append("        have hjv := (List.getElem?_eq_some_iff.1 hx).1")
            out.append("        wp_auto")
            out.append("        have hb : 0 ≤ sint.Z (W64 (j : Int)) ∧ sint.Z (W64 (j : Int)) < sint.Z s'.len := by")
            out.append("          constructor <;> word")
            out.append("        simp only [hb.1, hb.2, and_self, ↓reduceIte]")
            out.append("        wp_auto")
            out.append(f"        have hb' : 0 ≤ sint.Z (W64 (j : Int)) ∧ sint.Z (W64 (j : Int)) < sint.Z v.{p}'.len := by")
            out.append("          constructor <;> word")
            out.append("        simp only [hb'.1, hb'.2, and_self, ↓reduceIte]")
            out.append("        wp_auto")
            out.append(f"        wp_apply (wp_slice_elem_deepcopy {ety} {ein} {kd_name(c)}.wp_DeepCopyInto v.{p}' s' vs d.{p}' dq")
            out.append(f"            (sint.nat v.{p}'.len) j x hx (by omega) (by word)) $$ [Hs Hl Hc] as ⟨Hs, Hl, Hc⟩")
            out.append("        · iframe")
            out.append("        try wp_auto")
            out.append("        iframe")
            out.append("        ipureintro; rfl")
            out.append(f"      · iintro ⟨Hc, Hl, «in», i{sname(p)}, out, o{sname(p)}, %k, i⟩ Hs")
            out.append("        ihave %hdl := BigSepL2.bigSepL2_length $$ Hl")
            out.append("        rw [Hlen.1]")
            out.append(f"        ihave {p} := ownSliceD_intro _ _ _ _ _ $$ [Hs Hl]")
            out.append("        · iframe")
            out.append(f"        ihave {p}' := copyPrefix_done _ _ _ _ (by omega) $$ Hc")
            out.append("        wp_join_done")
            news.append((p, f"p{p}"))
        else:
            out.append(f"  sorry -- {k}")
            news.append((p, f"p{p}"))
        if hname(p) != p:
            out[start:] = [fix_names(l, p) for l in out[start:]]
    for p, t, (k, c) in fs:
        if k == "none":
            out.append(f"  icases {hname(p)} with %h{p}")
    allf = " ".join(f"i{sname(p)}" for p, _, _ in fs) + " i_"
    allo = " ".join(f"o{sname(p)}" for p, _, _ in fs) + " o_"
    vnew = "v" if not news else "{ v with " + ", ".join(f"{p}' := {x}" for p, x in news) + " }"
    hn = "".join(f", h{p}" for p, _, (k, _) in fs if k == "nil")
    out.append(f"  ihave Hi := typedPointsto_combine i v dq Hinn $$ [{allf}]")
    out.append(f"  · simp only [TypedPointsto.typedPointstoDef{hn}]; iframe")
    out.append(f"  ihave Ho := typedPointsto_combine o ({vnew} : {T}) (DFrac.own 1) Honn $$ [{allo}]")
    out.append(f"  · simp only [TypedPointsto.typedPointstoDef{hn}]; iframe")
    out.append("  iapply HΦ")
    out.append("  iframe")
    nils = sorted({nil_lemma(t)[:-len("_null")] for _, t, (k, _) in fs if k == "nil"})
    out.append(f"  simp only [{', '.join([n + '.own', 'named'] + nils)}]")
    out.append("  iframe")
    out.append("  all_goals (ipureintro; simp_all)")
    out.append("")
    return "\n".join(out)


DC_HEADER = """/-
GENERATED by `etc/gen-k8s-deep.py` from the Goose translation of `k8s.io/api` and apimachinery;
do not edit. **The deep copies (deepcopy-gen's `DeepCopyInto`)** of {names}: each one's spec
(`kd.*.DeepCopyInto.spec`: the copy owns, whole, the deep value of the original) and proof, over its
callees' (see the script's documentation and `Proof/k8s_io/api/DeepCopyBase.lean`). Lean-first (no
Rocq counterpart).
-/
module

{imports}

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

-- the slice copy loops are proved by `wp_slice_for_range`, at the `slice.forRange` it is about
attribute [-instance] pure_wp_slice_for_range

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {{GF : BundledGFunctors}} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
{assumptions}
"""


def dc_modules(only=None):
    """The generated modules: name -> (types, text)."""
    types = [q for q in proved if only is None or go_name(q) in only]
    lvl = {}
    def level(q):
        if q not in lvl:
            lvl[q] = max([level(c) + 1 for _, _, (k, c) in copy_fields(q)
                          if k in ("into", "ptr_into", "slice_into")] + [0])
        return lvl[q]
    # the structs the proved roots' copies reach first, so that their modules' chain is short
    rooted = set()
    def reach(q):
        if q not in rooted:
            rooted.add(q)
            for _, _, (k, c) in copy_fields(q):
                if k in ("into", "ptr_into", "slice_into"):
                    reach(c)
    for r in COPY_ROOTS:
        if r in types:
            reach(r)
    mods, where = {}, {}
    for L in sorted({level(q) for q in types}):
        qs = [q for q in types if level(q) == L and q in rooted] + \
            [q for q in types if level(q) == L and q not in rooted]
        for j in range(0, len(qs), CHUNK):
            name = f"L{L}_{j // CHUNK}"
            mods[name] = qs[j:j + CHUNK]
            for q in qs[j:j + CHUNK]:
                where[q] = name
    out = {}
    for name, qs in mods.items():
        deps = sorted({where[c] for q in qs for _, _, (k, c) in copy_fields(q)
                       if k in ("into", "ptr_into", "slice_into") and c in where} - {name})
        imports = [f"public import {DC_MOD}.Free"] + \
            [f"public import {DC_MOD}.{d}" for d in deps]
        assumptions = "\n".join(f"variable [{ns}.Assumptions]" for ns in PKG_ASSUMPTIONS)
        body = [DC_HEADER.format(names=", ".join(f"`{go_name(q)}`" for q in qs),
                                 imports="\n".join(imports), assumptions=assumptions)]
        for q in qs:
            body.append(gen_copy_proof(q))
        body.append("end proof\n\nend EtcdGrove\nend Perennial\n")
        out[os.path.join(DC_DIR, name + ".lean")] = "\n".join(body)
    assumptions = "\n".join(f"variable [{ns}.Assumptions]" for ns in PKG_ASSUMPTIONS)
    free = [DC_HEADER.format(names="no type: the shallow structs' ownership",
                             imports="public import Proof.k8s_io.api.Deep\npublic import Proof.k8s_io.api.DeepCopyBase",
                             assumptions=assumptions).replace(
        "**The deep copies (deepcopy-gen's `DeepCopyInto`)** of no type: the shallow structs' ownership",
        "**The shallow structs' deep ownership is fraction-free** (`DeepFree`: deepcopy-gen copies them\nwith their struct)")]
    free.append(gen_deep_free())
    free.append("end proof\n\nend EtcdGrove\nend Perennial\n")
    out[os.path.join(DC_DIR, "Free.lean")] = "\n".join(free)
    return out, where


def gen_deep_free():
    """`DeepFree` for the shallow structs (their copies are the struct's)."""
    out = ["/-! ### The shallow structs' ownership is fraction-free -/", ""]
    for q in used:
        if not shallow(q) or opaque(q):
            continue
        n = kd_name(q)
        nested = [p for p, ft in structs[q]
                  if resolve(parse_type(ft, ns_of(q)))[0] == "Named"
                  and not is_basic(parse_type(ft, ns_of(q)))]
        out.append(f"instance {n}.own_persistent' (x : {lean_name(q)}) (dq : DFrac) (e : {n}) :")
        out.append(f"    Persistent ({n}.own (GF := GF) x dq e) := by")
        out.append(f"  unfold {n}.own; infer_instance")
        out.append("")
        out.append(f"instance {n}.own_deepFree : DeepFree (GF := GF) {n}.own where")
        out.append(f"  persistent := by intro x dq e; infer_instance")
        if not nested:
            out.append(f"  frac := by intro x dq dq' e; unfold {n}.own; iintro H; iexact H")
        else:
            out.append(f"  frac := by")
            out.append(f"    intro x dq dq' e; unfold {n}.own; iintro H; iNamed H")
            for p in nested:
                out.append(f"    ihave {hname(p)} := DeepFree.frac _ _ dq' _ $$ {hname(p)}")
            out.append(f"    iframe")
        out.append("")
    return "\n".join(out)


TOML_BEGIN = "  # BEGIN etc/gen-k8s-deep.py: the deep copies the proofs need (generated; do not edit)\n"
TOML_END = "  # END etc/gen-k8s-deep.py\n"


def go_name(q):
    return q.split(".")[-1]


def translate_names():
    """The functions each package's Goose configuration translates, for the proved copies."""
    names = {}
    def add(q, fn):
        names.setdefault(ns_of(q), []).append(f"{go_name(q)}.{fn}")
    kinds = {k for q in proved for _, _, (k, _) in copy_fields(q)}
    if "time" in kinds or "ptr_time" in kinds:
        add(TIME, "DeepCopyInto")
    if "ptr_time" in kinds:
        add(TIME, "DeepCopy")
    for q in proved:
        add(q, "DeepCopyInto")
    for r in COPY_ROOTS:
        if r in proved:
            add(r, "DeepCopy")
            add(r, "DeepCopyObject")
    return names


def toml_path(ns):
    return os.path.join(CODE, ns.replace("«", "").replace("»", "").replace(".", "/") + ".toml")


def toml_outputs():
    out = {}
    names = translate_names()
    for ns in PKGS:
        path = toml_path(ns)
        if not os.path.exists(path):
            continue
        text = open(path, encoding="utf-8").read()
        if TOML_BEGIN not in text:
            if ns in names:
                die(f"{path}: no generated block for {names[ns]}")
            continue
        i, j = text.index(TOML_BEGIN), text.index(TOML_END)
        lines = "".join(f'  "{n}",\n' for n in sorted(names.get(ns, [])))
        out[path] = text[:i + len(TOML_BEGIN)] + lines + text[j:]
    return out


ROOT_SHORT = {"k8s_io.api.core.v1": ("core", "corev1"), "k8s_io.api.apps.v1": ("apps", "appsv1")}


def root_proof(r, where):
    """The proof of a root's `DeepCopyObject` (`Proof/k8s_io/api/<pkg>/<R>__DeepCopyObject.lean`)."""
    ns, R = r.rsplit(".", 1)
    path_pkg = ns.replace(".", "/")
    n, T = kd_name(r), r
    nsp = ROOT_SHORT[ns][1]
    return os.path.join(ROOT, "Proof", path_pkg, f"{R}__DeepCopyObject.lean"), f"""/-
GENERATED by `etc/gen-k8s-deep.py`; do not edit. Proof of
`Spec/{path_pkg}/{R}__DeepCopyObject.lean`: `(*{R}).DeepCopyObject()` and `DeepCopy()`
(`zz_generated.deepcopy.go`), over the generated proof of `DeepCopyInto`
(`Proof/k8s_io/api/DeepCopy/`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.{ns.replace("«", "").replace("»", "")}.{R}__DeepCopyObject
public import {DC_MOD}.{where[r]}

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace {nsp}

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {{GF : BundledGFunctors}} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : {ns}.Assumptions]

/-- `x.DeepCopy()` of a non-nil `*{R}`: a new `*{R}`, owned whole with the same deep value. -/
theorem {n}.wp_DeepCopy (l : Loc) (v : {T}) (dq : DFrac) (d : {n}) :
    {{{{ (l ↦{{dq}} v : IProp GF) ∗ {n}.own v dq d }}}}
      (App (Val (l @!! go.GoType.PointerType {T}.ty @!! go!"DeepCopy")) (Val #()))
    {{{{ (l' : Loc) (v' : {T}), RET #l'; l ↦{{dq}} v ∗ {n}.own v dq d ∗ l' ↦ v' ∗
        {n}.own v' (DFrac.own 1) d ∗ ⌜l' ≠ null⌝ }}}} := by
  wp_start as ⟨Hl, Hown⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hl with ⟨Hl, %Hlnn⟩
  wp_auto
  wp_if_destruct
  · exact absurd rfl Hlnn
  icases typedPointsto_not_null_dup _ _ _ $$ «$r0» with ⟨«$r0», %Hnn⟩
  wp_apply {n}.wp_DeepCopyInto $$ [Hl Hown «$r0»] as %v' ⟨Hl, Hown, «$r0», Hown'⟩
  · iframe
  try wp_auto
  iapply HΦ
  iframe
  ipureintro; exact Hnn

theorem {R}.DeepCopyObject.wp_proof : {R}.DeepCopyObject.spec (GF := GF) (hG := hG) := by
  intro l v dq d
  wp_start as ⟨Hl, Hown⟩
  wp_auto
  wp_apply {n}.wp_DeepCopy $$ [Hl Hown] as %l' %v' ⟨Hl, Hown, Hl', Hown', %Hl'nn⟩
  · iframe
  try wp_auto
  wp_if_destruct
  · exact absurd rfl Hl'nn
  iapply HΦ
  iframe

end proof

end {nsp}
end EtcdGrove
end Perennial
"""


def outputs():
    out = {OUT: gen()}
    out.update(toml_outputs())
    only = None
    for a in sys.argv[1:]:
        if a.startswith("--only="):
            only = set(a[len("--only="):].split(","))
    mods, where = dc_modules(only)
    out.update(mods)
    for r in COPY_ROOTS:
        if r in where:
            path, text = root_proof(r, where)
            out[path] = text
    return out


def main():
    outs = outputs()
    if "--check" in sys.argv[1:]:
        bad = []
        for path, text in outs.items():
            old = open(path, encoding="utf-8").read() if os.path.exists(path) else ""
            if old != text:
                bad.append(os.path.relpath(path, ROOT))
        if bad:
            print(f"gen-k8s-deep: {', '.join(bad)} differ(s) from the generated; run "
                  "etc/gen-k8s-deep.py", file=sys.stderr)
            sys.exit(1)
        print("gen-k8s-deep: up to date")
        return
    for path, text in outs.items():
        old = open(path, encoding="utf-8").read() if os.path.exists(path) else None
        if old != text:
            os.makedirs(os.path.dirname(path), exist_ok=True)
            with open(path, "w", encoding="utf-8") as f:
                f.write(text)
            print(f"wrote {os.path.relpath(path, ROOT)}")
    print(f"gen-k8s-deep: {len(used)} struct types; deep copies of {len(proved)} of {len(copy_used)} proved")


if __name__ == "__main__":
    main()
