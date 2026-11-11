/-
Lean-first (no Rocq counterpart).

# `k8s.io/apiserver/pkg/storage`: shared definitions (`notes/k8s-etcd3-plan.md`)

- `prepareKeyM`: `PrepareKey(resourcePrefix, key, recursive)` as a function: the key, with a
  trailing `/` if recursive, or none if it has a `.` or `..` segment, is empty or `/`, or lacks
  the resource prefix.
- `KPre`, `preAt pp p`: preconditions as data (an optional UID, an optional resource version
  string), and the `*Preconditions` `pp` holding them (`nil`: none); `KPre.ok`: whether they hold of
  an object's UID and resource version string (what `Preconditions.Check` tests).
- `metaAt x R uid rvs`: the object `x`, owned as `R`, as a `metav1.Object` (what `meta.Accessor`
  and `Check` call): its dynamic type is one, and `GetUID`/`GetResourceVersion` answer `uid`/`rvs`.
- `invalidErrIs err key`: `NewInvalidObjError(key, _)`'s error, a `*StorageError` with code `4`.
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

/-- `key` has a `..` segment (`PrepareKey`'s first test). -/
def dotDot (key : GoString) : Bool :=
  decide (key = go!".." ∨ go!"../" <+: key ∨ go!"/.." <:+ key ∨ go!"/../" <:+: key)

/-- `key` has a `.` segment (`PrepareKey`'s second test). -/
def dotSeg (key : GoString) : Bool :=
  decide (key = go!"." ∨ go!"./" <+: key ∨ go!"/." <:+ key ∨ go!"/./" <:+: key)

/-- **`PrepareKey(resourcePrefix, key, recursive)`** (`storage/interfaces.go`): the key, made a
directory (a trailing `/`) if recursive, if it has no `.` or `..` segment, is neither empty nor
`/`, and has the resource prefix; else none (an error). -/
def prepareKeyM (rp key : GoString) (r : Bool) : Option GoString :=
  if dotDot key then none
  else if dotSeg key then none
  else if key = [] ∨ key = go!"/" then none
  else
    let k := if r = true ∧ ¬ go!"/" <:+ key then key ++ go!"/" else key
    if rp <+: k then some k else none

/-- **Preconditions as data** (`storage.Preconditions`): the UID and the resource version string
an object must have, each optional. -/
structure KPre where
  uid : Option GoString
  rv : Option GoString

/-- **The preconditions hold** of an object with the UID `uid` and resource version string `rvs`
(`Preconditions.Check`'s two tests). -/
def KPre.ok (p : KPre) (uid rvs : GoString) : Bool :=
  p.uid.all (· = uid) && p.rv.all (· = rvs)

open Iris Iris.BI

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- An optional pointer to a string: `nil` for none, else read-only. -/
def optStrPtr (l : Loc) : Option GoString → IProp GF
  | none => iprop(⌜l = null⌝)
  | some v => iprop(l ↦□ v)

/-- **The `*storage.Preconditions` `pp` holds `p`** (read-only): `nil` for no preconditions, or a
struct whose `UID` and `ResourceVersion` pointers hold `p`'s (`nil` for none). -/
def preAt (pp : Loc) (p : KPre) : IProp GF :=
  iprop(⌜pp = null ∧ p = ⟨none, none⟩⌝ ∨
    ∃ lu lr : Loc, pp ↦□ k8s_io.apiserver.pkg.storage.Preconditions.mk lu lr ∗
      optStrPtr lu p.uid ∗ optStrPtr lr p.rv)

instance preAt_persistent (pp : Loc) (p : KPre) : Persistent (preAt (GF := GF) pp p) := by
  unfold preAt
  cases p with
  | mk u r => cases u <;> cases r <;> (simp only [optStrPtr]; infer_instance)

/-- **The object `x`, owned as `R`, as a `metav1.Object`** (persistent): its dynamic type is a
`metav1.Object` (`meta.Accessor`'s first case), and its `GetUID` and `GetResourceVersion` answer
`uid` and `rvs`, leaving `R`. -/
def metaAt (x : GoInterface) (R : IProp GF) (uid rvs : GoString) : IProp GF :=
  iprop(□ (R -∗ ⌜∃ ii, x = GoInterface.ok ii ∧
      go.typeSetContains ii.ty k8s_io.apimachinery.pkg.apis.«meta».v1.Object.ty = true⌝) ∗
    □ (∀ (ii : GoInterfaceOk) (Φ : val → IProp GF), ⌜x = GoInterface.ok ii⌝ -∗ R -∗
        ▷ (R -∗ Φ #uid) -∗ WP (App (Val #(methods ii.ty go!"GetUID" ii.v)) (Val #())) {{ Φ }}) ∗
    □ (∀ (ii : GoInterfaceOk) (Φ : val → IProp GF), ⌜x = GoInterface.ok ii⌝ -∗ R -∗
        ▷ (R -∗ Φ #rvs) -∗
        WP (App (Val #(methods ii.ty go!"GetResourceVersion" ii.v)) (Val #())) {{ Φ }}))

instance metaAt_persistent (x : GoInterface) (R : IProp GF) (uid rvs : GoString) :
    Persistent (metaAt x R uid rvs) := by
  unfold metaAt; infer_instance

/-- **`NewInvalidObjError(key, _)`'s error** (persistent): a `*StorageError` with code `4`
(`ErrCodeInvalidObj`), the key, and an inner error (the message's). -/
def invalidErrIs (err : GoInterface) (key : GoString) : IProp GF :=
  iprop(∃ (l : Loc) (e : GoInterface), ⌜err = interface.mkOk
      (go.GoType.PointerType k8s_io.apiserver.pkg.storage.StorageError.ty) #l⌝ ∗
    l ↦□ k8s_io.apiserver.pkg.storage.StorageError.mk (W64 4) key (W64 0) e)

instance invalidErrIs_persistent (err : GoInterface) (key : GoString) :
    Persistent (invalidErrIs (GF := GF) err key) := by
  unfold invalidErrIs; infer_instance

end defs

end k8s
end EtcdGrove
end Perennial
