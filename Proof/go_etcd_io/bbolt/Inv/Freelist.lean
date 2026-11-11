/-
The freelist object split by field (U0a of `notes/bbolt-proof-plan.md`; design §3.5): the
`readonlyTXIDs` field of the embedded `*shared` (`flRoOwn`, `metaR`'s) and the rest (`flPgOwn`,
the writer side's). `AddReadonlyTXID`/`RemoveReadonlyTXID` need only `flRoOwn`,
`ReleasePendingPages` both, the other methods only `flPgOwn`; U2 restates the old `Iface`
contract per part (`old/bbolt/.../internal/freelist/{Iface,HashModel,ArrayIface}.lean`).

(U0a deviation: this module is not in the brief's list; `Inv/Locks.lean` needs the two parts
defined. Only field points-tos are used, so that nothing here needs a package's `Assumptions`:
the sealed predicates of `Api.lean` cannot take them.)
-/
module

public import Proof.go_etcd_io.bbolt.Model.FL
public import Proof.go_etcd_io.bbolt.Inv.State
public import GeneratedProof.go_etcd_io.bbolt.internal.freelist

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI go_etcd_io.bbolt.internal.freelist

/-! ## The hash map implementation's pure state (old `HashModel`) -/

/-- The spans (first id ↦ size) have positive sizes, do not wrap around, and are disjoint. -/
def spansOK (sp : GMap w64 w64) : Prop :=
  (∀ st sz, sp !! st = some sz → 1 ≤ sz.toNat ∧ st.toNat + sz.toNat ≤ 2 ^ 64) ∧
  (∀ st sz st' sz' x, sp !! st = some sz → sp !! st' = some sz' → st ≠ st' →
    inRun st sz.toNat x → ¬ inRun st' sz'.toNat x)

/-- The free ids are the ids of the spans, increasing. -/
def spansFree (sp : GMap w64 w64) (free : List w64) : Prop :=
  PgidsIncr free ∧ ∀ x, x ∈ free ↔ ∃ st sz, sp !! st = some sz ∧ inRun st sz.toNat x

/-- The maps of a `hashMap` agree: `bwm` is `sp` by last ids, `sets` by size. -/
def mapsOK (sp bwm : GMap w64 w64) (sets : GMap w64 (GMap w64 Unit)) : Prop :=
  (∀ k v, bwm !! k = some v ↔ ∃ st, sp !! st = some v ∧ k = st + v - W64 1) ∧
  (∀ sz st, (∃ set, sets !! sz = some set ∧ (set !! st).isSome) ↔ sp !! st = some sz) ∧
  (∀ sz set, sets !! sz = some set → ∃ st, (set !! st).isSome)

/-- A consistent `hashMap` holding the free ids `free`. -/
def hashOK (cnt : w64) (sp bwm : GMap w64 w64) (sets : GMap w64 (GMap w64 Unit))
    (free : List w64) : Prop :=
  spansOK sp ∧ spansFree sp free ∧ mapsOK sp bwm sets ∧ cnt.toNat = free.length ∧
  free.length < 2 ^ 63

section preds
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The freelist interface value `fli` is an implementation (an `*array` or a `*hashMap` at
`a`) whose embedded `*shared` is `s` (persistent). -/
def flImplAt (fli : GoInterface) (a s : Loc) : IProp GF :=
  iprop((⌜fli = interface.mkOk (go.GoType.PointerType array'.ty) #a⌝ ∗
      structFieldRef array' go!"shared" a ↦□ s) ∨
    (⌜fli = interface.mkOk (go.GoType.PointerType hashMap.ty) #a⌝ ∗
      structFieldRef hashMap go!"shared" a ↦□ s))

/-- **The freelist's `readonlyTXIDs`** (`metaR`'s part): the read-only transactions `ro`. -/
def flRoOwn (fli : GoInterface) (ro : List w64) : IProp GF :=
  iprop(∃ (a s : Loc) (sl : GoSlice), flImplAt fli a s ∗
    structFieldRef shared go!"readonlyTXIDs" s ↦ sl ∗ sl ↦* ro ∗
    ownSliceCap w64 sl (DFrac.own 1))

/-- A `*txPending` at `p` holding `pd` (`flPgOwn` adds that `p` is not nil: every entry the
code stores is a fresh allocation). -/
def ownPending (p : Loc) (pd : Pending) : IProp GF :=
  iprop(∃ (ids atx : GoSlice),
    structFieldRef txPending go!"ids" p ↦ ids ∗ ids ↦* pd.ids ∗
    ownSliceCap w64 ids (DFrac.own 1) ∗
    structFieldRef txPending go!"alloctx" p ↦ atx ∗ atx ↦* pd.alloctx ∗
    ownSliceCap w64 atx (DFrac.own 1) ∗
    structFieldRef txPending go!"lastReleaseBegin" p ↦ pd.lastReleaseBegin)

/-- The implementation's own part, holding the free ids: an `array`'s sorted `ids`, or a
`hashMap`'s spans. -/
def flImplOwn (fli : GoInterface) (a : Loc) (free : List w64) : IProp GF :=
  iprop((⌜fli = interface.mkOk (go.GoType.PointerType array'.ty) #a⌝ ∗
      ∃ sl : GoSlice, structFieldRef array' go!"ids" a ↦ sl ∗ sl ↦* free ∗
        ownSliceCap w64 sl (DFrac.own 1)) ∨
    (⌜fli = interface.mkOk (go.GoType.PointerType hashMap.ty) #a⌝ ∗
      ∃ (cnt : w64) (sp bwm : GMap w64 w64) (sets : GMap w64 (GMap w64 Unit))
        (fm fw bw : Loc) (FM : GMap w64 Loc),
        structFieldRef hashMap go!"freePagesCount" a ↦ cnt ∗
        structFieldRef hashMap go!"freemaps" a ↦ fm ∗
        structFieldRef hashMap go!"forwardMap" a ↦ fw ∗
        structFieldRef hashMap go!"backwardMap" a ↦ bw ∗
        fm ↦$ FM ∗ ([∗map] _sz ↦ l;st ∈ FM;sets, l ↦$ st) ∗ fw ↦$ sp ∗ bw ↦$ bwm ∗
        ⌜hashOK cnt sp bwm sets free⌝))

/-- **The freelist but its `readonlyTXIDs`** (the writer side's part, `rwR`): `shared`'s
`Interface`, `allocs`, `cache` (the free and pending ids) and `pending`, and the
implementation's free ids. -/
def flPgOwn (fli : GoInterface) (fl : FLPg) : IProp GF :=
  iprop(∃ (a s : Loc) (al ca pe : Loc) (c : GMap w64 Unit) (pp : GMap w64 Loc),
    flImplAt fli a s ∗
    structFieldRef shared go!"Interface" s ↦ fli ∗
    structFieldRef shared go!"allocs" s ↦ al ∗ al ↦$ fl.allocs ∗
    structFieldRef shared go!"cache" s ↦ ca ∗ ca ↦$ c ∗
    structFieldRef shared go!"pending" s ↦ pe ∗ pe ↦$ pp ∗
    ([∗map] _t ↦ p;pd ∈ pp;fl.pending, ⌜p ≠ null⌝ ∗ ownPending p pd) ∗
    flImplOwn fli a fl.free ∗
    ⌜(∀ id, (c !! id).isSome ↔ id ∈ fl.allIds) ∧ fl.WF⌝)

end preds

/-- `fli.m`, a method value of the freelist interface value `fli` (U2): the dynamic type's
method (`nil` panics). What Go's `fl.M(args)` steps to once `MethodResolve Interface.ty "M" fl`
has loaded the interface value; the freelist's interface specs are stated over it. -/
abbrev ifaceCall [GooseExts] [GoGlobalContext] [GoSemanticsFunctions] (fli : GoInterface)
    (m : GoString) : Expr :=
  match fli with
  | GoInterface.nil => Panic "nil interface"
  | GoInterface.ok i => Val #(methods i.ty m i.v)

end bbolt
end EtcdGrove
end Perennial
