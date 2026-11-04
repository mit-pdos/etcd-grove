/-
The freelist's ownership as U2's proofs use it (`notes/bbolt-proof-plan.md`): `flPgOwn`
(`Inv/Freelist.lean`) split into the implementation (`FLImpl`: an `*array` or a `*hashMap`, its
pointer to its `shared` and its own part holding the free ids) and `shared`'s fields but
`readonlyTXIDs` (`ownSh`), with the cache `c`; and the contract an implementation meets for the
methods `shared` calls back through its embedded `Interface` (`FLImpl.Contract`). Ported from
the old proof's `old/bbolt/.../internal/freelist/{Model,ArrayModel,HashModel}.lean`.
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.Model
public import Proof.go_etcd_io.bbolt.Inv.Freelist
public import Proof.go_etcd_io.bbolt.PkgInit

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.freelist

section preds
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

/-- The cache holds exactly the free and pending ids. -/
def cacheOK (c : GMap w64 Unit) (fl : FLPg) : Prop := ∀ id, (c !! id).isSome ↔ id ∈ fl.allIds

/-- `shared`'s fields at `s` but `readonlyTXIDs`: its interface `fli`, `fl`'s allocations and
pending entries, and the cache `c`. -/
def ownShC (s : Loc) (fli : GoInterface) (fl : FLPg) (c : GMap w64 Unit) : IProp GF :=
  iprop(∃ (al ca pe : Loc) (pp : GMap w64 Loc),
    "Hif" ∷ structFieldRef shared go!"Interface" s ↦ fli ∗
    "Hal" ∷ structFieldRef shared go!"allocs" s ↦ al ∗ "Hallocs" ∷ al ↦$ fl.allocs ∗
    "Hca" ∷ structFieldRef shared go!"cache" s ↦ ca ∗ "Hcache" ∷ ca ↦$ c ∗
    "Hpe" ∷ structFieldRef shared go!"pending" s ↦ pe ∗ "Hpending" ∷ pe ↦$ pp ∗
    "Hpds" ∷ ([∗map] _t ↦ p;pd ∈ pp;fl.pending, ownPending p pd))

/-- `ownShC` with its cache up to date and the state well-formed. -/
def ownSh (s : Loc) (fli : GoInterface) (fl : FLPg) : IProp GF :=
  iprop(∃ (c : GMap w64 Unit), ownShC s fli fl c ∗ ⌜cacheOK c fl ∧ fl.WF⌝)

/-- `ownShC` with its cache up to date and the state weakly well-formed. -/
def ownShW (s : Loc) (fli : GoInterface) (fl : FLPg) : IProp GF :=
  iprop(∃ (c : GMap w64 Unit), ownShC s fli fl c ∗ ⌜cacheOK c fl ∧ fl.WFw⌝)

theorem ownSh_w (s : Loc) (fli : GoInterface) (fl : FLPg) :
    ownSh (GF := GF) s fli fl ⊢ ownShW s fli fl := by
  unfold ownSh ownShW
  iintro ⟨%c, H, %Hok⟩
  iexists c; iframe; ipureintro; exact ⟨Hok.1, Hok.2.wfw⟩

theorem ownShW_wf (s : Loc) (fli : GoInterface) (fl : FLPg) (h : fl.WF) :
    ownShW (GF := GF) s fli fl ⊢ ownSh s fli fl := by
  unfold ownSh ownShW
  iintro ⟨%c, H, %Hok⟩
  iexists c; iframe; ipureintro; exact ⟨Hok.1, h⟩

theorem ownSh_wf (s : Loc) (fli : GoInterface) (fl : FLPg) :
    ownSh (GF := GF) s fli fl ⊢ ownSh s fli fl ∗ ⌜fl.WF⌝ := by
  unfold ownSh
  iintro ⟨%c, H, %Hok⟩
  isplitl
  · iexists c; iframe; ipureintro; exact Hok
  · ipureintro; exact Hok.2

/-- An implementation of the freelist interface: the interface value's dynamic type `ity` and
value `iv`, `own free` (its own part, holding the free ids) and `hdl s` (its pointer to its
`shared` at `s`, persistent). -/
structure FLImpl where
  ity : go.GoType
  iv : val
  own : List w64 → IProp GF
  hdl : Loc → IProp GF
  hdl_persistent : ∀ s, Persistent (hdl s)

/-- The interface value of `I`. -/
def FLImpl.iface (I : FLImpl (GF := GF)) : GoInterface := interface.mkOk I.ity I.iv

instance FLImpl.hdl_persistent' (I : FLImpl (GF := GF)) (s : Loc) : Persistent (I.hdl s) :=
  I.hdl_persistent s

/-- `FreeCount()`: the number of free ids. -/
def FLImpl.FreeCountSpec (I : FLImpl (GF := GF)) : Prop :=
  ∀ (free : List w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ I.own free }}
      (App (Val #(methods I.ity go!"FreeCount" I.iv)) (Val #()))
    {{ RET #(W64 (free.length : Int)); I.own free }}

/-- `freePageIds()`: a slice of the free ids, lent until it is given back. -/
def FLImpl.FreePageIdsSpec (I : FLImpl (GF := GF)) : Prop :=
  ∀ (free : List w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ I.own free }}
      (App (Val #(methods I.ity go!"go.etcd.io/bbolt/internal/freelist.freePageIds" I.iv))
        (Val #()))
    {{ (r : GoSlice), RET #r; r ↦* free ∗ (r ↦* free -∗ I.own free) }}

/-- `Init(ids)`, from and to weakly well-formed states (the ids may be pending, as in
`Reload`): the free ids become `ids` (the slice is consumed), the cache rebuilt. Of no ids,
the old free ids must all be pending: `hashMap.Init` then returns before `reindex`, keeping the
old cache. -/
def FLImpl.InitSpec (I : FLImpl (GF := GF)) : Prop :=
  ∀ (s : Loc) (fl : FLPg) (ids : GoSlice) (xs : List w64),
    ({ fl with free := xs } : FLPg).WFw → (xs ≠ [] ∨ ∀ x ∈ fl.free, x ∈ fl.pendingIds) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗
        I.hdl s ∗ ownShW s I.iface fl ∗ I.own fl.free ∗ ids ↦* xs ∗
        ownSliceCap w64 ids (DFrac.own 1) }}
      (App (Val #(methods I.ity go!"Init" I.iv)) (Val #ids))
    {{ RET #(); ownShW s I.iface { fl with free := xs } ∗ I.own xs }}

/-- `mergeSpans(ids)`: the ids (distinct, at least 2, not free) become free (the slice is
consumed: an implementation may keep it), sorted. -/
def FLImpl.MergeSpansSpec (I : FLImpl (GF := GF)) : Prop :=
  ∀ (free : List w64) (ids : GoSlice) (ys : List w64),
    PgidsIncr free → (free ++ ys).Nodup → (∀ y ∈ ys, 2 ≤ y.toNat) →
    free.length + ys.length < 2 ^ 63 →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗
        I.own free ∗ ids ↦* ys ∗ ownSliceCap w64 ids (DFrac.own 1) }}
      (App (Val #(methods I.ity go!"go.etcd.io/bbolt/internal/freelist.mergeSpans" I.iv))
        (Val #ids))
    {{ RET #(); I.own (sortPgids (free ++ ys)) }}

/-- The specs of the methods `shared`'s methods call back through its `Interface`. -/
structure FLImpl.Contract (I : FLImpl (GF := GF)) : Prop where
  freeCount : I.FreeCountSpec
  freePageIds : I.FreePageIdsSpec
  init : I.InitSpec
  mergeSpans : I.MergeSpansSpec

/-! ## The two implementations -/

/-- The `*array` at `a`, its `shared` at `s`. -/
def arrayImpl (a : Loc) : FLImpl (GF := GF) where
  ity := go.GoType.PointerType array'.ty
  iv := #a
  own free := iprop(∃ sl : GoSlice, structFieldRef array' go!"ids" a ↦ sl ∗ sl ↦* free ∗
    ownSliceCap w64 sl (DFrac.own 1))
  hdl s := iprop(structFieldRef array' go!"shared" a ↦□ s)
  hdl_persistent _ := by infer_instance

/-- The `*hashMap` at `h`, its `shared` at `s`. -/
def hashImpl (h : Loc) : FLImpl (GF := GF) where
  ity := go.GoType.PointerType hashMap.ty
  iv := #h
  own free := iprop(∃ (cnt : w64) (sp bwm : GMap w64 w64) (sets : GMap w64 (GMap w64 Unit))
      (fm fw bw : Loc) (FM : GMap w64 Loc),
    structFieldRef hashMap go!"freePagesCount" h ↦ cnt ∗
    structFieldRef hashMap go!"freemaps" h ↦ fm ∗
    structFieldRef hashMap go!"forwardMap" h ↦ fw ∗
    structFieldRef hashMap go!"backwardMap" h ↦ bw ∗
    fm ↦$ FM ∗ ([∗map] _sz ↦ l;st ∈ FM;sets, l ↦$ st) ∗ fw ↦$ sp ∗ bw ↦$ bwm ∗
    ⌜hashOK cnt sp bwm sets free⌝)
  hdl s := iprop(structFieldRef hashMap go!"shared" h ↦□ s)
  hdl_persistent _ := by infer_instance

end preds

end bbolt
end EtcdGrove
end Perennial
