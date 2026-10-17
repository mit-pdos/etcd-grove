/-
The Go values of the mvcc KV core's model (`Model.lean`): `mvcc.Revision` as `Rev`, and the
representation predicates of a key index (`keyIndex`, `generation`). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Base
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Model

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section defs
variable [ext : FfiSyntax] [GoGlobalContext]

/-- The model of a Go `Revision` value. -/
def revOf (r : Revision) : Rev := ⟨r.Main', r.Sub'⟩

/-- The Go `Revision` value of a model revision. -/
def revVal (r : Rev) : Revision := ⟨r.main, r.sub⟩

@[simp] theorem revOf_revVal (r : Rev) : revOf (revVal r) = r := rfl
@[simp] theorem revVal_revOf (r : Revision) : revVal (revOf r) = r := rfl
@[simp] theorem revVal_main (r : Rev) : (revVal r).Main' = r.main := rfl
@[simp] theorem revVal_sub (r : Rev) : (revVal r).Sub' = r.sub := rfl

@[simp] theorem revVal_zero : revVal Rev.zero = zero_val Revision := rfl
@[simp] theorem revVal_mk (a b : w64) : revVal ⟨a, b⟩ = Revision.mk a b := rfl
@[simp] theorem revOf_main (r : Revision) : (revOf r).main = r.Main' := rfl
@[simp] theorem revOf_sub (r : Revision) : (revOf r).sub = r.Sub' := rfl

/-- The Go `revisionLease` value of a model revision, with its lease `lf r` (the key index's
lease function, `ownGen`). -/
def rlVal (lf : Rev → w64) (r : Rev) : revisionLease := ⟨revVal r, lf r⟩

@[simp] theorem rlVal_revision (lf : Rev → w64) (r : Rev) : (rlVal lf r).revision' = revVal r := rfl
@[simp] theorem rlVal_leaseID (lf : Rev → w64) (r : Rev) : (rlVal lf r).leaseID' = lf r := rfl

/-- What `keyIndex.get` returns (`modified, created, ver, leaseID, err`), with `lf` the key
index's leases and `e` the value of `ErrRevisionNotFound`. -/
def kiGetVal (ki : KeyIndex) (lf : Rev → w64) (atRev : w64) (e : GoInterface) : val :=
  match kiGet ki atRev with
  | some (m, c, v) =>
    PairV (PairV (PairV (PairV #(revVal m) #(revVal c)) #v) #(lf m)) #(GoInterface.nil)
  | none => PairV (PairV (PairV (PairV #(zero_val Revision) #(zero_val Revision)) #(W64 0))
      #(W64 0)) #e

end defs

section addrs
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- The pointer `findGeneration` returns: `nil`, or the address of the generation at `i`. -/
def genPtr (gs : GoSlice) : Option Nat → Loc
  | none => null
  | some i => sliceIndexRef generation (i : Int) gs

end addrs

section inj
variable [FfiSyntax] [GoGlobalContext] [GoLocalContext] [GoSemanticsFunctions]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- A `Revision` value determines its fields (its fields' loads are deterministic): the
`available` map's keys (`map[Revision]struct{}`) are compared by value. -/
instance revision_intoValInj : go.IntoValInj Revision where
  intoVal_inj x y h := by
    have hm : ∀ z : Revision, is_go_step_pure (StructFieldGet Revision.underlying go!"Main")
        #z = Eq (Val #(z.Main')) := fun z =>
      (Revision.TypeAssumptions.get_Main z).isGoStep_det_internal.isGoStep_pure_det
    have hs : ∀ z : Revision, is_go_step_pure (StructFieldGet Revision.underlying go!"Sub")
        #z = Eq (Val #(z.Sub')) := fun z =>
      (Revision.TypeAssumptions.get_Sub z).isGoStep_det_internal.isGoStep_pure_det
    have e1 := hm x
    rw [h, hm y] at e1
    have e2 := hs x
    rw [h, hs y] at e2
    have f1 : Val #(x.Main') = Val #(y.Main') := by
      have := congrFun e1 (Val #(x.Main')); simp only [eq_iff_iff, iff_true] at this; exact this.symm
    have f2 : Val #(x.Sub') = Val #(y.Sub') := by
      have := congrFun e2 (Val #(x.Sub')); simp only [eq_iff_iff, iff_true] at this; exact this.symm
    injection f1 with f1
    injection f2 with f2
    cases x; cases y
    simp only [Revision.mk.injEq]
    exact ⟨GoGlobalContext.intoVal_inj_w64 f1, GoGlobalContext.intoVal_inj_w64 f2⟩

end inj

/-! ## Key indexes (`key_index.go`) -/

section reprs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- The Go `generation` value `gv` holds the model generation `gm`: its `ver` and `created`,
and its revisions in the slice `revs` (at fraction `dq`, with the slice's capacity at the same
fraction: `put` appends to it), each with its lease `lf r` (`revisionLease`). The model
generation has no leases: the lease of a revision is a function of the revision (of the change
it is the revision of: `evLease`), so `lf` is one function for the whole index. -/
def ownGen (gv : generation) (gm : Gen) (lf : Rev → w64) (dq : DFrac) : IProp GF :=
  iprop(⌜gv.ver' = gm.ver ∧ gv.created' = revVal gm.created⌝ ∗
    gv.revs' ↦*{dq} gm.revs.map (rlVal lf) ∗ ownSliceCap revisionLease gv.revs' dq)

/-- A `generation` points-to as its fields (loads through a fractional struct points-to need
the field's own points-to). -/
theorem gen_split (g : Loc) (gv : generation) (dq : DFrac) :
    (g ↦{dq} gv : IProp GF) ⊢
      g.[generation, go!"ver"] ↦{dq} gv.ver' ∗ g.[generation, go!"created"] ↦{dq} gv.created' ∗
      g.[generation, go!"revs"] ↦{dq} gv.revs' ∗ ⌜g ≠ null⌝ := by
  iintro H
  ihave %Hn := typedPointsto_not_null _ _ _ $$ H
  icases typedPointsto_split _ _ _ $$ H with H
  simp only [TypedPointsto.typedPointstoDef]
  iNamed H
  iframe ver created revs
  ipureintro; exact Hn

/-- The fields of a `generation` as its points-to. -/
theorem gen_combine (g : Loc) (gv : generation) (dq : DFrac) (h : g ≠ null) :
    g.[generation, go!"ver"] ↦{dq} gv.ver' ∗ g.[generation, go!"created"] ↦{dq} gv.created' ∗
      g.[generation, go!"revs"] ↦{dq} gv.revs' ⊢ (g ↦{dq} gv : IProp GF) := by
  iintro ⟨Hv, Hc, Hr⟩
  iapply typedPointsto_combine _ _ _ h
  simp only [TypedPointsto.typedPointstoDef]
  iframe Hv Hc Hr

/-- The fields of a `generation`, by value, as its points-to. -/
theorem gen_combine' (g : Loc) (a : w64) (b : Revision) (c : GoSlice) (dq : DFrac) (h : g ≠ null) :
    g.[generation, go!"ver"] ↦{dq} a ∗ g.[generation, go!"created"] ↦{dq} b ∗
      g.[generation, go!"revs"] ↦{dq} c ⊢ (g ↦{dq} (generation.mk a b c) : IProp GF) :=
  gen_combine g (generation.mk a b c) dq h

/-- A `Revision` points-to as its fields. -/
theorem rev_split (l : Loc) (r : Revision) (dq : DFrac) :
    (l ↦{dq} r : IProp GF) ⊢
      l.[Revision, go!"Main"] ↦{dq} r.Main' ∗ l.[Revision, go!"Sub"] ↦{dq} r.Sub' ∗ ⌜l ≠ null⌝ := by
  iintro H
  ihave %Hn := typedPointsto_not_null _ _ _ $$ H
  icases typedPointsto_split _ _ _ $$ H with H
  simp only [TypedPointsto.typedPointstoDef]
  iNamed H
  iframe Main Sub
  ipureintro; exact Hn

/-- The fields of a `Revision` as its points-to. -/
theorem rev_combine (l : Loc) (r : Revision) (dq : DFrac) (h : l ≠ null) :
    l.[Revision, go!"Main"] ↦{dq} r.Main' ∗ l.[Revision, go!"Sub"] ↦{dq} r.Sub' ⊢
      (l ↦{dq} r : IProp GF) := by
  iintro ⟨Hm, Hs⟩
  iapply typedPointsto_combine _ _ _ h
  simp only [TypedPointsto.typedPointstoDef]
  iframe Hm Hs

/-- A `revisionLease` points-to as its fields. -/
theorem rl_split (l : Loc) (v : revisionLease) (dq : DFrac) :
    (l ↦{dq} v : IProp GF) ⊢
      l.[revisionLease, go!"revision"] ↦{dq} v.revision' ∗
        l.[revisionLease, go!"leaseID"] ↦{dq} v.leaseID' ∗ ⌜l ≠ null⌝ := by
  iintro H
  ihave %Hn := typedPointsto_not_null _ _ _ $$ H
  icases typedPointsto_split _ _ _ $$ H with H
  simp only [TypedPointsto.typedPointstoDef]
  iNamed H
  iframe revision leaseID
  ipureintro; exact Hn

/-- The fields of a `revisionLease` as its points-to. -/
theorem rl_combine (l : Loc) (v : revisionLease) (dq : DFrac) (h : l ≠ null) :
    l.[revisionLease, go!"revision"] ↦{dq} v.revision' ∗
      l.[revisionLease, go!"leaseID"] ↦{dq} v.leaseID' ⊢ (l ↦{dq} v : IProp GF) := by
  iintro ⟨Hm, Hs⟩
  iapply typedPointsto_combine _ _ _ h
  simp only [TypedPointsto.typedPointstoDef]
  iframe Hm Hs

/-- The `Revision` of a slice element `&revs[i]` (a `revisionLease`), as its two fields. -/
theorem rlRev_split (l : Loc) (v : revisionLease) (dq : DFrac) :
    (l ↦{dq} v : IProp GF) ⊢
      (structFieldRef revisionLease go!"revision" l).[Revision, go!"Main"] ↦{dq} v.revision'.Main' ∗
      (structFieldRef revisionLease go!"revision" l).[Revision, go!"Sub"] ↦{dq} v.revision'.Sub' ∗
      l.[revisionLease, go!"leaseID"] ↦{dq} v.leaseID' ∗
      ⌜l ≠ null ∧ structFieldRef revisionLease go!"revision" l ≠ null⌝ := by
  iintro H
  icases rl_split _ _ _ $$ H with ⟨Hr, Hl, %Hn⟩
  icases rev_split _ _ _ $$ Hr with ⟨Hm, Hs, %Hn'⟩
  iframe Hm Hs Hl
  ipureintro; exact ⟨Hn, Hn'⟩

theorem rlRev_combine (l : Loc) (v : revisionLease) (dq : DFrac)
    (h : l ≠ null ∧ structFieldRef revisionLease go!"revision" l ≠ null) :
    (structFieldRef revisionLease go!"revision" l).[Revision, go!"Main"] ↦{dq} v.revision'.Main' ∗
      (structFieldRef revisionLease go!"revision" l).[Revision, go!"Sub"] ↦{dq} v.revision'.Sub' ∗
      l.[revisionLease, go!"leaseID"] ↦{dq} v.leaseID' ⊢ (l ↦{dq} v : IProp GF) := by
  iintro ⟨Hm, Hs, Hl⟩
  iapply rl_combine _ _ _ h.1
  iframe Hl
  iapply rev_combine _ _ _ h.2
  iframe Hm Hs

/-- The Go values `gvs` hold the model generations `gens`, in order. -/
def ownGensL (lf : Rev → w64) (dq : DFrac) : List generation → List Gen → IProp GF
  | [], [] => iprop(True)
  | gv :: gvs, gm :: gens => iprop(ownGen gv gm lf dq ∗ ownGensL lf dq gvs gens)
  | [], _ :: _ => iprop(False)
  | _ :: _, [] => iprop(False)

theorem ownGensL_len (lf : Rev → w64) (dq : DFrac) : ∀ (gvs : List generation) (gens : List Gen),
    ownGensL (GF := GF) lf dq gvs gens ⊢ ⌜gvs.length = gens.length⌝
  | [], [] => by simp [ownGensL]
  | gv :: gvs, gm :: gens => by
    simp only [ownGensL]
    iintro ⟨-, H⟩
    ihave %H := ownGensL_len lf dq gvs gens $$ H
    ipureintro; simp [H]
  | [], _ :: _ => by simp [ownGensL]
  | _ :: _, [] => by simp [ownGensL]

/-- The `i`-th generation, borrowed; given back with a new value and model, the lists are
`set`. -/
theorem ownGensL_acc (lf : Rev → w64) (dq : DFrac) : ∀ (gvs : List generation) (gens : List Gen) (i : Nat)
    (gv : generation) (gm : Gen), gvs[i]? = some gv → gens[i]? = some gm →
    ownGensL (GF := GF) lf dq gvs gens ⊢ ownGen gv gm lf dq ∗
      (∀ (gv' : generation) (gm' : Gen), ownGen gv' gm' lf dq -∗
        ownGensL lf dq (gvs.set i gv') (gens.set i gm'))
  | gv0 :: gvs, gm0 :: gens, 0, gv, gm, h1, h2 => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h1 h2
    subst h1 h2
    simp only [ownGensL, List.set_cons_zero]
    iintro ⟨H, Hrest⟩
    iframe H
    iintro %gv' %gm' H'
    iframe H' Hrest
  | gv0 :: gvs, gm0 :: gens, i + 1, gv, gm, h1, h2 => by
    simp only [List.getElem?_cons_succ] at h1 h2
    simp only [ownGensL, List.set_cons_succ]
    iintro ⟨H0, Hrest⟩
    icases ownGensL_acc lf dq gvs gens i gv gm h1 h2 $$ Hrest with ⟨H, Hback⟩
    iframe H
    iintro %gv' %gm' H'
    iframe H0
    iapply Hback $$ H'
  | [], _, _, _, _, h1, _ => by simp at h1
  | _ :: _, [], _, _, _, _, h2 => by simp at h2

/-- A generation appended to the lists. -/
theorem ownGensL_app (lf : Rev → w64) (dq : DFrac) : ∀ (gvs : List generation) (gens : List Gen) (gv : generation)
    (gm : Gen),
    ownGensL (GF := GF) lf dq gvs gens ∗ ownGen gv gm lf dq ⊢ ownGensL lf dq (gvs ++ [gv]) (gens ++ [gm])
  | [], [], gv, gm => by
    simp only [List.nil_append, ownGensL]
    iintro ⟨-, H⟩
    iframe H
  | gv0 :: gvs, gm0 :: gens, gv, gm => by
    simp only [List.cons_append, ownGensL]
    iintro ⟨⟨H0, Hrest⟩, H⟩
    iframe H0
    iapply ownGensL_app lf dq gvs gens gv gm
    iframe Hrest H
  | [], _ :: _, _, _ => by
    simp only [ownGensL]
    iintro ⟨%h, -⟩
    exact h.elim
  | _ :: _, [], _, _ => by
    simp only [ownGensL]
    iintro ⟨%h, -⟩
    exact h.elim

/-- The generations slice `gs` holds the model generations `gens`, in order. -/
def ownGens (gs : GoSlice) (gens : List Gen) (lf : Rev → w64) (dq : DFrac) : IProp GF :=
  iprop(∃ gvs : List generation,
    gs ↦*{dq} gvs ∗ ownSliceCap generation gs dq ∗ ownGensL lf dq gvs gens)

theorem ownGens_len (gs : GoSlice) (gens : List Gen) (lf : Rev → w64) (dq : DFrac) :
    ownGens (GF := GF) gs gens lf dq ⊢ ⌜gens.length = sint.nat gs.len ∧ 0 ≤ sint.Z gs.len⌝ := by
  unfold ownGens
  iintro ⟨%gvs, Hgvs, -, H⟩
  ihave %Hlen := ownGensL_len _ _ _ $$ H
  ihave %Hl := ownSlice_len _ _ _ $$ Hgvs
  ipureintro; rw [← Hlen]; exact Hl

/-- The `i`-th generation, borrowed: its Go value's points-to (the address `&gs[i]`) and its
model; given back with a new value holding a new model `gm'`, the slice holds `gens.set i gm'`. -/
theorem ownGens_acc (gs : GoSlice) (gens : List Gen) (lf : Rev → w64) (dq : DFrac) (i : Nat) (gm : Gen)
    (h : gens[i]? = some gm) :
    ownGens (GF := GF) gs gens lf dq ⊢ ∃ gv : generation,
      sliceIndexRef generation (i : Int) gs ↦{dq} gv ∗ ownGen gv gm lf dq ∗
      (∀ (gv' : generation) (gm' : Gen), sliceIndexRef generation (i : Int) gs ↦{dq} gv' -∗
        ownGen gv' gm' lf dq -∗ ownGens gs (gens.set i gm') lf dq) := by
  unfold ownGens
  iintro ⟨%gvs, Hgvs, Hcap, Hall⟩
  ihave %Hlen := ownGensL_len _ _ _ $$ Hall
  have hi : i < gvs.length := by
    rw [Hlen]; exact (List.getElem?_eq_some_iff.1 h).1
  obtain ⟨gv, hgv⟩ : ∃ gv, gvs[i]? = some gv := ⟨_, List.getElem?_eq_getElem hi⟩
  icases ownSlice_elem_acc (i : Int) gv gs dq gvs (by omega) (by simpa using hgv) $$ Hgvs
    with ⟨Hel, Hback⟩
  icases ownGensL_acc lf dq gvs gens i gv gm hgv h $$ Hall with ⟨Hg, Hrest⟩
  iexists gv
  iframe Hel Hg
  iintro %gv' %gm' Hel' Hg'
  iexists gvs.set i gv'
  ispecialize Hback $$ %gv' Hel'
  rw [show ((i : Int)).toNat = i from rfl]
  iframe Hback Hcap
  iapply Hrest $$ Hg'

/-- `ownGens_acc` at a Go index (an `Int`). -/
theorem ownGens_acc_z (gs : GoSlice) (gens : List Gen) (lf : Rev → w64) (dq : DFrac) (i : Int) (gm : Gen)
    (hi : 0 ≤ i) (h : gens[i.toNat]? = some gm) :
    ownGens (GF := GF) gs gens lf dq ⊢ ∃ gv : generation,
      sliceIndexRef generation i gs ↦{dq} gv ∗ ownGen gv gm lf dq ∗
      (∀ (gv' : generation) (gm' : Gen), sliceIndexRef generation i gs ↦{dq} gv' -∗
        ownGen gv' gm' lf dq -∗ ownGens gs (gens.set i.toNat gm') lf dq) := by
  have e : i = ((i.toNat : Nat) : Int) := by omega
  rw [e]
  exact ownGens_acc gs gens lf dq i.toNat gm h

/-- The last revision of a generation, as the slice holds it. -/
theorem revs_last (lf : Rev → w64) (revs : List Rev) (len : w64) (hne : revs ≠ [])
    (hlen : revs.length = sint.nat len) :
    (revs.map (rlVal lf))[(sint.Z (len - W64 1)).toNat]? =
      some (rlVal lf (revs.getLastD Rev.zero)) := by
  rw [List.getElem?_map, List.getLastD_eq_getLast?, List.getLast?_eq_getElem?]
  have hpos : 0 < revs.length := List.length_pos_iff.2 hne
  rw [show (sint.Z (len - W64 1)).toNat = revs.length - 1 by rw [hlen]; word]
  obtain ⟨r, hr⟩ : ∃ r, revs[revs.length - 1]? = some r := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  rw [hr]; rfl

/-- The first revision of a generation, as the slice holds it. -/
theorem revs_first (lf : Rev → w64) (revs : List Rev) (hne : revs ≠ []) :
    (revs.map (rlVal lf))[(sint.Z (W64 0)).toNat]? = some (rlVal lf (revs.headD Rev.zero)) := by
  rw [List.getElem?_map, List.headD_eq_head?, List.head?_eq_getElem?]
  obtain ⟨r, hr⟩ : ∃ r, revs[0]? = some r :=
    ⟨_, List.getElem?_eq_getElem (List.length_pos_iff.2 hne)⟩
  rw [show (sint.Z (W64 0)).toNat = 0 from rfl, hr]; rfl

/-- `p` is a `*keyIndex` of key `k`, for good: the key is set by `&keyIndex{key: k}` and
never written. -/
def kiKey (p : Loc) (k : GoString) : IProp GF :=
  iprop(∃ ks : GoSlice, p.[keyIndex, go!"key"] ↦□ ks ∗ ks ↦*□ k)

instance kiKey_persistent (p : Loc) (k : GoString) : Persistent (kiKey (GF := GF) p k) := by
  unfold kiKey; infer_instance

/-- The mutable part of the `*keyIndex` `p`: `modified` and its generations slice `gs`
(`ownGens`), holding `ki` with the leases `lf`, at fraction `dq`. -/
def ownKi (p : Loc) (gs : GoSlice) (ki : KeyIndex) (lf : Rev → w64) (dq : DFrac) : IProp GF :=
  iprop(p.[keyIndex, go!"modified"] ↦{dq} revVal ki.modified ∗
    p.[keyIndex, go!"generations"] ↦{dq} gs ∗ ownGens gs ki.gens lf dq)

/-- A `Revision` is a safe map key: comparing it with itself (field by field) does not panic. -/
instance revision_safeMapKey (r : Revision) : SafeMapKey (GF := GF) Revision.ty r where
  wp_go_eq_safe_map_key s E Φ := by
    iintro HΦ
    wp_pures
    iapply HΦ

/-- The triple of the function `walk` is given (`get`'s closure): on a revision, it returns
whether the predicate `p` holds of it. -/
def walkFnSpec (f : GoFunc) (p : Rev → Bool) : IProp GF :=
  iprop(□ ∀ r : Revision, {{ True }} (App (Val #f) (Val #r)) {{ RET #(p (revOf r)); True }})

instance walkFnSpec_persistent (f : GoFunc) (p : Rev → Bool) :
    Persistent (walkFnSpec (GF := GF) f p) := by
  unfold walkFnSpec; infer_instance

/-- The triple of an effectful function given to `walk` (`doCompact`'s closure writes the
`available` map): on a revision for which the predicate `p` holds it returns true and keeps the
resource `R`; on one where `p` fails it returns false, turning `R` into `Q` of that revision
(`walk` stops there). -/
def walkFnSpecR (f : GoFunc) (p : Rev → Bool) (R : IProp GF) (Q : Rev → IProp GF) : IProp GF :=
  iprop(□ ∀ r : Revision, {{ R }} (App (Val #f) (Val #r))
    {{ RET #(p (revOf r)); if p (revOf r) then R else Q (revOf r) }})

instance walkFnSpecR_persistent (f : GoFunc) (p : Rev → Bool) (R : IProp GF) (Q : Rev → IProp GF) :
    Persistent (walkFnSpecR (GF := GF) f p R Q) := by
  unfold walkFnSpecR; infer_instance

/-- What `walk` leaves of the closure's resource: `R` if every revision passed `p`, else `Q` of
the revision where it stopped (the last one failing `p`, at `genWalk`). -/
def walkPost (revs : List Rev) (p : Rev → Bool) (R : IProp GF) (Q : Rev → IProp GF) : IProp GF :=
  if genWalk revs p = -1 then R else Q (revs.getD (genWalk revs p).toNat Rev.zero)

/-- A pure closure (`walkFnSpec`) is an effectful one with no resource. -/
theorem walkFnSpecR_of_pure (f : GoFunc) (p : Rev → Bool) :
    walkFnSpec (GF := GF) f p ⊢ walkFnSpecR f p iprop(True) (fun _ => iprop(True)) := by
  unfold walkFnSpec walkFnSpecR
  iintro #Hf
  imodintro
  iintro %r
  wp_start
  wp_apply Hf $$ %r
  iapply HΦ
  split <;> itrivial

end reprs

end mvcc
end EtcdGrove
end Perennial
