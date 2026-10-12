/-
The shape (`WriteTxShape.lean`'s `txShape`) of the write transaction `beginRWTx` begins
(`WriteTxInit.lean`): a new ghost map of the view's page ids (`ghost_map_alloc`) gives the
authority and a token per page; the root bucket, with no node and no opened child, takes the
tokens of its whole tree (the others are dropped: the view has no other page, `treeHas_treePages`),
and its keys are the current tree's (`treeStrict`).
-/
module

public import Proof.go_etcd_io.bbolt.WriteTxInit
public import Proof.go_etcd_io.bbolt.ShapeMat
public import Proof.go_etcd_io.bbolt.DBBegin

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [ext : FfiSyntax]

/-- The pages of a tree reach each other in the tree's pages alone. -/
theorem treeHas_treePages (P : GMap Nat (List w8)) (r : Nat) :
    ∀ a id, treeHas P a id → (∀ x, treeHas P a x → treeHas P r x) → treeHas (treePages P r) a id := by
  intro a id h
  have hlk : ∀ x pg, P !! x = some pg → treeHas P r x → treePages P r !! x = some pg := by
    intro x pg hx hr
    unfold treePages
    rw [GMap.lookup_filter, hx]
    simp [Option.filter, hr]
  induction h using treeHas.rec
    (motive_2 := fun pg id _ => (∀ x, pageHas P pg x → treeHas P r x) → pageHas (treePages P r) pg id)
    (motive_3 := fun v id _ => (∀ x, bucketHas P v x → treeHas P r x) → bucketHas (treePages P r) v id) with
  | root a pg hpg =>
    intro hs
    exact treeHas.root a pg (hlk a pg hpg (hs a (treeHas.root a pg hpg)))
  | sub a pg id hpg _ ih =>
    intro hs
    exact treeHas.sub a pg id (hlk a pg hpg (hs a (treeHas.root a pg hpg)))
      (ih fun x hx => hs x (treeHas.sub a pg x hpg hx))
  | child pg i id hb hi _ ih =>
    rename_i hs
    exact pageHas.child pg i id hb hi (ih fun x hx => hs x (pageHas.child pg i x hb hi hx))
  | bucket pg i id hl hi hf _ ih =>
    rename_i hs
    exact pageHas.bucket pg i id hl hi hf (ih fun x hx => hs x (pageHas.bucket pg i x hl hi hf hx))
  | file v id h0 _ ih =>
    rename_i hs
    exact bucketHas.file v id h0 (ih fun x hx => hs x (bucketHas.file v x h0 hx))
  | inline v id h0 _ ih =>
    rename_i hs
    exact bucketHas.inline v id h0 (ih fun x hx => hs x (bucketHas.inline v x h0 hx))

/-- Every page of a tree's pages is a page of the tree (in them). -/
theorem treePages_has (P : GMap Nat (List w8)) (r id : Nat) (h : (treePages P r !! id).isSome) :
    treeHas (treePages P r) r id := by
  have hr : treeHas P r id := by
    unfold treePages at h
    rw [GMap.lookup_filter] at h
    cases hp : P !! id with
    | none => rw [hp] at h; cases h
    | some pg =>
      rw [hp] at h
      simp only [Option.filter] at h
      by_cases ht : treeHas P r id
      · exact ht
      · simp [ht] at h
  exact treeHas_treePages P r r id hr (fun _ h => h)

end pure

section shape
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]

/-- A transaction whose only bucket has no node and no opened child, its keys the tree's, has a
shape. -/
theorem txShape_alloc (W : WView) (T : WTx) (bl : Loc) (B : BRec) (hbs : T.bs = {[bl := B]})
    (hrn : B.bv.rootNode' = null) (hbm : B.bm = ∅) (hns : B.ns = ∅)
    (htk : B.ib.root' ≠ W64 0 → treeKeys W.pages (uint.nat B.ib.root') none none) :
    ⊢ |==> ∃ γ, txShape (GF := GF) γ W T := by
  imod ghost_map_alloc (GF := GF) (Iris.Std.PartialMap.map (fun _ => ()) W.pages) with ⟨%γ, Ha, Hs⟩
  have hmap : ([∗map] k ↦ v ∈ Iris.Std.PartialMap.map (fun _ => ()) W.pages, (k ↪[γ] v : IProp GF)) =
      [∗map] k ↦ _v ∈ W.pages, (k ↪[γ] () : IProp GF) :=
    Iris.Algebra.BigOpM.bigOpM_map_eq (fun _ => ()) (fun k v => (k ↪[γ] v : IProp GF)) W.pages
  ihave Hs := (show ([∗map] k ↦ v ∈ Iris.Std.PartialMap.map (fun _ => ()) W.pages,
      (k ↪[γ] v : IProp GF)) ⊢ [∗map] k ↦ _v ∈ W.pages, (k ↪[γ] () : IProp GF)
    from hmap ▸ BIBase.Entails.rfl) $$ Hs
  imodintro
  iexists γ
  unfold txShape
  iexists Iris.Std.PartialMap.map (fun _ => ()) W.pages
  iframe Ha
  isplitr
  · ipureintro
    intro id
    show ((W.pages !! id).bind fun v => some ()).isSome ↔ _
    cases W.pages !! id <;> rfl
  rw [hbs]
  isplitl [Hs]
  · iapply (bigSepM_gsingleton (GF := GF) (fun _ B => bktToks γ W B) bl B).2
    unfold bktToks
    rw [if_pos hrn]
    split
    · itrivial
    · unfold xPages
      rw [pgToks_filter γ W.pages]
      iapply (tokB_mono γ W.pages (fun _ => true) _ (fun _ _ => rfl))
      unfold tokB
      simp only [↓reduceIte]
      iexact Hs
  · ipureintro
    intro bl' B' hB'
    rw [GMap.lookup_singleton_Some] at hB'
    obtain ⟨-, rfl⟩ := hB'
    refine ⟨⟨fun _ => (none, none), fun _ hb => htk hb, fun r hr => ?_, fun l r hr => ?_⟩, fun k c hk => ?_⟩
    · rw [hns] at hr; cases hr
    · rw [hns] at hr; cases hr
    · rw [hbm] at hk; cases hk

variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]

theorem txShape_wtxInit (dbl txl ml ibl : Loc) (pm bm nm : GoMap) (w : Reader) (data : Loc)
    (ps : Nat) (v0 v1 : Meta) (lg : GoInterface) (dl : Loc) (fli : GoInterface)
    (hstrict : treeStrict w.pages (uint.nat (curMeta v0 v1).pgid')
      (uint.nat (curMeta v0 v1).root'.root')) :
    ⊢ |==> ∃ γ, txShape (GF := GF) γ (wViewOf dbl w data ps lg dl fli)
      (wtxInitT (hG := hG) txl dbl ml ibl pm bm nm v0 v1) := by
  refine txShape_alloc (GF := GF) (wViewOf dbl w data ps lg dl fli)
    (wtxInitT (hG := hG) txl dbl ml ibl pm bm nm v0 v1) _ _ rfl ?_ rfl rfl ?_
  · simp [txInitOf, newBucketOf]
  · intro _; exact hstrict.2.2

/-- `ownWriteTx_init` with the transaction's shape. -/
theorem ownWriteTx_init_s (dbl txl : Loc) (w : Reader) (data : Loc) (ps : Nat) (v0 v1 : Meta)
    (lg : GoInterface) (dl : Loc) (fli : GoInterface)
    (hhwmw : w.hwm = uint.nat (curMeta v0 v1).pgid')
    (hstrict : treeStrict w.pages (uint.nat (curMeta v0 v1).pgid')
      (uint.nat (curMeta v0 v1).root'.root'))
    (hroot : (curMeta v0 v1).root'.root' ≠ W64 0) (hhwm : 2 ≤ uint.nat (curMeta v0 v1).pgid')
    (hdata : data.locCar ≠ 0) (hps : 80 ≤ ps ∧ ps < 2 ^ 32)
    (hbound : ∀ id pg, w.pages !! id = some pg → id * ps < 281474976710655) (hdbl : dbl ≠ null)
    (hlg : lg = interface.nil ∨ lg = discardIface dl) :
    wtxInit dbl txl w data ps v0 v1 ∗ structFieldRef DB go!"logger" dbl ↦□ lg ∗
      (globalAddr discardLogger ↦□ dl : IProp GF) ∗
      structFieldRef DB go!"freelist" dbl ↦{DFrac.own halfQ} fli ⊢
    |==> ∃ T γ, ownWriteTx (wViewOf dbl w data ps lg dl fli) txl T ∗
      txShape γ (wViewOf dbl w data ps lg dl fli) T := by
  iintro ⟨Hi, #Hlg, #Hdl, Hfl⟩
  unfold wtxInit
  icases Hi with ⟨%ml, %ibl, %pm, %bm, %nm, Ht, Hml, Hibl, Hpm, Hbm, Hnm, Hdata, #Hps, Hpv⟩
  imod (txShape_wtxInit (GF := GF) dbl txl ml ibl pm bm nm w data ps v0 v1 lg dl fli hstrict) with
    ⟨%γ, Hsh⟩
  imodintro
  icases (TxW_split_root _ _ _).1 $$ Ht with ⟨Hroot, Hrest⟩
  iexists wtxInitT txl dbl ml ibl pm bm nm v0 v1, γ
  iframe Hsh
  unfold ownWriteTx ownWriteTxG wView
  simp only [wtxInitT, wViewOf, txInitOf, newBucketOf]
  iframe Hrest Hml Hpm Hdata Hpv Hfl
  iframe #
  isplitl [Hroot Hibl Hbm Hnm]
  · isplitl []
    · iapply BigSepM.bigSepM_empty.2; iempintro
    iapply (bigSepM_gsingleton _ _ _).2
    unfold bktOwn pageOwn
    simp only [txInitOf, newBucketOf]
    iframe
    isplitl []
    · simp only [ite_true]; itrivial
    iapply BigSepM.bigSepM_empty.2; iempintro
  ipureintro
  refine ⟨hlg, ⟨hdata, hps.1, hps.2, hbound, hstrict.2.1⟩, ?_⟩
  refine ⟨by simp [txInitOf], by simp [txInitOf], hdbl, rfl, by rw [txMetaOf_pgid]; exact hhwm, by rw [txMetaOf_pgid]; simp [wViewOf, hhwmw],
    by rw [GMap.lookup_singleton]; rfl, ?_⟩
  intro bl B hB
  rw [GMap.lookup_singleton_Some] at hB
  obtain ⟨-, rfl⟩ := hB
  refine ⟨by simp [txInitOf, newBucketOf], ?_, by simp⟩
  rw [txMetaOf_pgid]
  have hlt : uint.nat (curMeta v0 v1).root'.root' < uint.nat (curMeta v0 v1).pgid' := by
    cases hstrict.1 with
    | page _ _ hlt _ _ _ => exact hlt
  unfold bktClean
  simp only
  refine ⟨fun h _ => absurd h hroot, fun _ => ⟨hlt, fun _ => hstrict.1⟩, fun _ => ⟨trivial, trivial⟩,
    fun h => absurd rfl h, by simp, fun _ => trivial, fun h => absurd h hroot, by simp, ?_, ?_⟩
  · intro l1 i1 c1 _ _ _ h; obtain ⟨r, _, h, _⟩ := h; simp at h
  · intro l i c h; obtain ⟨r, _, h, _⟩ := h; simp at h

/-- `ownWriteTx_begin` with the transaction's shape. -/
theorem ownWriteTx_begin_s (dbl txl : Loc) (w : Reader) (data : Loc) (ps : Nat) (v0 v1 : Meta)
    (lg : GoInterface) (dl : Loc) (fli : GoInterface) (h : wtxOK dbl w data ps v0 v1)
    (hlg : lg = interface.nil ∨ lg = discardIface dl) :
    wtxInit dbl txl w data ps v0 v1 ∗ structFieldRef DB go!"logger" dbl ↦□ lg ∗
      (globalAddr discardLogger ↦□ dl : IProp GF) ∗
      structFieldRef DB go!"freelist" dbl ↦{DFrac.own halfQ} fli ⊢
    |==> ∃ T γ, ownWriteTx (wViewOf dbl w data ps lg dl fli) txl T ∗
      txShape γ (wViewOf dbl w data ps lg dl fli) T :=
  ownWriteTx_init_s dbl txl w data ps v0 v1 lg dl fli h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1
    h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2 hlg

/-- A new writer's view (`newReader`) has no page but its tree's. -/
theorem newReader_treeHas (σ : DBState) (v0 v1 : Meta) (q : Qp) (id : Nat)
    (h : ((newReader σ v0 v1 q).pages !! id).isSome) :
    treeHas (newReader σ v0 v1 q).pages (newReader σ v0 v1 q).root id :=
  treePages_has _ _ id h

end shape

end bbolt
end EtcdGrove
end Perennial
