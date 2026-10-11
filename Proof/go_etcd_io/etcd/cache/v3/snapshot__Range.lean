/-
Proof of `Spec/snapshot__Range.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.snapshot__Range
public import Spec.go_etcd_io.etcd.cache.v3.probeItemFromKey
public import Spec.go_etcd_io.etcd.cache.v3.isPrefixScan
public import Spec.k8s_io.utils.third_party.forked.golang.btree.BTree__Get
public import Spec.k8s_io.utils.third_party.forked.golang.btree.BTree__AscendGreaterOrEqual
public import Spec.k8s_io.utils.third_party.forked.golang.btree.BTree__AscendRange

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3 k8s_io.utils.third_party.forked.golang

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- On a map sorted by key, `Get` of key `k` (as a list) is the entries with key `k`. -/
theorem snapshot_Range_find_eq_filter (k : GoString) (l0 : Loc) (m : KvMap)
    (hs : m.Pairwise kvLess) :
    (match btFind kvLess (k, l0) m with | some e => [e] | none => []) =
      m.filter (fun e => decide (e.1 = k)) := by
  induction m with
  | nil => simp [btFind]
  | cons w ws ih =>
    rw [List.pairwise_cons] at hs
    have hgt : ∀ x ∈ ws, go.GoStringLt w.1 x.1 := fun x hx => hs.1 x hx
    unfold btFind
    by_cases h1 : kvLess w (k, l0)
    · rw [ite_eq_left h1, ih hs.2, List.filter_cons]
      have : w.1 ≠ k := fun h => goStringLt_irrefl k (by have := h1; unfold kvLess at this; simpa [h] using this)
      simp [this]
    · rw [ite_eq_right h1]
      by_cases h2 : kvLess (k, l0) w
      · rw [ite_eq_left h2]
        have hk : ∀ x ∈ ws, x.1 ≠ k := fun x hx he =>
          goStringLt_irrefl k (goStringLt_trans h2 (he ▸ hgt x hx))
        have hw : w.1 ≠ k := fun he => goStringLt_irrefl k (by have := h2; unfold kvLess at this; simpa [he] using this)
        rw [List.filter_cons, ite_eq_right (by simpa using hw)]
        symm
        rw [List.filter_eq_nil_iff]
        intro x hx; simpa using hk x hx
      · rw [ite_eq_right h2]
        have hw : w.1 = k := kvLess_equiv h1 h2
        have hk : ∀ x ∈ ws, x.1 ≠ k := fun x hx he => by
          have := hgt x hx; rw [hw, he] at this; exact goStringLt_irrefl k this
        rw [List.filter_cons, ite_eq_left (by simpa using hw)]
        have : List.filter (fun e => decide (e.fst = k)) ws = [] := by
          rw [List.filter_eq_nil_iff]; intro x hx; simpa using hk x hx
        rw [this]

theorem snapshot_Range_ge_eq (k : GoString) (l0 : Loc) (m : KvMap) :
    btAscendGe kvLess (k, l0) m = m.filter (fun e => !decide (go.GoStringLt e.1 k)) := rfl

theorem snapshot_Range_range_eq (k e : GoString) (l0 l1 : Loc) (m : KvMap) :
    btAscendRange kvLess (k, l0) (e, l1) m =
      m.filter (fun x => !decide (go.GoStringLt x.1 k) && decide (go.GoStringLt x.1 e)) := rfl

theorem snapshot_Range_take_succ (l : KvMap) (i : Nat) (v : KvEntry) (h : l[i]? = some v) :
    (l.take (i + 1)).map Prod.snd = (l.take i).map Prod.snd ++ [v.2] := by
  rw [List.take_add_one, h]; simp

-- Loads from read-only struct points-tos: the field-store `AccessStrict` instances (which
-- need `DFrac.own 1`) are found first, so they are switched off here (this proof only loads).
attribute [-instance] snapshot.snapshot_access_store_rev snapshot.snapshot_access_store_tree
  kvItem.kvItem_access_store_key kvItem.kvItem_access_store_kv

theorem snapshot.Range.wp_proof
    (wp_probeItemFromKey : probeItemFromKey.spec (GF := GF) (hG := hG))
    (wp_isPrefixScan : isPrefixScan.spec (GF := GF) (hG := hG))
    (wp_Get : btree.BTree.Get.spec (GF := GF) (hG := hG))
    (wp_AscendGreaterOrEqual : btree.BTree.AscendGreaterOrEqual.spec (GF := GF) (hG := hG))
    (wp_AscendRange : btree.BTree.AscendRange.spec (GF := GF) (hG := hG)) :
    snapshot.Range.spec (GF := GF) (hG := hG) := by
  have wp_Get : btree.BTree.Get.modelSpec (GF := GF) (hG := hG) := btree.BTree.Get.modelSpec_of wp_Get
  have wp_AscendGreaterOrEqual : btree.BTree.AscendGreaterOrEqual.modelSpec (GF := GF) (hG := hG) := btree.BTree.AscendGreaterOrEqual.modelSpec_of wp_AscendGreaterOrEqual
  have wp_AscendRange : btree.BTree.AscendRange.modelSpec (GF := GF) (hG := hG) := btree.BTree.AscendRange.modelSpec_of wp_AscendRange
  intro p h startSl endSl startKey endKey d1 d2
  wp_start as ⟨#Hsnap, Hs, He⟩
  iunfold snapIs at Hsnap
  icases Hsnap with ⟨%t, #Hp, #Ht, #Hkvs, %Hsorted⟩
  wp_auto
  ihave %HlenE := ownSlice_len _ _ _ $$ He
  rw [show (zero_val GoSlice) = slice.nil from rfl]
  ihave Hnil : (slice.nil ↦* ([] : List Loc) : IProp GF) $$ []
  · iapply ownSlice_nil
  ihave Hnilcap : ownSliceCap Loc slice.nil (DFrac.own 1) $$ []
  · iapply ownSliceCap_nil
  wp_if_destruct
  · -- `len(endKey) == 0`: `Get`
    wp_apply wp_probeItemFromKey $$ [$Hs] as %pr ⟨Hs, #Hpr⟩
    wp_apply wp_Get kvItemPtrT t kvItemIs kvLess h.2 DFrac.discard pr (startKey, null) $$ []
      as %item %ok ⟨-, Hres⟩
    · iframe Ht Hpr; ipureintro; exact kvLess_swo
    have HeK : endKey = [] := by
      apply List.eq_nil_of_length_eq_zero
      have : endSl.len = W64 0 := by simpa using Hif.symm
      rw [HlenE.1, this]; rfl
    have Hrange : kvRange startKey endKey h.2 =
        (match btFind kvLess (startKey, null) h.2 with | some e => [e] | none => []) := by
      rw [kvRange, ite_eq_left HeK, snapshot_Range_find_eq_filter _ _ _ Hsorted]
    rw [Hrange]
    have Hmem := fun e => btFind_mem (less := kvLess) (k := (startKey, null)) (items := h.2) (x := e)
    generalize btFind kvLess (startKey, null) h.2 = f at Hmem ⊢
    cases f with
    | none =>
      icases Hres with % ⟨Hok, Hitem⟩
      subst Hok Hitem
      wp_auto
      iapply HΦ
      simp only [List.map_nil]
      iframe Hs He Hnil Hnilcap
      unfold kvsAt; imodintro; iintro %e %He; simp at He
    | some v =>
      icases Hres with ⟨%Hok, #Hit⟩
      subst Hok
      unfold kvItemIs
      wp_auto
      wp_apply wp_slice_literal (V := Loc) [v.2]
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, -⟩
      wp_apply wp_slice_append $$ [$Hnil $Hnilcap $Hsl] as %o ⟨Ho, Hocap, -⟩
      iapply HΦ
      simp only [List.nil_append, List.map_cons, List.map_nil] at *
      iframe Hs He Ho Hocap
      unfold kvsAt; imodintro; iintro %e %He
      simp at He; subst He
      iapply Hkvs; ipureintro; exact Hmem _ rfl
  have HeK : endKey ≠ [] := by
    intro h0
    apply Hif
    have : sint.nat endSl.len = 0 := by rw [← HlenE.1, h0]; rfl
    have : endSl.len = W64 0 := by word
    simp [this]
  wp_apply wp_isPrefixScan $$ [$He] as He
  wp_if_destruct
  · -- `isPrefixScan(endKey)`: `AscendGreaterOrEqual`
    have HeK0 : endKey = [W8 0] := by simpa using Hif
    wp_apply wp_probeItemFromKey $$ [$Hs] as %pr ⟨Hs, #Hpr⟩
    have Hrange : kvRange startKey endKey h.2 = btAscendGe kvLess (startKey, null) h.2 := by
      rw [kvRange, ite_eq_right HeK, ite_eq_left HeK0, snapshot_Range_ge_eq]
    rw [Hrange]
    have Hsub : ∀ e ∈ btAscendGe kvLess (startKey, null) h.2, e ∈ h.2 :=
      fun e he => (List.mem_filter.1 he).1
    wp_apply (wp_AscendGreaterOrEqual kvItemPtrT t kvItemIs kvLess h.2 DFrac.discard pr
      (startKey, null) _
      (fun i => iprop(∃ sl : GoSlice, out_ptr ↦ sl ∗
        sl ↦* (((btAscendGe kvLess (startKey, null) h.2).take i).map Prod.snd) ∗
        ownSliceCap Loc sl (DFrac.own 1))) iprop(False)) $$ [out Hnil Hnilcap] as ⟨-, Hpost⟩
    · iframe Ht Hpr
      isplitr
      · ipureintro; exact kvLess_swo
      isplitl [out Hnil Hnilcap]
      · iexists slice.nil; iframe
      unfold btIterSpec
      iintro %i %q %v %Hv
      wp_start_folded as ⟨⟨%sl, Hout, Hsl, Hcap⟩, #Hit⟩
      unfold kvItemIs
      wp_auto
      wp_apply wp_slice_literal (V := Loc) [v.2]
      isplitr
      · ipureintro; rfl
      iintro %sl2 ⟨Hsl2, -⟩
      wp_apply wp_slice_append $$ [$Hsl $Hcap $Hsl2] as %o ⟨Ho, Hocap, -⟩
      iapply HΦ
      simp only [ite_true]
      iexists o
      rw [snapshot_Range_take_succ _ _ _ Hv]
      iframe
    icases Hpost with (⟨⟩ | ⟨%sl, Hout, Hsl, Hcap⟩)
    rw [List.take_length]
    wp_auto
    iapply HΦ
    iframe Hs He Hsl Hcap
    unfold kvsAt; imodintro; iintro %e %He
    iapply Hkvs; ipureintro; exact Hsub e He
  -- the default: `AscendRange`
  have HeK0 : endKey ≠ [W8 0] := fun h0 => Hif (by simp [h0])
  wp_apply wp_probeItemFromKey $$ [$Hs] as %pr ⟨Hs, #Hpr⟩
  wp_apply wp_probeItemFromKey $$ [$He] as %pe ⟨He, #Hpe⟩
  have Hrange : kvRange startKey endKey h.2 = btAscendRange kvLess (startKey, null) (endKey, null) h.2 := by
    rw [kvRange, ite_eq_right HeK, ite_eq_right HeK0, snapshot_Range_range_eq]
  rw [Hrange]
  have Hsub : ∀ e ∈ btAscendRange kvLess (startKey, null) (endKey, null) h.2, e ∈ h.2 :=
    fun e he => (List.mem_filter.1 he).1
  wp_apply (wp_AscendRange kvItemPtrT t kvItemIs kvLess h.2 DFrac.discard pr pe
    (startKey, null) (endKey, null) _
    (fun i => iprop(∃ sl : GoSlice, out_ptr ↦ sl ∗
      sl ↦* (((btAscendRange kvLess (startKey, null) (endKey, null) h.2).take i).map Prod.snd) ∗
      ownSliceCap Loc sl (DFrac.own 1))) iprop(False)) $$ [out Hnil Hnilcap] as ⟨-, Hpost⟩
  · iframe Ht Hpr Hpe
    isplitr
    · ipureintro; exact kvLess_swo
    isplitl [out Hnil Hnilcap]
    · iexists slice.nil; iframe
    unfold btIterSpec
    iintro %i %q %v %Hv
    wp_start_folded as ⟨⟨%sl, Hout, Hsl, Hcap⟩, #Hit⟩
    unfold kvItemIs
    wp_auto
    wp_apply wp_slice_literal (V := Loc) [v.2]
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    wp_apply wp_slice_append $$ [$Hsl $Hcap $Hsl2] as %o ⟨Ho, Hocap, -⟩
    iapply HΦ
    simp only [ite_true]
    iexists o
    rw [snapshot_Range_take_succ _ _ _ Hv]
    iframe
  icases Hpost with (⟨⟩ | ⟨%sl, Hout, Hsl, Hcap⟩)
  rw [List.take_length]
  wp_auto
  iapply HΦ
  iframe Hs He Hsl Hcap
  unfold kvsAt; imodintro; iintro %e %He
  iapply Hkvs; ipureintro; exact Hsub e He

end proof

end EtcdGrove
end Perennial
