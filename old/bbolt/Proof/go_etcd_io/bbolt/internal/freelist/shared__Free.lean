module
public import Spec.go_etcd_io.bbolt.internal.freelist.shared__Free
public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas
public import Spec.go_etcd_io.bbolt.internal.common.Page__Id
public import Spec.go_etcd_io.bbolt.internal.common.Page__Overflow
public import Spec.go_etcd_io.bbolt.internal.common.Verify

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.freelist

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

theorem shared.Free.wp_proof (hId : Page.Id.spec (GF := GF) (hG := hG))
    (hOv : Page.Overflow.spec (GF := GF) (hG := hG))
    (hVerify : Verify.spec (GF := GF) (hG := hG)) :
    shared.Free.spec (GF := GF) (hG := hG) := by
  intro s iface σ txid p pv dq Hcan
  wp_start as ⟨Hs, Hp⟩
  ihave #Hc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  unfold ownShared ownSharedC
  icases Hs with ⟨%sv, %c, Hs, %Hok⟩
  iNamed Hs
  obtain ⟨Hid2, Hidb, Hncached, Hatx, Hlen⟩ := Hcan
  ihave %Hdom := BigSepM2.bigSepM2_lookup_iff $$ Hpds
  wp_auto
  wp_apply (hId p pv dq) $$ [Hp] as Hp
  · iexact Hp
  rw [decide_eq_false (show ¬ uint.Z pv.id' ≤ uint.Z (W64 1) by word)]
  try wp_auto
  wp_apply wp_map_lookup1 $$ [Hpending] as Hpending
  · iexact Hpending
  try wp_auto
  wp_join iprop(∃ (tp : Loc), "txp" ∷ txp_ptr ↦ tp ∗
      "Hpending" ∷ sv.pending' ↦$ (<[txid := tp]> pp) ∗
      "Hpd" ∷ ownPending tp (σ.pendingOf txid) ∗
      "Hpds" ∷ ([∗map] _t ↦ p;pd ∈ GMap.delete txid pp;GMap.delete txid σ.pending, ownPending p pd) ∗
      "Hs" ∷ s ↦ sv ∗ "t" ∷ t_ptr ↦ s ∗ "txid" ∷ txid_ptr ↦ txid)
    with [txp Hpending Hpds Hs t txid] as ⟨%tp, txp, Hpending, Hpd, Hpds, Hs, t, txid⟩
  · -- no entry yet: a new one
    rcases hpt : pp !! txid with _ | p0
    rotate_left
    · rw [hpt] at Hif
      simp only [Option.getD_some] at Hif
      obtain ⟨pd0, hpd0⟩ := Option.isSome_iff_exists.1
        ((Hdom txid).1 (by simp only [show Std.get? pp txid = some p0 from hpt, Option.isSome_some]))
      icases BigSepM2.bigSepM2_lookup_acc (show Std.get? pp txid = some p0 from hpt) hpd0 $$ Hpds
        with ⟨Hpo, -⟩
      unfold ownPending
      icases Hpo with ⟨%tv, Hpp, -⟩
      ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hpp
      exact absurd Hif Hnn
    have hpd : σ.pending !! txid = none := by
      have := Hdom txid
      simp only [show Std.get? pp txid = pp !! txid from rfl, hpt, Option.isSome_none] at this
      cases h : σ.pending !! txid
      · rfl
      · simp [show Std.get? σ.pending txid = σ.pending !! txid from rfl, h] at this
    try wp_auto
    wp_apply wp_mapInsert $$ [Hpending] as Hpending
    · iexact Hpending
    wp_join_done
    iexists «$r0_ptr»
    iframe
    rw [delete_of_none hpt, delete_of_none hpd]
    iframe
    unfold ownPending
    iexists _
    simp only [FLState.pendingOf, hpd, Option.getD_none, named]
    iframe
    rw [show (zero_val txPending).ids' = slice.nil from rfl,
      show (zero_val txPending).alloctx' = slice.nil from rfl]
    isplitl []
    · iapply ownSlice_nil
    isplitl []
    · iapply ownSliceCap_nil
    isplitl []
    · iapply ownSlice_nil
    isplitl []
    · iapply ownSliceCap_nil
    ipureintro; rfl
  · rcases hpt : pp !! txid with _ | p0
    · rw [hpt] at Hif; exact absurd rfl Hif
    obtain ⟨pd0, hpd0⟩ := Option.isSome_iff_exists.1
      ((Hdom txid).1 (by simp only [show Std.get? pp txid = some p0 from hpt, Option.isSome_some]))
    icases (BigSepM2.bigSepM2_delete (show Std.get? pp txid = some p0 from hpt) hpd0).1 $$ Hpds
      with ⟨Hpo, Hpds⟩
    iexists p0
    rw [GMap.insert_id pp txid p0 hpt]
    simp only [Option.getD_some, named]
    iframe
    simp only [FLState.pendingOf, show σ.pending !! txid = some pd0 from hpd0, Option.getD_some]
    iframe
  wp_apply (hId p pv dq) $$ [Hp] as Hp
  · iexact Hp
  wp_apply wp_map_lookup2 $$ [Hallocs] as Hallocs
  · iexact Hallocs
  try wp_auto
  wp_apply (hVerify _ iprop(allocTxid_ptr ↦ (σ.allocs !! pv.id').getD (zero_val w64) ∗
      txid_ptr ↦ txid)) $$ [allocTxid txid]
  · isplit
    · wp_auto
      wp_if_destruct
      · first | exact absurd rfl Hatx | exact absurd ‹_› Hatx | exact absurd (Eq.symm ‹_›) Hatx
      try wp_auto
      iframe
    · iframe
  iintro ⟨allocTxid, txid⟩
  try wp_auto
  wp_join iprop(sv.allocs' ↦$ GMap.delete pv.id' σ.allocs ∗ s ↦ sv ∗ t_ptr ↦ s ∗ p ↦{dq} pv ∗
      p_ptr ↦ p)
    with [Hallocs Hs t Hp p] as ⟨Hallocs, Hs, t, Hp, p⟩
  · try wp_auto
    wp_apply (hId p pv dq) $$ [Hp] as Hp
    · iexact Hp
    wp_apply wp_mapDelete $$ [Hallocs] as Hallocs
    · iexact Hallocs
    wp_join_done
  · have h : σ.allocs !! pv.id' = none := by
      cases h : σ.allocs !! pv.id' <;> simp_all
    rw [delete_of_none h]
    iframe
  wp_apply (hId p pv dq) $$ [Hp] as Hp
  · iexact Hp
  iunfold named at Hpd
  iunfold ownPending at Hpd
  icases Hpd with ⟨%tv, Htp, Hids, Hids_cap, Hatx, Hatx_cap, %Hlrb⟩
  have Hn : uint.Z pv.id' + (uint.nat pv.overflow' + 1 : Nat) ≤ 2 ^ 64 := by omega
  ihave IH : iprop(∃ (m : Nat) (tv : txPending) (cm : GMap w64 Unit),
      "id" ∷ id_ptr ↦ (pv.id' + W64 (m : Int)) ∗ "Htp" ∷ tp ↦ tv ∗
      "Hids" ∷ tv.ids' ↦* ((σ.pendingOf txid).ids ++ runIds pv.id' m) ∗
      "Hids_cap" ∷ ownSliceCap w64 tv.ids' (DFrac.own 1) ∗
      "Hatx" ∷ tv.alloctx' ↦* ((σ.pendingOf txid).alloctx ++
        List.replicate m ((σ.allocs !! pv.id').getD 0)) ∗
      "Hatx_cap" ∷ ownSliceCap w64 tv.alloctx' (DFrac.own 1) ∗
      "Hcache" ∷ sv.cache' ↦$ cm ∗ "Hp" ∷ p ↦{dq} pv ∗
      "%Hm" ∷ ⌜m ≤ uint.nat pv.overflow' + 1 ∧
        tv.lastReleaseBegin' = (σ.pendingOf txid).lastReleaseBegin ∧
        ∀ x, (cm !! x).isSome ↔ (c !! x).isSome ∨ x ∈ runIds pv.id' m⌝)
      $$ [id Htp Hids Hids_cap Hatx Hatx_cap Hcache Hp]
  · iexists 0, tv, c
    simp only [runIds, List.range_zero, List.map_nil, List.append_nil, List.replicate_zero]
    rw [show pv.id' + W64 ((0 : Nat) : Int) = pv.id' by word]
    iframe
    ipureintro
    exact ⟨by omega, Hlrb, fun x => by simp⟩
  wp_for IH
  wp_apply (hId p pv dq) $$ [Hp] as Hp
  · iexact Hp
  try wp_auto
  wp_apply (hOv p pv dq) $$ [Hp] as Hp
  · iexact Hp
  try wp_auto
  have hiff : uint.Z (pv.id' + W64 (m : Int)) ≤ uint.Z (pv.id' + W64 (uint.Z pv.overflow')) ↔
      m < uint.nat pv.overflow' + 1 := by
    constructor <;> intro h <;> word
  wp_if_destruct
  · have hlt := hiff.1 (of_decide_eq_true (go.intoVal_inj Hif))
    try wp_auto
    wp_apply wp_map_lookup2 $$ [Hcache] as Hcache
    · iexact Hcache
    have hx : (cm !! (pv.id' + W64 (m : Int))).isSome = false := by
      cases h : (cm !! (pv.id' + W64 (m : Int))).isSome
      · rfl
      · exfalso
        rcases (Hm.2.2 _).1 h with h' | h'
        · apply Hncached _ ?_ ((Hok.1 _).1 h')
          rw [mem_runIds Hn]; constructor <;> word
        · have := ((mem_runIds (by omega)).1 h').2; word
    rw [hx]
    try wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply wp_slice_append $$ [Hids Hids_cap Hsl] as %ids2 ⟨Hids, Hids_cap, -⟩
    · iframe
    try wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    wp_apply wp_slice_append $$ [Hatx Hatx_cap Hsl2] as %atx2 ⟨Hatx, Hatx_cap, -⟩
    · iframe
    try wp_auto
    wp_apply wp_mapInsert $$ [Hcache] as Hcache
    · iexact Hcache
    try wp_auto
    wp_for_post
    iframe
    iexists (m + 1), ({ ids' := ids2, alloctx' := atx2, lastReleaseBegin' := tv.lastReleaseBegin' } : txPending),
      (<[pv.id' + W64 (m : Int) := ()]> cm)
    rw [runIds_succ, List.replicate_succ', ← List.append_assoc, ← List.append_assoc,
      show pv.id' + W64 ((m + 1 : Nat) : Int) = pv.id' + W64 (m : Int) + W64 1 by word]
    simp only [named]
    iframe
    ipureintro
    refine ⟨by omega, Hm.2.1, fun x => ?_⟩
    by_cases hx : pv.id' + W64 (m : Int) = x
    · subst hx; simp [GMap.lookup_insert]
    · rw [GMap.lookup_insert_ne _ _ hx, Hm.2.2 x]
      simp only [List.mem_append, List.mem_singleton]
      constructor
      · rintro (h | h); exact Or.inl h; exact Or.inr (Or.inl h)
      · rintro (h | h | h); exact Or.inl h; exact Or.inr h; exact absurd h.symm hx
  · try wp_auto
    have hmn : m = uint.nat pv.overflow' + 1 := by
      have := Hm.1
      have : ¬ m < uint.nat pv.overflow' + 1 := fun h => Hif (by rw [decide_eq_true (hiff.2 h)])
      omega
    subst hmn
    rw [decide_eq_false (fun h => by have := hiff.1 h; omega)]
    simp only [Bool.false_eq_true, ite_false]
    try wp_auto
    obtain ⟨Hcached', Hwf'⟩ := freePages_ok (txid := txid) Hok.2 ⟨Hid2, Hidb, Hncached, Hatx, Hlen⟩
    iapply HΦ
    iframe Hp
    iexists sv, cm
    isplitl
    · iexists (<[txid := tp]> pp)
      simp only [named, FLState.freePages]
      iframe
      isplitr
      · ipureintro; exact Hiface
      iapply (BigSepM2.bigSepM2_insert_delete).2
      iframe
      unfold ownPending
      iexists _
      isimp only [FLState.pendingOf] at Hids Hatx
      iframe
      ipureintro; simpa [FLState.pendingOf] using Hm.2.1
    · ipureintro
      refine ⟨fun x => ?_, Hwf'⟩
      rw [Hm.2.2 x, Hcached' x, Hok.1 x]

end proof

end bbolt
end EtcdGrove
end Perennial
