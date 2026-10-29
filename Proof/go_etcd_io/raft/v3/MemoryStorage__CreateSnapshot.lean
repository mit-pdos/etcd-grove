/- `MemoryStorage.CreateSnapshot` (`storage.go:244`), proved 2026-10-12 (Lean-first); U8 v2 step 3
(2026-10-29): over the lock's invariant and the stored snapshot's home (`InvMemstorage.lean`). The
caller's snapshot half agrees with the lock's quarter and the home's; the caller's frozen entry at
`i` puts `i` in the map, so below the end (no panic) and its term is the physical one. -/
module

public import Spec.go_etcd_io.raft.v3.MemoryStorage__CreateSnapshot
public import Spec.go_etcd_io.raft.v3.raftpb.EnsureSnapshot
public import Spec.go_etcd_io.raft.v3.raftpb.Snapshot__GetMetadata
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetIndex
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetIndex
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetTerm
public import Spec.google_golang_org.protobuf.proto.CloneSnapshot
public import Spec.google_golang_org.protobuf.proto.CloneConfState
public import Proof.go_etcd_io.raft.v3.LemmasMemstorage
public import Spec.go_etcd_io.raft.v3.MemoryStorage__lastIndex

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem MemoryStorage.CreateSnapshot.wp_proof
    (wp_GetMetadata : raftpb.Snapshot.GetMetadata.spec (GF := GF) (hG := hG))
    (wp_SMGetIndex : raftpb.SnapshotMetadata.GetIndex.spec (GF := GF) (hG := hG))
    (wp_GetIndex : raftpb.Entry.GetIndex.spec (GF := GF) (hG := hG))
    (wp_MemoryStorage_lastIndex : MemoryStorage.lastIndex.spec (GF := GF) (hG := hG))
    (wp_EnsureSnapshot : raftpb.EnsureSnapshot.spec (GF := GF) (hG := hG))
    (wp_GetTerm : raftpb.Entry.GetTerm.spec (GF := GF) (hG := hG))
    (wp_CloneConfState : proto.CloneConfState.spec (GF := GF) (hG := hG))
    (wp_CloneSnapshot : proto.CloneSnapshot.spec (GF := GF) (hG := hG)) :
    MemoryStorage.CreateSnapshot.spec (GF := GF) (hG := hG) := by
  have HN : ↑memStorN ⊆ (⊤ : CoPset) := CoPset.subseteq_top
  intro ms γs J i e cs dq oc data bs sv0 eood
  wp_start as ⟨#Hsi, #Hei, #HSV, #HDL, Hsx, Hcs, Hdata, #Herr⟩
  ihave #Hsi2 := Hsi
  iunfold memStorInvP at Hsi2
  icases Hsi2 with ⟨#Hlock, -, -⟩
  iunfold memStorLock at Hlock
  icases Hlock with ⟨#Hinit, #Hmu⟩
  iunfold memLog at Hei
  icases Hei with ⟨#Hei, -⟩
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_method_call
  wp_call
  wp_apply +noauto sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
  iunfold memstorageInv at Hinv
  icases Hinv with ⟨%p, %ents, %M, %sv, Hinv⟩
  iNamedSuffix Hinv "_inv"
  icases memSnapExact_agree γs sv0 sv $$ Hsx Hsx_inv with %Hsv
  subst Hsv
  -- the caller's frozen entry is the map's at `i`
  icases memLogL_auth γs.log 1 M (uint.nat i) DFrac.discard [e] $$ Hlog_inv Hei with %HMi
  have HMi0 : M.lookup (uint.nat i) = some e := by simpa using HMi 0 e rfl
  generalize Hσf : memPhys p ents = σp
  have Hσp : σp.prev = p ∧ σp.ents = ents := by subst Hσf; exact ⟨rfl, rfl⟩
  obtain ⟨Hp, Hents⟩ := Hσp
  subst Hp Hents
  obtain ⟨Hb, Hnone, Hmap, Hcsi, Hsie, Hpos⟩ := Hok_inv
  have Hpb_inv : uint.Z σp.prev.index' + (σp.ents.length : Int) < 2^61 := by word
  iunfold memstorageFields at Hfields_inv
  icases Hfields_inv with ⟨%hp, %es, %dummy, %nfi, %nli, %nen, %nte, %nsn, Hfields_inv⟩
  iNamed Hfields_inv
  -- the stored snapshot, taken out of its home with the lock's key
  imod memSnap_take ms γs J ⊤ HN $$ Hsi Hlk_inv with Hhome
  wp_auto
  iunfold memSnapHome at Hhome
  icases Hhome with ⟨Hhk, %sp0, %sv1, Hsnapshot, Hsnap0, Hsxh, Hval⟩
  icases ghostVar_agree γs.sx _ _ _ _ $$ Hsx_inv Hsxh with %Hsv1
  subst Hsv1
  icases ownSnapM_not_null $$ Hsnap0 with ⟨Hsnap0, %Hsp0nn⟩
  (try wp_auto)
  wp_apply wp_GetMetadata.1 sp0 (DFrac.own 1) sv0 $$ [Hsnap0] as %pm0 ⟨Hm0, Hmback0⟩
  · iframe Hsnap0
  wp_apply wp_SMGetIndex pm0 (DFrac.own 1) sv0.Metadata' $$ [Hm0] as Hm0
  · iframe Hm0
  ihave Hsnap0 := Hmback0 $$ Hm0
  wp_if_destruct
  · -- `ErrSnapOutOfDate`: the snapshot back home unchanged
    imod memSnap_put ms γs J ⊤ HN $$ Hsi [Hhk Hsnapshot Hsnap0 Hsxh Hval] with Hlk
    · iunfold memSnapHome
      iframe Hhk
      iexists sp0, sv0
      iframe
    wp_method_call
    wp_call
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked HhardState Hents_f Hents Hents_cap
      Hcs_firstIndex Hcs_lastIndex Hcs_entries Hcs_term Hcs_snapshot Hlog_inv Hen_inv Hcp_inv
      Hsx_inv Hlk]
    · unfold memstorageInv
      iexists σp.prev, σp.ents, M, sv0
      simp only [named]
      rw [Hσf]
      isplitl [HhardState Hents_f Hents Hents_cap Hcs_firstIndex Hcs_lastIndex Hcs_entries
        Hcs_term Hcs_snapshot]
      · unfold memstorageFields
        iexists hp, es, dummy, nfi, nli, nen, nte, nsn
        simp only [named]
        iframe # ∗
        ipureintro; exact Hdummy
      iframe # ∗
      ipureintro; exact ⟨Hb, Hnone, Hmap, Hcsi, Hsie, Hpos⟩
    iapply HΦ
    iframe Hcs
    iright
    iframe Hsx Hdata
    ipureintro
    exact ⟨rfl, rfl, by word⟩
  -- `i` is past the stored snapshot (so past the compaction point) and in the map (below the end)
  have Hci : uint.nat σp.prev.index' < uint.nat i := by word
  have Hie : uint.nat i < uint.nat σp.prev.index' + 1 + σp.ents.length := by
    refine Nat.lt_of_not_le fun h => ?_
    have := Hnone (uint.nat i) h
    rw [HMi0] at this
    cases this
  have HMe : σp.ents[uint.nat i - uint.nat σp.prev.index' - 1]? = some e := by
    rw [← Hmap _ Hci Hie, HMi0]
  have Hlo : uint.Z σp.prev.index' ≤ uint.Z i := by word
  have Hhi : uint.Z i ≤ uint.Z σp.prev.index' + (σp.ents.length : Int) := by word
  obtain ⟨Hd0i, Hd0t⟩ := Hdummy
  icases Hents with #Hents
  ihave %Hcl := entsRO_cons_len $$ Hents
  icases entsRO_lookup es (dummy :: σp.ents) 0 dummy rfl $$ Hents
    with ⟨%ls, %l0, #Hls, #He0, %Hl0⟩
  rw [ite_eq_left ⟨by word, by word⟩]
  wp_apply wp_load_slice_index es (sint.Z (W64 0)) ls DFrac.discard l0 (by word) $$ [Hls] with -
  · iframe Hls; ipureintro; exact Hl0.1
  wp_apply wp_GetIndex.1 l0 DFrac.discard dummy $$ [He0] with -
  · iframe He0
  ihave Hf : memstorageFields ms σp $$ [HhardState Hents_f Hents_cap
      Hcs_firstIndex Hcs_lastIndex Hcs_entries Hcs_term Hcs_snapshot]
  · unfold memstorageFields
    iexists hp, es, dummy, nfi, nli, nen, nte, nsn
    iframe # ∗
    ipureintro; exact ⟨Hd0i, Hd0t⟩
  wp_apply wp_MemoryStorage_lastIndex ms σp Hpb_inv $$ [$Hf] as %li ⟨%Hli, Hf⟩
  wp_if_destruct
  · exfalso; word
  iunfold memstorageFields at Hf
  icases Hf with ⟨%hp1, %es1, %dummy1, %nfi1, %nli1, %nen1, %nte1, %nsn1, Hf⟩
  iNamedSuffix Hf "_1"
  obtain ⟨Hd1i, Hd1t⟩ := Hdummy_1
  icases Hents_1 with #Hents_1
  clear Hcl Hl0
  ihave %Hcl := entsRO_cons_len $$ Hents_1
  -- the storage's snapshot, made whole in place
  wp_apply wp_EnsureSnapshot.1 sp0 (some sv0) $$ [Hsnap0] as %r ⟨Hr, %Hrsp⟩
  · simp only [snapOpt]; iexact Hsnap0
  ihave Hr := ownSnapS_W _ _ _ $$ Hr
  ihave Hr := ownSnapW_E $$ Hr
  have Hr : r = sp0 := Hrsp Hsp0nn
  subst r
  simp only [Option.getD_some]
  iNamedSuffix Hr "_s"
  iNamedSuffix Hm_s "_m"
  wp_auto
  imod cellRO_alloc $$ «$r0» with #cIn
  -- the term of `i`: `ms.ents[i - offset]`, the caller's entry
  rw [Hd0i]
  have Hk : sint.Z (i - σp.prev.index') = uint.Z i - uint.Z σp.prev.index' := by word
  have He : (dummy1 :: σp.ents)[(uint.Z i - uint.Z σp.prev.index').toNat]? = some e := by
    rw [show (uint.Z i - uint.Z σp.prev.index').toNat =
      (uint.nat i - uint.nat σp.prev.index' - 1) + 1 by word, List.getElem?_cons_succ]
    exact HMe
  icases entsRO_lookup es1 (dummy1 :: σp.ents) _ e (by rw [← Hk] at He; exact He) $$ Hents_1
    with ⟨%ls1, %lk, #Hls1, #Hek, %Hlk⟩
  rw [ite_eq_left ⟨by word, by word⟩]
  wp_apply wp_load_slice_index es1 (sint.Z (i - σp.prev.index')) ls1 DFrac.discard lk (by word) $$ [Hls1] with -
  · iframe Hls1; ipureintro; exact Hlk.1
  wp_apply wp_GetTerm.1 lk DFrac.discard e $$ [Hek] with -
  · iframe Hek
  imod cellRO_alloc $$ «$r0» with #cTn
  -- the frozen entry at the new snapshot's index (the lock's `Hsf`)
  ihave #Hei1 : (uint.nat i) ↪[γs.log]□ e $$ [Hei]
  · iunfold memLogL at Hei
    icases Hei with ⟨#H, -⟩
    iexact H
  have Hok' : MemOk σp.prev σp.ents M (memSnapCreated sv0 i e.Term' oc bs) :=
    ⟨Hb, Hnone, Hmap, by simp only [memSnapCreated]; omega, by simp only [memSnapCreated]; omega, Hpos⟩
  iunfold memSnapExact at Hsx
  imod memSnap_update γs sv0 sv0 sv0 (memSnapCreated sv0 i e.Term' oc bs) $$ Hsx Hsx_inv Hsxh
    with ⟨Hsx, Hsx_inv, Hsxh⟩
  rcases oc with _ | cc
  · -- `cs == nil`: the `ConfState` stays
    simp only [memCsArg]
    icases Hcs with %Hn
    subst Hn
    wp_auto
    ihave Hsm : smPts pm (DFrac.own 1) (SnapshotMetadataM.mk sv0.Metadata'.ConfState' i e.Term') $$ [HC_m Hc_m HI_m HT_m]
    · iunfold smPts
      iexists _, _, _, uf
      isplitr
      · ipureintro; exact Hnn_m
      iframe HC_m Hc_m HI_m HT_m cIn cTn Hpb_m
    ihave Hsnap : ownSnapM sp0 (DFrac.own 1) (memSnapCreated sv0 i e.Term' none bs) $$ [HD_s Hdata HM_s Hsm]
    · rw [show memSnapCreated sv0 i e.Term' none bs = SnapshotM.mk bs (SnapshotMetadataM.mk sv0.Metadata'.ConfState' i e.Term') from rfl]
      iunfold ownSnapM
      iexists data, pm, _
      isplitr
      · ipureintro; exact Hnn_s
      iframe HD_s Hdata HM_s Hpb_s
      iunfold smOpt
      iright; iexact Hsm
    wp_apply wp_CloneSnapshot.1 sp0 (DFrac.own 1) _ $$ [Hsnap] as %p' ⟨Hsnap, Hp'⟩
    · iframe Hsnap
    -- the new snapshot back home, with its validity and delivered bound
    imod memSnap_put ms γs J ⊤ HN $$ Hsi [Hhk Hsnapshot Hsnap Hsxh] with Hlk
    · iunfold memSnapHome
      iframe Hhk
      iexists sp0, _
      iframe Hsnapshot Hsnap Hsxh
      iright
      iframe HSV
      simp only [memSnapCreated]
      iexact HDL
    wp_method_call
    wp_call
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked HhardState_1
      Hents_f_1 Hents_1 Hents_cap_1 Hcs_firstIndex_1 Hcs_lastIndex_1 Hcs_entries_1 Hcs_term_1
      Hcs_snapshot_1 Hlog_inv Hen_inv Hcp_inv Hsx_inv Hlk]
    · unfold memstorageInv
      iexists σp.prev, σp.ents, M, memSnapCreated sv0 i e.Term' none bs
      simp only [named]
      rw [Hσf]
      isplitl [HhardState_1 Hents_f_1 Hents_1 Hents_cap_1 Hcs_firstIndex_1 Hcs_lastIndex_1
        Hcs_entries_1 Hcs_term_1 Hcs_snapshot_1]
      · unfold memstorageFields
        iexists hp1, es1, dummy1, nfi1, nli1, nen1, nte1, nsn1
        simp only [named]
        iframe # ∗
        ipureintro; exact ⟨Hd1i, Hd1t⟩
      iframe # ∗
      isplitr
      · iright
        iexists e
        simp only [memSnapCreated]
        iframe Hei1
      ipureintro; exact Hok'
    iapply HΦ
    isplitr
    · simp only [memCsArg]; ipureintro; trivial
    ileft
    iunfold memSnapExact
    iframe Hsx Hp'
    ipureintro; rfl
  · -- `cs != nil`: the stored `ConfState` is a clone of `*cs`
    simp only [memCsArg]
    icases csPts_not_null $$ Hcs with ⟨Hcs, %Hcsnn⟩
    wp_if_destruct
    all_goals try (exfalso; exact Hcsnn rfl)
    wp_apply wp_CloneConfState.1 cs dq cc $$ [Hcs] as %pc' ⟨Hcs, Hpc'⟩
    · iframe Hcs
    iclear Hc_m
    ihave Hc_m : csOptA pc' (DFrac.own 1) cc $$ [Hpc']
    · iunfold csOptA; iright; ileft; iexact Hpc'
    ihave Hsm : smPts pm (DFrac.own 1) (SnapshotMetadataM.mk cc i e.Term') $$ [HC_m Hc_m HI_m HT_m]
    · iunfold smPts
      iexists _, _, _, uf
      isplitr
      · ipureintro; exact Hnn_m
      iframe HC_m Hc_m HI_m HT_m cIn cTn Hpb_m
    ihave Hsnap : ownSnapM sp0 (DFrac.own 1) (memSnapCreated sv0 i e.Term' (some cc) bs) $$ [HD_s Hdata HM_s Hsm]
    · rw [show memSnapCreated sv0 i e.Term' (some cc) bs = SnapshotM.mk bs (SnapshotMetadataM.mk cc i e.Term') from rfl]
      iunfold ownSnapM
      iexists data, pm, _
      isplitr
      · ipureintro; exact Hnn_s
      iframe HD_s Hdata HM_s Hpb_s
      iunfold smOpt
      iright; iexact Hsm
    wp_apply wp_CloneSnapshot.1 sp0 (DFrac.own 1) _ $$ [Hsnap] as %p' ⟨Hsnap, Hp'⟩
    · iframe Hsnap
    -- the new snapshot back home, with its validity and delivered bound
    imod memSnap_put ms γs J ⊤ HN $$ Hsi [Hhk Hsnapshot Hsnap Hsxh] with Hlk
    · iunfold memSnapHome
      iframe Hhk
      iexists sp0, _
      iframe Hsnapshot Hsnap Hsxh
      iright
      iframe HSV
      simp only [memSnapCreated]
      iexact HDL
    wp_method_call
    wp_call
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked HhardState_1
      Hents_f_1 Hents_1 Hents_cap_1 Hcs_firstIndex_1 Hcs_lastIndex_1 Hcs_entries_1 Hcs_term_1
      Hcs_snapshot_1 Hlog_inv Hen_inv Hcp_inv Hsx_inv Hlk]
    · unfold memstorageInv
      iexists σp.prev, σp.ents, M, memSnapCreated sv0 i e.Term' (some cc) bs
      simp only [named]
      rw [Hσf]
      isplitl [HhardState_1 Hents_f_1 Hents_1 Hents_cap_1 Hcs_firstIndex_1 Hcs_lastIndex_1
        Hcs_entries_1 Hcs_term_1 Hcs_snapshot_1]
      · unfold memstorageFields
        iexists hp1, es1, dummy1, nfi1, nli1, nen1, nte1, nsn1
        simp only [named]
        iframe # ∗
        ipureintro; exact ⟨Hd1i, Hd1t⟩
      iframe # ∗
      isplitr
      · iright
        iexists e
        simp only [memSnapCreated]
        iframe Hei1
      ipureintro; exact Hok'
    iapply HΦ
    iframe Hcs
    ileft
    iunfold memSnapExact
    iframe Hsx Hp'
    ipureintro; rfl

end proof

end EtcdGrove
end Perennial
