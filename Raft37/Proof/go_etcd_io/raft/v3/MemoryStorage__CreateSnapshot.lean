/- `MemoryStorage.CreateSnapshot` (`storage.go:230`), proved 2026-10-12 (Lean-first). -/
module

public import Raft37.Spec.go_etcd_io.raft.v3.MemoryStorage__CreateSnapshot
public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.EnsureSnapshot
public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.Snapshot__GetMetadata
public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetIndex
public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.Entry__GetIndex
public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.Entry__GetTerm
public import Spec.google_golang_org.protobuf.proto.CloneSnapshot
public import Spec.google_golang_org.protobuf.proto.CloneConfState
public import Raft37.Proof.go_etcd_io.raft.v3.LemmasMemstorage
public import Raft37.Spec.go_etcd_io.raft.v3.MemoryStorage__lastIndex

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
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
  intro ms γs σ i cs dq oc data bs eood Hidle Hpre
  wp_start as ⟨Hms, Hcs, Hdata, #Herr⟩
  iunfold ownMemoryStorage at Hms
  icases Hms with ⟨#Hinit, #Hmu, Hview, Hsn, %Hbounded⟩
  iunfold memSnapOwn at Hsn
  icases Hsn with ⟨%sp0, %sv0, Hsnapshot, Hsnap0, %Hsnap_id⟩
  icases ownSnapM_not_null $$ Hsnap0 with ⟨Hsnap0, %Hsp0nn⟩
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
  iunfold memstorageInv at Hinv
  icases Hinv with ⟨%σp, Hinv⟩
  iNamedSuffix Hinv "_inv"
  icases memView_agree γs σ σp $$ Hview Hgs_inv with ⟨%Hvw, Hview, Hgs_inv⟩
  have Hσp : σp = σ := Hvw.2.2.2 Hidle
  subst Hσp
  iunfold memstorageFields at Hfields_inv
  icases Hfields_inv with ⟨%hp, %es, %dummy, %nfi, %nli, %nen, %nte, %nsn, Hfields_inv⟩
  iNamed Hfields_inv
  have Hss : σp.ss.index' = sv0.Metadata'.Index' := by rw [← Hsnap_id.1]; rfl
  have Hcs0 : sv0.Metadata'.ConfState' = storCS σp :=
    confState_eq_storCS _ σp Hsnap_id.2.1 Hsnap_id.2.2
  wp_apply wp_GetMetadata.1 sp0 (DFrac.own 1) sv0 $$ [Hsnap0] as %pm0 ⟨Hm0, Hmback0⟩
  · iframe Hsnap0
  wp_apply wp_SMGetIndex pm0 (DFrac.own 1) sv0.Metadata' $$ [Hm0] as Hm0
  · iframe Hm0
  ihave Hsnap0 := Hmback0 $$ Hm0
  rw [← Hss]
  wp_if_destruct
  · -- `ErrSnapOutOfDate`: nothing changes
    wp_method_call
    wp_call
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hgs_inv HhardState Hents_f
      Hents Hents_cap Hcs_firstIndex Hcs_lastIndex Hcs_entries Hcs_term Hcs_snapshot]
    · inext
      unfold memstorageInv memstorageFields
      iexists σp
      iframe Hgs_inv
      isplitl
      · iexists hp, es, dummy, nfi, nli, nen, nte, nsn
        iframe # ∗
        ipureintro; exact Hdummy
      ipureintro; exact Hpb_inv
    iapply HΦ
    iframe Hcs
    ileft
    isplitr
    · ipureintro; exact ⟨Hif, rfl, rfl⟩
    iframe Hdata
    unfold ownMemoryStorage memSnapOwn
    iframe # ∗
    isplitl
    · iexists sp0, sv0
      iframe
      ipureintro; exact Hsnap_id
    ipureintro; exact Hbounded
  have Hnew : uint.Z σp.ss.index' < uint.Z i := by omega
  obtain ⟨Hlo, Hhi⟩ := Hpre Hnew
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
  wp_apply wp_EnsureSnapshot sp0 (some sv0) $$ [Hsnap0] as %r ⟨Hr, %Hrsp⟩
  · simp only [snapOpt]; iexact Hsnap0
  have Hr : r = sp0 := Hrsp Hsp0nn
  subst r
  simp only [Option.getD_some]
  iNamedSuffix Hr "_s"
  iNamedSuffix Hm_s "_m"
  wp_auto
  imod cellRO_alloc $$ «$r0» with #cIn
  -- the term of `i`: `ms.ents[i - offset]`
  rw [Hd0i]
  have Hk : sint.Z (i - σp.prev.index') = uint.Z i - uint.Z σp.prev.index' := by word
  have Hkl : (uint.Z i - uint.Z σp.prev.index').toNat < (dummy1 :: σp.ents).length := by
    simp only [List.length_cons]; omega
  obtain ⟨e, He⟩ : ∃ e, (dummy1 :: σp.ents)[(uint.Z i - uint.Z σp.prev.index').toNat]? = some e :=
    ⟨_, List.getElem?_eq_getElem Hkl⟩
  have Hterm : termAt σp.prev σp.ents i = some e.Term' := by
    unfold termAt
    by_cases Hi : uint.Z i = uint.Z σp.prev.index'
    · simp only [Hi, ↓reduceIte]
      rw [show (uint.Z i - uint.Z σp.prev.index').toNat = 0 by omega] at He
      simp only [List.getElem?_cons_zero, Option.some.injEq] at He
      subst He
      rw [Hd1t]
    · simp only [Hi, ↓reduceIte]
      rw [show (uint.Z i - uint.Z σp.prev.index').toNat =
        (uint.Z i - uint.Z σp.prev.index' - 1).toNat + 1 by omega] at He
      simp only [List.getElem?_cons_succ] at He
      rw [He]
      rfl
  icases entsRO_lookup es1 (dummy1 :: σp.ents) _ e (by rw [← Hk] at He; exact He) $$ Hents_1
    with ⟨%ls1, %lk, #Hls1, #Hek, %Hlk⟩
  rw [ite_eq_left ⟨by word, by word⟩]
  wp_apply wp_load_slice_index es1 (sint.Z (i - σp.prev.index')) ls1 DFrac.discard lk (by word) $$ [Hls1] with -
  · iframe Hls1; ipureintro; exact Hlk.1
  wp_apply wp_GetTerm.1 lk DFrac.discard e $$ [Hek] with -
  · iframe Hek
  imod cellRO_alloc $$ «$r0» with #cTn
  rcases oc with _ | c
  · -- `cs == nil`: the `ConfState` stays
    icases Hcs with %Hn
    subst Hn
    wp_auto
    ihave Hsm : smPts pm (DFrac.own 1) (SnapshotMetadataM.mk sv0.Metadata'.ConfState' i e.Term') $$ [HC_m Hc_m HI_m HT_m]
    · iunfold smPts
      iexists _, _, _, uf
      isplitr
      · ipureintro; exact Hnn_m
      iframe HC_m Hc_m HI_m HT_m cIn cTn Hpb_m
    ihave Hsnap : ownSnapM sp0 (DFrac.own 1) (memSnapCreated σp i e.Term' none bs) $$ [HD_s Hdata HM_s Hsm]
    · rw [show memSnapCreated σp i e.Term' none bs = SnapshotM.mk bs (SnapshotMetadataM.mk sv0.Metadata'.ConfState' i e.Term') by rw [Hcs0]; rfl]
      iunfold ownSnapM
      iexists data, pm, _
      isplitr
      · ipureintro; exact Hnn_s
      iframe HD_s Hdata HM_s Hpb_s
      iunfold smOpt
      iright; iexact Hsm
    wp_apply wp_CloneSnapshot.1 sp0 (DFrac.own 1) _ $$ [Hsnap] as %p' ⟨Hsnap, Hp'⟩
    · iframe Hsnap
    imod memView_set γs σp σp
      { σp with ss := entryID.mk e.Term' i,
                scs := (memSnapCreated σp i e.Term' none bs).Metadata'.ConfState'.lists,
                sal := (memSnapCreated σp i e.Term' none bs).Metadata'.ConfState'.AutoLeave' }
      Hidle Hidle $$ Hview Hgs_inv with ⟨-, Hview, Hgs_inv⟩
    wp_method_call
    wp_call
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hgs_inv HhardState_1
      Hents_f_1 Hents_1 Hents_cap_1 Hcs_firstIndex_1 Hcs_lastIndex_1 Hcs_entries_1 Hcs_term_1
      Hcs_snapshot_1]
    · inext
      unfold memstorageInv memstorageFields
      iexists _
      iframe Hgs_inv
      isplitl
      · iexists hp1, es1, dummy1, nfi1, nli1, nen1, nte1, nsn1
        iframe # ∗
        ipureintro; exact ⟨Hd1i, Hd1t⟩
      ipureintro; exact Hpb_inv
    iapply HΦ
    isplitr
    · ipureintro; rfl
    iright
    iexists e.Term'
    isplitr
    · ipureintro; exact ⟨Hnew, Hterm, rfl⟩
    iframe Hp'
    unfold ownMemoryStorage memSnapOwn
    iframe # ∗
    isplitl
    · iexists sp0, _
      iframe Hsnapshot Hsnap
      ipureintro; exact ⟨rfl, rfl, rfl⟩
    ipureintro; exact Hbounded
  · -- `cs != nil`: the stored `ConfState` is a clone of `*cs`
    icases csPts_not_null $$ Hcs with ⟨Hcs, %Hcsnn⟩
    wp_if_destruct
    all_goals try (exfalso; exact Hcsnn rfl)
    wp_apply wp_CloneConfState.1 cs dq c $$ [Hcs] as %pc' ⟨Hcs, Hpc'⟩
    · iframe Hcs
    iclear Hc_m
    ihave Hc_m : csOptA pc' (DFrac.own 1) c $$ [Hpc']
    · iunfold csOptA; iright; ileft; iexact Hpc'
    ihave Hsm : smPts pm (DFrac.own 1) (SnapshotMetadataM.mk c i e.Term') $$ [HC_m Hc_m HI_m HT_m]
    · iunfold smPts
      iexists _, _, _, uf
      isplitr
      · ipureintro; exact Hnn_m
      iframe HC_m Hc_m HI_m HT_m cIn cTn Hpb_m
    ihave Hsnap : ownSnapM sp0 (DFrac.own 1) (memSnapCreated σp i e.Term' (some c) bs) $$ [HD_s Hdata HM_s Hsm]
    · rw [show memSnapCreated σp i e.Term' (some c) bs = SnapshotM.mk bs (SnapshotMetadataM.mk c i e.Term') from rfl]
      iunfold ownSnapM
      iexists data, pm, _
      isplitr
      · ipureintro; exact Hnn_s
      iframe HD_s Hdata HM_s Hpb_s
      iunfold smOpt
      iright; iexact Hsm
    wp_apply wp_CloneSnapshot.1 sp0 (DFrac.own 1) _ $$ [Hsnap] as %p' ⟨Hsnap, Hp'⟩
    · iframe Hsnap
    imod memView_set γs σp σp
      { σp with ss := entryID.mk e.Term' i,
                scs := (memSnapCreated σp i e.Term' (some c) bs).Metadata'.ConfState'.lists,
                sal := (memSnapCreated σp i e.Term' (some c) bs).Metadata'.ConfState'.AutoLeave' }
      Hidle Hidle $$ Hview Hgs_inv with ⟨-, Hview, Hgs_inv⟩
    wp_method_call
    wp_call
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hgs_inv HhardState_1
      Hents_f_1 Hents_1 Hents_cap_1 Hcs_firstIndex_1 Hcs_lastIndex_1 Hcs_entries_1 Hcs_term_1
      Hcs_snapshot_1]
    · inext
      unfold memstorageInv memstorageFields
      iexists _
      iframe Hgs_inv
      isplitl
      · iexists hp1, es1, dummy1, nfi1, nli1, nen1, nte1, nsn1
        iframe # ∗
        ipureintro; exact ⟨Hd1i, Hd1t⟩
      ipureintro; exact Hpb_inv
    iapply HΦ
    isplitl [Hcs]
    · iexact Hcs
    iright
    iexists e.Term'
    isplitr
    · ipureintro; exact ⟨Hnew, Hterm, rfl⟩
    iframe Hp'
    unfold ownMemoryStorage memSnapOwn
    iframe # ∗
    isplitl
    · iexists sp0, _
      iframe Hsnapshot Hsnap
      ipureintro; exact ⟨rfl, rfl, rfl⟩
    ipureintro; exact Hbounded

end proof

end EtcdGrove
end Perennial
