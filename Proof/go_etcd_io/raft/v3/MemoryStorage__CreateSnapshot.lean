/- `MemoryStorage.CreateSnapshot` (`storage.go:230`), proved 2026-10-12 (Lean-first). -/
module

public import Spec.go_etcd_io.raft.v3.MemoryStorage__CreateSnapshot
public import Spec.go_etcd_io.raft.v3.MemoryStorage__lastIndex

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
    (wp_MemoryStorage_lastIndex : MemoryStorage.lastIndex.spec (GF := GF) (hG := hG)) :
    MemoryStorage.CreateSnapshot.spec (GF := GF) (hG := hG) := by
  intro ms γs σ hs snap i cs dq c data eood Hidle Hpre
  wp_start as ⟨Hms, Hmeta, Hcs, #Herr⟩
  iunfold ownMemoryStorage at Hms
  icases Hms with ⟨#Hinit, #Hmu, Hview, %Hbounded⟩
  iunfold memStorMeta at Hmeta
  icases Hmeta with ⟨%n, %voters0, Hmeta⟩
  iNamedSuffix Hmeta "_m"
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
  icases Hfields_inv with ⟨%hs0, %snap0, %es, %dummy, %nfi, %nli, %nen, %nte, %nsn, %voters1,
    Hfields_inv⟩
  iNamed Hfields_inv
  -- the two halves of `snapshot` make the whole field
  icombine Hsnapshot_m Hsnapshot gives %Heq
  subst Heq
  ihave Hsnap := (ptsto_halves _ _).2 $$ [Hsnapshot_m Hsnapshot]
  · iframe Hsnapshot_m Hsnapshot
  have Hss : σp.ss.index' = snap.Metadata'.Index' := by rw [← Hsnap_id]; rfl
  wp_auto
  wp_if_destruct
  · -- `ErrSnapOutOfDate`: nothing changes
    icases (ptsto_halves _ _).1 $$ Hsnap with ⟨Hsnapshot_m, Hsnapshot⟩
    wp_method_call
    wp_call
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hgs_inv HhardState Hsnapshot Hvoters Hents_f
      Hents Hents_cap Hcs_firstIndex Hcs_lastIndex Hcs_entries Hcs_term Hcs_snapshot]
    · inext
      unfold memstorageInv memstorageFields
      iexists σp
      iframe Hgs_inv
      isplitl
      · iexists hs0, snap, es, dummy, nfi, nli, nen, nte, nsn, voters1
        iframe # ∗
        ipureintro; exact ⟨Hsnap_id, Hdummy⟩
      ipureintro; exact Hpb_inv
    iapply HΦ
    isplitl [Hcs]
    · icases Hcs with (%Hn | ⟨Hc, -⟩)
      · ileft; ipureintro; exact Hn
      · iright; iexact Hc
    ileft
    isplitr
    · ipureintro; rw [Hss]; exact ⟨Hif, rfl, rfl⟩
    isplitl [Hview]
    · unfold ownMemoryStorage
      iframe # ∗
      ipureintro; exact Hbounded
    unfold memStorMeta
    iexists n, voters0
    iframe # ∗
  have Hnew : uint.Z σp.ss.index' < uint.Z i := by rw [Hss]; omega
  obtain ⟨Hlo, Hhi⟩ := Hpre Hnew
  obtain ⟨Hd0i, Hd0t⟩ := Hdummy
  icases Hents with #Hents
  ihave %Hlen := ownSlice_len $$ Hents
  simp only [List.length_cons] at Hlen
  icases ownSlice_elem_acc (sint.Z (W64 0)) dummy es DFrac.discard (dummy :: σp.ents) (by word) rfl
    $$ Hents with ⟨#Hd0, -⟩
  iStructNamedSuffix Hd0 "_d"
  have Hes0 : (0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z es.len) = True :=
    eq_true ⟨by word, by word⟩
  simp only [Hes0, ↓reduceIte]
  wp_auto
  icases (ptsto_halves _ _).1 $$ Hsnap with ⟨Hsnapshot_m, Hsnapshot⟩
  ihave Hf : memstorageFields ms σp $$ [HhardState Hsnapshot Hvoters Hents_f Hents_cap
      Hcs_firstIndex Hcs_lastIndex Hcs_entries Hcs_term Hcs_snapshot]
  · unfold memstorageFields
    iexists hs0, snap, es, dummy, nfi, nli, nen, nte, nsn, voters1
    iframe # ∗
    ipureintro; exact ⟨Hsnap_id, Hd0i, Hd0t⟩
  wp_apply wp_MemoryStorage_lastIndex ms σp Hpb_inv $$ [$Hf] as %li ⟨%Hli, Hf⟩
  wp_if_destruct
  · exfalso; word
  iunfold memstorageFields at Hf
  icases Hf with ⟨%hs1, %snap1, %es1, %dummy1, %nfi1, %nli1, %nen1, %nte1, %nsn1, %voters2, Hf⟩
  iNamedSuffix Hf "_1"
  icombine Hsnapshot_m Hsnapshot_1 gives %Heq1
  subst Heq1
  ihave Hsnap := (ptsto_halves _ _).2 $$ [Hsnapshot_m Hsnapshot_1]
  · iframe Hsnapshot_m Hsnapshot_1
  obtain ⟨Hd1i, Hd1t⟩ := Hdummy_1
  icases Hents_1 with #Hents_1
  ihave %Hlen1 := ownSlice_len $$ Hents_1
  simp only [List.length_cons] at Hlen1
  -- the term of `i`: `ms.ents[i - offset]`
  rw [Hd0i]
  have Hk : sint.Z (i - σp.prev.index') = uint.Z i - uint.Z σp.prev.index' := by word
  have Hkb : (0 ≤ sint.Z (i - σp.prev.index') ∧ sint.Z (i - σp.prev.index') < sint.Z es1.len) =
      True := eq_true ⟨by word, by word⟩
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
  icases ownSlice_elem_acc (sint.Z (i - σp.prev.index')) e es1 DFrac.discard _ (by word)
    (by rw [Hk]; exact He) $$ Hents_1 with ⟨#Hek, -⟩
  iStructNamedSuffix Hek "_e"
  wp_auto
  simp only [Hkb, ↓reduceIte]
  wp_auto
  wp_if_destruct
  · -- `cs == nil`: the `ConfState` stays
    icases (ptsto_halves _ _).1 $$ Hsnap with ⟨Hsnapshot_m, Hsnapshot⟩
    imod memView_set γs σp σp
      { prev := σp.prev, ents := σp.ents, pend := σp.pend,
        ss := snapId (raftpb.Snapshot.mk data
          (raftpb.SnapshotMetadata.mk snap.Metadata'.ConfState' i e.Term')) }
      Hidle Hidle $$ Hview Hgs_inv with ⟨-, Hview, Hgs_inv⟩
    wp_method_call
    wp_call
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hgs_inv HhardState_1 Hsnapshot Hvoters_1
      Hents_f_1 Hents_1 Hents_cap_1 Hcs_firstIndex_1 Hcs_lastIndex_1 Hcs_entries_1 Hcs_term_1
      Hcs_snapshot_1]
    · inext
      unfold memstorageInv memstorageFields
      iexists _
      iframe Hgs_inv
      isplitl
      · iexists hs1, _, es1, dummy1, nfi1, nli1, nen1, nte1, nsn1, voters2
        iframe # ∗
        ipureintro; exact ⟨rfl, Hd1i, Hd1t⟩
      ipureintro; exact Hpb_inv
    iapply HΦ
    isplitl [Hcs]
    · icases Hcs with (%Hn | ⟨Hc, -⟩)
      · ileft; ipureintro; exact Hn
      · iright; iexact Hc
    iright
    iexists e.Term'
    isplitr
    · ipureintro; exact ⟨Hnew, Hterm, by simp [memSnapCreated], rfl⟩
    isplitl [Hview]
    · unfold ownMemoryStorage
      iframe # ∗
      ipureintro; exact Hbounded
    unfold memStorMeta
    iexists n, voters0
    simp only
    iframe # ∗
  -- `cs != nil`: the `ConfState` is `*cs`
  icases Hcs with (%Hn | ⟨Hc, %vc, #Hcv⟩)
  · exact absurd Hn Hif
  wp_auto
  icases (ptsto_halves _ _).1 $$ Hsnap with ⟨Hsnapshot_m, Hsnapshot⟩
  imod memView_set γs σp σp
    { prev := σp.prev, ents := σp.ents, pend := σp.pend,
      ss := snapId (raftpb.Snapshot.mk data (raftpb.SnapshotMetadata.mk c i e.Term')) }
    Hidle Hidle $$ Hview Hgs_inv with ⟨-, Hview, Hgs_inv⟩
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hgs_inv HhardState_1 Hsnapshot
    Hents_f_1 Hents_1 Hents_cap_1 Hcs_firstIndex_1 Hcs_lastIndex_1 Hcs_entries_1 Hcs_term_1
    Hcs_snapshot_1]
  · inext
    unfold memstorageInv memstorageFields
    iexists _
    iframe Hgs_inv
    isplitl
    · ihave #Hcv' : (raftpb.Snapshot.mk data
          (raftpb.SnapshotMetadata.mk c i e.Term')).Metadata'.ConfState'.Voters' ↦*□ vc $$ []
      · iexact Hcv
      iexists hs1, raftpb.Snapshot.mk data (raftpb.SnapshotMetadata.mk c i e.Term'), es1, dummy1,
        nfi1, nli1, nen1, nte1, nsn1, vc
      iframe # ∗
      ipureintro; exact ⟨rfl, Hd1i, Hd1t⟩
    ipureintro; exact Hpb_inv
  iapply HΦ
  isplitl [Hc]
  · iright; iexact Hc
  iright
  iexists e.Term'
  isplitr
  · ipureintro; exact ⟨Hnew, Hterm, by simp [memSnapCreated, Hif], rfl⟩
  isplitl [Hview]
  · unfold ownMemoryStorage
    iframe # ∗
    ipureintro; exact Hbounded
  unfold memStorMeta
  iexists n, vc
  iframe # ∗

end proof

end EtcdGrove
end Perennial
