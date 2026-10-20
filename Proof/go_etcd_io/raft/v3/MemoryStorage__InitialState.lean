/- `MemoryStorage.InitialState` (`storage.go:121`), proved 2026-10-12 (Lean-first). -/
module

public import Spec.go_etcd_io.raft.v3.MemoryStorage__InitialState
public import Spec.go_etcd_io.raft.v3.raftpb.Snapshot__GetMetadata
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetConfState
public import Spec.go_etcd_io.raft.v3.raftpb.EnsureConfState
public import Proof.go_etcd_io.raft.v3.LemmasMemstorage
public import Proof.go_etcd_io.raft.v3.LemmasConfState

@[expose] public section

set_option linter.unusedSectionVars false

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

theorem MemoryStorage.InitialState.wp_proof
    (wp_GetMetadata : raftpb.Snapshot.GetMetadata.spec (GF := GF) (hG := hG))
    (wp_GetConfState : raftpb.SnapshotMetadata.GetConfState.spec (GF := GF) (hG := hG))
    (wp_EnsureConfState : raftpb.EnsureConfState.spec (GF := GF) (hG := hG)) :
    MemoryStorage.InitialState.spec (GF := GF) (hG := hG) := by
  have HN : ↑memSnapN ⊆ (⊤ : CoPset) := CoPset.subseteq_top
  intro ms γs σ σt hs
  wp_start as ⟨Hms, Hmeta, Htok⟩
  iunfold memStorMeta at Hmeta
  icases Hmeta with ⟨%n, %hp, Hmeta⟩
  iNamed Hmeta
  iunfold ownMemoryStorage at Hms
  icases Hms with ⟨#Hinit, #Hmu, Hview, Hsn, %Hbounded⟩
  iunfold memSnapShare at Hsn
  icases Hsn with ⟨#Hsinv, Hok⟩
  iunfold memSnapTok at Htok
  icases Htok with ⟨-, -, -, Hak, Hsvt, Hcbt⟩
  -- (D17d) the owner's and the application's keys lend the snapshot, without the lock
  imod memSnap_take ms γs 3 ⊤ HN $$ Hsinv [Hok Hak] with ⟨Hhome, Hrcpt⟩
  · iunfold memSnapKeys; iright; iright; iframe; ipureintro; rfl
  wp_auto
  iunfold memSnapHome at Hhome
  icases Hhome with ⟨%σp, Hsn, Hsnh, #Hcert1⟩
  icases ghostVar_agree γs.sn _ _ _ _ $$ Hsvt Hsnh with %Hag
  obtain ⟨Hs1, Hs2, Hs3⟩ := snapPart_inj Hag
  ihave Hsn := memSnapOwn_congr ms σp σt Hs1 Hs2 Hs3 $$ Hsn
  ihave #Hcertt := memSnapCertOk_congr γs σp σt Hs1 Hs2 Hs3 $$ Hcert1
  iunfold memSnapOwn at Hsn
  icases Hsn with ⟨%sp, %sv, Hsnapshot, Hsnap, %Hsnap_id⟩
  have Hcs : sv.Metadata'.ConfState' = storCS σt :=
    confState_eq_storCS _ σt Hsnap_id.2.1 Hsnap_id.2.2
  (try wp_auto)
  wp_apply wp_GetMetadata.1 sp (DFrac.own 1) sv $$ [Hsnap] as %pm ⟨Hm, Hmback⟩
  · iframe Hsnap
  wp_apply wp_GetConfState pm (DFrac.own 1) sv.Metadata' $$ [Hm] as %pc ⟨Hc, Hcback⟩
  · iframe Hm
  icases csOptA_nn _ _ _ $$ Hc with ⟨Hc, %Hnull⟩
  rcases Hnull with Hnull | Hnn
  · -- no conf state: `EnsureConfState` makes a fresh one, frozen; the storage is as it was
    obtain ⟨Hpc, Hc0⟩ := Hnull
    subst Hpc
    ihave Hm := Hcback $$ Hc
    ihave Hsnap := Hmback $$ Hm
    iapply wp_fupd
    wp_apply wp_EnsureConfState.2 as %r Hr
    imod csPts_persist _ _ _ _ $$ Hr with #Hr
    imod memSnap_put ms γs 3 σt ⊤ HN $$ Hsinv Hrcpt [Hsnapshot Hsnap] [Hsnh] Hcertt with Hk
    · iunfold memSnapOwn
      iexists sp, sv
      iframe
      ipureintro; exact Hsnap_id
    · rw [Hag]; iexact Hsnh
    iunfold memSnapKeys at Hk
    icases Hk with (⟨%Hk, -⟩ | ⟨%Hk, -⟩ | ⟨-, Hok, Hak⟩)
    · exact absurd Hk (by decide)
    · exact absurd Hk (by decide)
    imodintro
    iapply HΦ
    iframe Hhs
    isplitl [HhardState Hcs_initialState]
    · unfold memStorMeta
      iexists _, hp
      iframe # ∗
    rw [← Hcs, Hc0]
    iframe Hr
    unfold ownMemoryStorage memSnapShare memSnapTok
    simp only [named]
    iframe # ∗
    ipureintro; exact Hbounded
  · -- the storage's conf state: `EnsureConfState` sets its `AutoLeave` in place; then frozen,
    -- the storage's snapshot holding it read-only (`csOptA`'s third case)
    iapply wp_fupd
    wp_apply wp_EnsureConfState_freeze wp_EnsureConfState pc sv.Metadata'.ConfState' Hnn
      $$ [Hc] as #Hr
    · iexact Hc
    ihave Hm := Hcback $$ []
    · iunfold csOptA; iright; iright; iexact Hr
    ihave Hsnap := Hmback $$ Hm
    imod memSnap_put ms γs 3 σt ⊤ HN $$ Hsinv Hrcpt [Hsnapshot Hsnap] [Hsnh] Hcertt with Hk
    · iunfold memSnapOwn
      iexists sp, sv
      iframe
      ipureintro; exact Hsnap_id
    · rw [Hag]; iexact Hsnh
    iunfold memSnapKeys at Hk
    icases Hk with (⟨%Hk, -⟩ | ⟨%Hk, -⟩ | ⟨-, Hok, Hak⟩)
    · exact absurd Hk (by decide)
    · exact absurd Hk (by decide)
    imodintro
    iapply HΦ
    iframe Hhs
    isplitl [HhardState Hcs_initialState]
    · unfold memStorMeta
      iexists _, hp
      iframe # ∗
    rw [← Hcs]
    iframe Hr
    unfold ownMemoryStorage memSnapShare memSnapTok
    simp only [named]
    iframe # ∗
    ipureintro; exact Hbounded

end proof

end EtcdGrove
end Perennial
