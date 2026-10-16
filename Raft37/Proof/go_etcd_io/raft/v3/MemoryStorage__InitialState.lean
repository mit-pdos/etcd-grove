/- `MemoryStorage.InitialState` (`storage.go:121`), proved 2026-10-12 (Lean-first). -/
module

public import Raft37.Spec.go_etcd_io.raft.v3.MemoryStorage__InitialState
public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.Snapshot__GetMetadata
public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetConfState
public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.EnsureConfState
public import Raft37.Proof.go_etcd_io.raft.v3.LemmasMemstorage
public import Raft37.Proof.go_etcd_io.raft.v3.LemmasConfState

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
  intro ms γs σ hs
  wp_start as ⟨Hms, Hmeta⟩
  iunfold memStorMeta at Hmeta
  icases Hmeta with ⟨%n, %hp, Hmeta⟩
  iNamed Hmeta
  iunfold ownMemoryStorage at Hms
  icases Hms with ⟨#Hinit, #Hmu, Hview, Hsn, %Hbounded⟩
  iunfold memSnapOwn at Hsn
  icases Hsn with ⟨%sp, %sv, Hsnapshot, Hsnap, %Hsnap_id⟩
  have Hcs : sv.Metadata'.ConfState' = storCS σ :=
    confState_eq_storCS _ σ Hsnap_id.2.1 Hsnap_id.2.2
  wp_auto
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
    imodintro
    iapply HΦ
    iframe Hhs
    isplitl [HhardState Hcs_initialState]
    · unfold memStorMeta
      iexists _, hp
      iframe # ∗
    rw [← Hcs, Hc0]
    iframe Hr
    unfold ownMemoryStorage memSnapOwn
    iframe # ∗
    isplitl
    · iexists sp, sv
      iframe
      ipureintro; exact Hsnap_id
    ipureintro; exact Hbounded
  · -- the storage's conf state: `EnsureConfState` sets its `AutoLeave` in place; then frozen,
    -- the storage's snapshot holding it read-only (`csOptA`'s third case)
    wp_apply wp_EnsureConfState_freeze wp_EnsureConfState pc sv.Metadata'.ConfState' Hnn
      $$ [Hc] as #Hr
    · iexact Hc
    ihave Hm := Hcback $$ []
    · iunfold csOptA; iright; iright; iexact Hr
    ihave Hsnap := Hmback $$ Hm
    iapply HΦ
    iframe Hhs
    isplitl [HhardState Hcs_initialState]
    · unfold memStorMeta
      iexists _, hp
      iframe # ∗
    rw [← Hcs]
    iframe Hr
    unfold ownMemoryStorage memSnapOwn
    iframe # ∗
    isplitl
    · iexists sp, sv
      iframe
      ipureintro; exact Hsnap_id
    ipureintro; exact Hbounded

end proof

end EtcdGrove
end Perennial
