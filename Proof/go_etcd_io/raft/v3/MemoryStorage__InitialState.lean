/- `MemoryStorage.InitialState` (`storage.go:121`; U8 v2 step 3): without the lock, the snapshot
read from the allocation's fuel (`memStorFresh`), the hard state and the counter from
`memStorMeta`. -/
module

public import Spec.go_etcd_io.raft.v3.MemoryStorage__InitialState
public import Spec.go_etcd_io.raft.v3.raftpb.Snapshot__GetMetadata
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetConfState
public import Spec.go_etcd_io.raft.v3.raftpb.EnsureConfState
public import Proof.go_etcd_io.raft.v3.LemmasConfState

@[expose] public section

set_option linter.unusedSectionVars false

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

theorem MemoryStorage.InitialState.wp_proof
    (wp_GetMetadata : raftpb.Snapshot.GetMetadata.spec (GF := GF) (hG := hG))
    (wp_GetConfState : raftpb.SnapshotMetadata.GetConfState.spec (GF := GF) (hG := hG))
    (wp_EnsureConfState : raftpb.EnsureConfState.spec (GF := GF) (hG := hG)) :
    MemoryStorage.InitialState.spec (GF := GF) (hG := hG) := by
  intro ms γs hs
  wp_start as ⟨Hmeta, Hfresh⟩
  iunfold memStorMeta at Hmeta
  icases Hmeta with ⟨%n, %hp, Hmeta⟩
  iNamed Hmeta
  iunfold memStorFresh at Hfresh
  icases Hfresh with ⟨Hjc, Hhk, %sp, Hsnapshot, Hsnap, Hsx⟩
  wp_auto
  wp_apply wp_GetMetadata.1 sp (DFrac.own 1) memSnapEmpty $$ [Hsnap] as %pm ⟨Hm, Hmback⟩
  · iframe Hsnap
  wp_apply wp_GetConfState pm (DFrac.own 1) memSnapEmpty.Metadata' $$ [Hm] as %pc ⟨Hc, Hcback⟩
  · simp only [memSnapEmpty]; iframe Hm
  icases csOptA_nn _ _ _ $$ Hc with ⟨Hc, %Hnull⟩
  rcases Hnull with Hnull | Hnn
  · -- no conf state: `EnsureConfState` makes a fresh one, frozen
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
    isplitl [Hjc Hhk Hsnapshot Hsnap Hsx]
    · iunfold memStorFresh
      iframe Hjc Hhk
      iexists sp
      iframe
    rw [Hc0]
    simp only [memSnapEmpty]
    iframe Hr
  · -- the storage's conf state: its `AutoLeave` set in place, then frozen
    iapply wp_fupd
    wp_apply wp_EnsureConfState_freeze wp_EnsureConfState pc memSnapEmpty.Metadata'.ConfState' Hnn
      $$ [Hc] as #Hr
    · simp only [memSnapEmpty]; iexact Hc
    ihave Hm := Hcback $$ []
    · iunfold csOptA; iright; iright; iexact Hr
    ihave Hsnap := Hmback $$ Hm
    imodintro
    iapply HΦ
    simp only [memSnapEmpty] at *
    iframe Hhs Hr
    isplitl [HhardState Hcs_initialState]
    · unfold memStorMeta
      iexists _, hp
      iframe # ∗
    iunfold memStorFresh
    iframe Hjc Hhk
    iexists sp
    iframe

end proof

end EtcdGrove
end Perennial
