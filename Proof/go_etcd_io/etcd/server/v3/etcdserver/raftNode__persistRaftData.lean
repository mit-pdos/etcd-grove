/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/raftNode__persistRaftData.lean`. Lean-first
(no Rocq counterpart; etcd-io/etcd#22223: the steps of `raftNode__start.lean`'s proof it took).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.raftNode__persistRaftData
public import Spec.go_etcd_io.raft.v3.IsEmptySnap
public import Spec.go_etcd_io.raft.v3.IsEmptyHardState
public import Spec.go_etcd_io.raft.v3.raftpb.HardState__GetCommit
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Fatal

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem raftNode.persistRaftData.wp_proof
    (wp_IsEmptySnap : IsEmptySnap.spec (GF := GF) (hG := hG))
    (wp_IsEmptyHardState : IsEmptyHardState.spec (GF := GF) (hG := hG))
    (wp_GetCommit : raftpb.HardState.GetCommit.spec (GF := GF) (hG := hG))
    (wp_Error : zap.Error.spec (GF := GF) (hG := hG))
    (wp_Fatal : zap.Logger.Fatal.spec (GF := GF) (hG := hG)) :
    raftNode.persistRaftData.spec (GF := GF) (hG := hG) := by
  have wp_IsEmptySnap := wp_IsEmptySnap_nil wp_IsEmptySnap
  have wp_IsEmptyHardState := wp_hardStateAt_IsEmptyHardState wp_IsEmptyHardState
  have wp_GetCommit := wp_hardStateAt_GetCommit wp_GetCommit
  intro E γ r hp hs sl esL es c
  wp_start as ⟨#Hr, #Hhs, #Hes, #Hesa, Happ⟩
  ihave #Hr' := Hr
  iunfold isRaftNode at Hr'
  iNamed Hr'
  iunfold isRNWal at Hsti
  icases Hsti with ⟨%si, %Hsieq, #HSave, #HClose⟩
  subst Hsieq
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Hrpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  ihave #Hpbpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  ihave Hsi : (srvInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  iunfold srvInit at Hsi
  icases Hsi with ⟨⟨-, -, ⟨%gpc, #Hgpc, #Hgpcs⟩, -, -⟩, -⟩
  iunfold gaugeSetSpec at Hgpcs
  wp_auto
  -- `if !raft.IsEmptySnap(raftSnap)`: the snapshot is nil
  wp_apply wp_IsEmptySnap $$ [$Hrpkg]
  -- `r.storage.Save(hardState, entries)`, `lg.Fatal` on an error
  wp_apply HSave $$ [$Hhs $Hes $Hesa] as %err -
  rcases err with ei | _
  · wp_auto
    wp_apply wp_Error $$ [$Hzap] as %f -
    wp_apply wp_slice_literal
    try (isplitr; (ipureintro; rfl))
    try iintro %_ ⟨_, -⟩
    try wp_auto
    wp_apply wp_Fatal lg $$ [$Hzap] as %v Hf
    · ipureintro; exact Hlgnn
    iexfalso
    iexact Hf
  wp_auto
  -- `if !raft.IsEmptyHardState(hardState) { proposalsCommitted.Set(..) }`
  wp_apply wp_IsEmptyHardState hp hs $$ [$Hrpkg $Hhs] as %ehs -
  wp_join at next with [r hardState]
  · cases ehs
    · wp_auto
      wp_apply wp_GetCommit hp hs $$ [$Hpbpkg $Hhs]
      wp_apply Hgpcs
      wp_join_done
    · wp_auto
      wp_join_done
  -- the snapshot is nil: no `Sync`, no `ApplySnapshot`, no `Release`
  wp_apply wp_IsEmptySnap $$ [$Hrpkg]
  -- `r.raftStorage.Append(entries)`: the right becomes the receipt
  ihave #HApp := Hmsi
  iunfold isRNMemStor at HApp
  ispecialize HApp $$ %sl %esL %es
  wp_apply HApp $$ [$Hes $Hesa $Happ] as Hrcpt
  (try wp_auto)
  iapply HΦ
  iexact Hrcpt

end proof

end EtcdGrove
end Perennial
