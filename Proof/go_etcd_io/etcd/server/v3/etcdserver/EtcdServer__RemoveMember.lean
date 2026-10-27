/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__RemoveMember.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__RemoveMember
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__checkMembershipOperationPermission
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChangeType__Enum

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.RemoveMember.wp_proof
    (hChk : EtcdServer.checkMembershipOperationPermission.spec (GF := GF) (hG := hG))
    (hEnum : raftpb.ConfChangeType.Enum.spec (GF := GF) (hG := hG)) :
    EtcdServer.RemoveMember.spec (GF := GF) (hG := hG) := by
  intro s E ctx cd id Pin Pm Qm Qin
  wp_start as ⟨#Hau, #Hnil, #Hctx, HRD, HPin, HPm, #Hmay, #Hconf⟩
  iunfold mayRemoveOk at Hmay
  iunfold configureRemoveOk at Hconf
  (try wp_auto)
  wp_apply (hChk s E ctx cd) $$ [$HRD] as %err ⟨HRD, #Hout⟩
  · iframe #
  iunfold adminOut at Hout
  icases Hout with ⟨#Herr, #Htok⟩
  (try wp_auto)
  rcases err with ei | _
  · (try wp_auto)
    iapply HΦ
    iframe HRD
    iright
    iframe HPin
    isplitr
    · ipureintro; intro h; cases h
    ileft
    iframe HPm
    iexact Herr
  · (try wp_auto)
    wp_apply Hmay $$ [$HPm] as %errm Hqm
    (try wp_auto)
    rcases errm with em | _
    · (try wp_auto)
      iapply HΦ
      iframe HRD
      iright
      iframe HPin
      isplitr
      · ipureintro; intro h; cases h
      iright
      iexact Hqm
    · (try wp_auto)
      ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
      · iPkgInit
      rw [show go_etcd_io.raft.v3.raftpb.ConfChangeRemoveNode =
        #((W32 1 : go_etcd_io.raft.v3.raftpb.ConfChangeType)) from rfl]
      haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
      wp_apply (hEnum (W32 1)) as %tp Htp
      (try wp_auto)
      ispecialize Htok $$ %rfl
      icases Htok with ⟨%ai, #Htk⟩
      ispecialize Hconf $$ %ai
      wp_apply Hconf $$ [$HPin $HRD $Hqm $cc $Htp $«$v1»] as %sl %err2 ⟨HRD, HQ⟩
      · iframe #; ipureintro; exact ⟨rfl, rfl⟩
      (try wp_auto)
      iapply HΦ
      iframe HRD
      ileft
      iexact HQ

end proof

end EtcdGrove
end Perennial
