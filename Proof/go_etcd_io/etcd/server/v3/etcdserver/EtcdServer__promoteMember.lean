/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__promoteMember.lean`. Lean-first (no Rocq
counterpart); auth-mediation M2 (2026-11-20).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__promoteMember
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__checkMembershipOperationPermission
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChangeType__Enum
public import Spec.encoding.json.MarshalConfigChangeContext

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

theorem EtcdServer.promoteMember.wp_proof
    (hChk : EtcdServer.checkMembershipOperationPermission.spec (GF := GF) (hG := hG))
    (hEnum : raftpb.ConfChangeType.Enum.spec (GF := GF) (hG := hG))
    (hMarshal : encoding.json.MarshalConfigChangeContext.spec (GF := GF) (hG := hG)) :
    EtcdServer.promoteMember.spec (GF := GF) (hG := hG) := by
  intro s E ctx cd tok id Pin Pm Qm Qin n
  wp_start as ⟨#Hau, #Hlb, #Hctx, #Hlib, #HtokC, HRD, HPin, HPm, #Hmay, #Hconf⟩
  iunfold mayPromoteOk at Hmay
  iunfold configureCcOk at Hconf
  (try wp_auto)
  wp_apply (hChk s E ctx cd tok n) $$ [$HRD] as %err ⟨HRD, #HoutC, #Hvar⟩
  · iframe #
  ihave #Hout := adminOut_of_C _ _ _ _ _ $$ HoutC
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
    iframe HPm Herr Hvar
    iunfold adminOutC at HoutC
    icases HoutC with ⟨-, #Hw⟩
    iapply Hw; intro h; cases h
  · (try wp_auto)
    ispecialize Htok $$ %rfl
    icases Htok with ⟨%ai, #Htk⟩
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
      iframe Hqm
      iexists ai
      iexact Htk
    · (try wp_auto)
      ihave #Hjs : isPkgInit (PROP := IProp GF) pkg_id.encoding.json $$ []
      · iPkgInit
      ihave Hn1 := ownSlice_nil (V := GoString) (GF := GF) (DFrac.own 1)
      ihave Hn2 := ownSlice_nil (V := GoString) (GF := GF) (DFrac.own 1)
      wp_apply (hMarshal _ (DFrac.own 1) (DFrac.own 1) [] []) $$ [Hn1 Hn2] as %bsl ⟨-, -, Hb⟩
      · iframe #
      (try wp_auto)
      ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
      · iPkgInit
      try rw [show go_etcd_io.raft.v3.raftpb.ConfChangeAddNode =
        #((W32 0 : go_etcd_io.raft.v3.raftpb.ConfChangeType)) from rfl]
      haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
      wp_apply (hEnum (W32 0)) as %tp Htp
      (try wp_auto)
      ispecialize Hconf $$ %ai
      wp_apply Hconf $$ [$HPin $HRD $Hqm $cc $Htp $«$v1» $Hb] as %sl %err2 ⟨HRD, HQ⟩
      · iframe #; ipureintro; exact ⟨rfl, rfl, rfl⟩
      (try wp_auto)
      iapply HΦ
      iframe HRD
      ileft
      iexact HQ

end proof

end EtcdGrove
end Perennial
