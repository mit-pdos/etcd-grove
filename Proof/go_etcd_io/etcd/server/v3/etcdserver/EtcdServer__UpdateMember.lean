/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__UpdateMember.lean`. Lean-first (no Rocq
counterpart); auth-mediation M2 (2026-11-20).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__UpdateMember
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__checkMembershipOperationPermission
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChangeType__Enum
public import Spec.encoding.json.MarshalMember

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

theorem EtcdServer.UpdateMember.wp_proof
    (hChk : EtcdServer.checkMembershipOperationPermission.spec (GF := GF) (hG := hG))
    (hEnum : raftpb.ConfChangeType.Enum.spec (GF := GF) (hG := hG))
    (hMarshal : encoding.json.MarshalMember.spec (GF := GF) (hG := hG)) :
    EtcdServer.UpdateMember.spec (GF := GF) (hG := hG) := by
  intro s E ctx cd tok memb dp dc ps cs Pin Qin n
  wp_start as ⟨#Hau, #Hlb, #Hctx, #Hlib, #HtokC, HRD, HPin, Hsl, #Hconf⟩
  iunfold configureCcOk at Hconf
  (try wp_auto)
  ihave #Hjs : isPkgInit (PROP := IProp GF) pkg_id.encoding.json $$ []
  · iPkgInit
  iunfold memberSlices at Hsl
  icases Hsl with ⟨Hps, Hcs⟩
  wp_apply (hMarshal memb dp dc ps cs) $$ [$Hps $Hcs] as %bsl ⟨Hps, Hcs, Hb⟩
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
    isplitl [Hps Hcs]
    · iunfold memberSlices; iframe Hps Hcs
    iright
    iframe HPin Herr
    isplitr
    · ipureintro; intro h; cases h
    iunfold adminOutC at HoutC
    icases HoutC with ⟨-, #Hw⟩
    iapply Hw; intro h; cases h
  · (try wp_auto)
    ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
    · iPkgInit
    try rw [show go_etcd_io.raft.v3.raftpb.ConfChangeUpdateNode =
      #((W32 2 : go_etcd_io.raft.v3.raftpb.ConfChangeType)) from rfl]
    haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
    wp_apply (hEnum (W32 2)) as %tp Htp
    (try wp_auto)
    ispecialize Htok $$ %rfl
    icases Htok with ⟨%ai, #Htk⟩
    ispecialize Hconf $$ %ai
    wp_apply Hconf $$ [$HPin $HRD $cc $Htp $«$v1» $Hb] as %sl %err2 ⟨HRD, HQ⟩
    · iframe #; ipureintro; exact ⟨rfl, rfl, rfl⟩
    (try wp_auto)
    iapply HΦ
    iframe HRD
    isplitl [Hps Hcs]
    · iunfold memberSlices; iframe Hps Hcs
    ileft
    iexact HQ

end proof

end EtcdGrove
end Perennial
