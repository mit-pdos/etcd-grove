/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__AddMember.lean`. Lean-first (no Rocq
counterpart); auth-mediation M2 (2026-11-20).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__AddMember
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

theorem EtcdServer.AddMember.wp_proof
    (hChk : EtcdServer.checkMembershipOperationPermission.spec (GF := GF) (hG := hG))
    (hEnum : raftpb.ConfChangeType.Enum.spec (GF := GF) (hG := hG))
    (hMarshal : encoding.json.MarshalMember.spec (GF := GF) (hG := hG)) :
    EtcdServer.AddMember.spec (GF := GF) (hG := hG) := by
  intro s E ctx cd tok memb dp dc ps cs Pin Pm Qm Qin n
  wp_start as ⟨#Hau, #Hlb, #Hctx, #Hlib, #HtokC, HRD, HPin, HPm, Hsl, #Hmay, #Hconf⟩
  iunfold mayAddOk at Hmay
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
    iframe HRD Hsl
    iright
    iframe HPin
    isplitr
    · ipureintro; intro h; cases h
    ileft
    iframe HPm Herr
    iunfold adminOutC at HoutC
    icases HoutC with ⟨-, #Hw⟩
    iapply Hw; intro h; cases h
  · (try wp_auto)
    ihave #Hjs : isPkgInit (PROP := IProp GF) pkg_id.encoding.json $$ []
    · iPkgInit
    iunfold memberSlices at Hsl
    icases Hsl with ⟨Hps, Hcs⟩
    wp_apply (hMarshal memb dp dc ps cs) $$ [$Hps $Hcs] as %bsl ⟨Hps, Hcs, Hb⟩
    (try wp_auto)
    wp_apply Hmay $$ [HPm Hps Hcs] as %errm ⟨Hqm, Hsl⟩
    · iframe HPm; iunfold memberSlices; iframe Hps Hcs
    (try wp_auto)
    rcases errm with em | _
    · (try wp_auto)
      iapply HΦ
      iframe HRD Hsl
      iright
      iframe HPin
      isplitr
      · ipureintro; intro h; cases h
      iright
      iexact Hqm
    · (try wp_auto)
      ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
      · iPkgInit
      try rw [show go_etcd_io.raft.v3.raftpb.ConfChangeAddNode =
        #((W32 0 : go_etcd_io.raft.v3.raftpb.ConfChangeType)) from rfl]
      haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
      wp_apply (hEnum (W32 0)) as %tp Htp
      (try wp_auto)
      ispecialize Htok $$ %rfl
      icases Htok with ⟨%ai, #Htk⟩
      ispecialize Hconf $$ %ai
      cases hL : memb.RaftAttributes'.IsLearner'
      · simp only [addChangeType, Bool.false_eq_true, ↓reduceIte]
        (try wp_auto)
        wp_apply Hconf $$ [$HPin $HRD $Hqm $cc $Htp $«$v1» $Hb] as %sl %err2 ⟨HRD, HQ⟩
        · iframe #; ipureintro; exact ⟨rfl, rfl, rfl⟩
        (try wp_auto)
        iapply HΦ
        iframe HRD Hsl
        ileft
        iexact HQ
      · simp only [addChangeType, ↓reduceIte]
        (try wp_auto)
        wp_apply (hEnum (W32 3)) as %tp3 Htp3
        (try wp_auto)
        wp_apply Hconf $$ [$HPin $HRD $Hqm $cc $Htp3 $«$v1» $Hb] as %sl %err2 ⟨HRD, HQ⟩
        · iframe #; ipureintro; exact ⟨rfl, rfl, rfl⟩
        (try wp_auto)
        iapply HΦ
        iframe HRD Hsl
        ileft
        iexact HQ

end proof

end EtcdGrove
end Perennial
