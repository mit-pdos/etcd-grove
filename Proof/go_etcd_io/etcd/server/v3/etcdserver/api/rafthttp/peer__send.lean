/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/peer__send.lean`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.peer__send
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.peer__pick
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.isMsgSnap
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.peerStatus__isActive
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetTo
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetFrom
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetType
public import Spec.go_etcd_io.raft.v3.raftpb.MessageType__String
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String_ptr
public import Spec.github_com.prometheus.client_golang.prometheus.CounterVec__WithLabelValues
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Bool
public import Proof.github_com.mit_pdos.etcd_grove.FirstCallee

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

set_option hygiene false in
/-- The drop: `ReportUnreachable`, not a snapshot, the log, `sentFailures` counted. -/
local macro "send_drop" : tactic => `(tactic| (
  haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
  haveI : go.NotInterface go.uint64 := ⟨by unfold go.uint64; trivial⟩
  (try wp_auto)
  wp_apply hGetTo.1 ml _ _ _ st $$ [] as -
  · iframe #
  wp_apply HRU
  (try wp_auto)
  wp_apply hIsSnap ml st $$ []
  · iframe #
  rw [_root_.decide_eq_false Hst.2.2.1]
  (try wp_auto)
  repeat' (first_callee
    | "GetType" => (wp_apply hGetType.1 ml _ _ _ st $$ [] as -; iframe #)
    | "GetFrom" => (wp_apply hGetFrom.1 ml _ _ _ st $$ [] as -; iframe #)
    | "String" => (ihave #HT := hTypeString st.msg.Type'
                   iunfold fmt.stringMethodSpec at HT
                   wp_apply HT as %_)
    | "String" => (wp_apply hIDString as %_ -)
    | "String" => (wp_apply hIDStringPtr _ DFrac.discard _ $$ [] as %_ -; iframe #)
    | "isActive" => (wp_apply hIsActive ps $$ [] as %_ -; iframe #)
    | "zap.String" => (wp_apply hZString as %_ -)
    | "zap.Bool" => (wp_apply hZBool as %_ -)
    | (wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field); isplitr; (ipureintro; rfl);
       iintro %_ ⟨-, -⟩)
    | "Warn" => (wp_apply hWarn lg _ _ $$ []; (iframe #; ipureintro; exact Hlgnn))
    | (wp_if_destruct; (try (exfalso; exact Hlgnn rfl)))
    | wp_auto)
  wp_apply hGetTo.1 ml _ _ _ st $$ [] as -
  · iframe #
  wp_apply hIDString as %ids %Hids
  wp_apply wp_slice_literal (V := GoString) [ids]
  isplitr
  · ipureintro; rfl
  iintro %lsl2 ⟨Hlsl2, -⟩
  (try wp_auto)
  wp_apply hWLV vSF _ [go!"To"] [ids] _ $$ [Hlsl2] as %c2 ⟨%ci2, %Hci2, #Hcnt2, -⟩
  · iframe; iframe #
    ipureintro
    refine ⟨HSFl, by simp, fun v hv => ?_⟩
    simp only [List.mem_singleton] at hv
    subst hv; exact utf8Valid_of_ascii _ (Hids ▸ types.idStr_ascii _)
  subst Hci2
  iunfold prometheus.counterSpec at Hcnt2
  icases Hcnt2 with ⟨#HInc, -⟩
  wp_apply HInc
  (try wp_auto)
  iapply HΦ; itrivial))

set_option hygiene false in
/-- `select { case writec <- m: default: drop }` on the bag `Hb` of `V`-payloads, `Hpay` the
message's. -/
local macro "send_sel" : tactic => `(tactic| (
  wp_apply_core chan.wp_select_nonblocking
  isplit
  · iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.nonblockingClausePre]
      iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, wc, γ, ml
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      isplitr
      · iapply is_bag_is_chan $$ Hb
      unfold nonblockingSendAu
      isplit
      · iapply bag_nonblocking_send_au $$ Hlc1 Hb Hpay
        inext
        (try wp_auto)
        iapply HΦ; itrivial
      · itrivial
    · iapply BigAndL.bigAndL_nil.2; itrivial
  · send_drop))

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem rafthttp.peer.send.wp_proof
    (hPick : rafthttp.peer.pick.spec (GF := GF) (hG := hG))
    (hIsSnap : rafthttp.isMsgSnap.spec (GF := GF) (hG := hG))
    (hIsActive : rafthttp.peerStatus.isActive.spec (GF := GF) (hG := hG))
    (hTypeString : raftpb.MessageType.String.spec (GF := GF) (hG := hG))
    (hGetFrom : raftpb.Message.GetFrom.spec (GF := GF) (hG := hG))
    (hGetTo : raftpb.Message.GetTo.spec (GF := GF) (hG := hG))
    (hGetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG))
    (hIDString : types.ID.String.spec (GF := GF) (hG := hG))
    (hIDStringPtr : types.ID.String_ptr.spec (GF := GF) (hG := hG))
    (hWLV : prometheus.CounterVec.WithLabelValues.spec (GF := GF) (hG := hG))
    (hWarn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (hZString : zap.String.spec (GF := GF) (hG := hG))
    (hZBool : zap.Bool.spec (GF := GF) (hG := hG)) :
    rafthttp.peer.send.spec (GF := GF) (hG := hG) := by
  intro Rh lid pid γd R p ml
  wp_start as ⟨#Hp, Hpm⟩
  ihave #Hp' := Hp
  iunfold peerOk at Hp'
  icases Hp' with ⟨%lg, %ps, %pk, %cw2, %cw1, %pl, %ss, %cr2, %cr1, %r, %rc, %pc, #Hlg, %Hlgnn,
    #Hlid, #Hpid, #Hr, #Hraft, #Hps, #Hpsok, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    #Hmu⟩
  iunfold peerMsg at Hpm
  icases Hpm with ⟨%st, #Hm, #HP, HO, %Hst⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave Hri : (go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.rafthttpInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hri with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, ⟨%vSF, #HSF, %HSFl⟩, -⟩
  wp_auto
  wp_apply sync.Mutex.wp_Lock _ (peerLockInv p) $$ [] as ⟨Hlocked, Hinv⟩
  · iexact Hmu
  iunfold peerLockInv at Hinv
  icases Hinv with ⟨%b, Hb⟩
  (try wp_auto)
  wp_apply sync.Mutex.wp_Unlock $$ [Hlocked Hb]
  · iframe Hmu Hlocked
    inext; iunfold peerLockInv; iexists _; iframe
  (try wp_auto)
  cases b
  rotate_left
  · (try wp_auto); iapply HΦ; itrivial
  wp_auto_lc 1
  wp_apply hPick Rh lid pid γd R p ml st $$ [] as %wc %name Hwc
  · iframe #
  (try wp_auto)
  iunfold netRaftOk at Hraft
  icases Hraft with ⟨%ri, %Hri, -, -, #HRU, -⟩
  subst Hri
  icases Hwc with (⟨%γ, #Hb, %Hty⟩ | ⟨%γ, #Hb⟩ | ⟨%γ, #Hb⟩)
  · ihave Hpay := swMsg_v2_of_peerMsg Rh lid pid ml st Hst Hty $$ Hm HP HO
    send_sel
  · ihave Hpay : swMsg Rh .message lid pid ml $$ [HO]
    · iapply swMsg_message_of_peerMsg
      iunfold peerMsg; iexists st; iframe; iframe #; ipureintro; exact Hst
    send_sel
  · ihave Hpay : pipeMsg Rh pid ml $$ [HO]
    · iapply pipeMsg_of_peerMsg
      iunfold peerMsg; iexists st; iframe; iframe #; ipureintro; exact Hst
    send_sel

end proof

end EtcdGrove
end Perennial
