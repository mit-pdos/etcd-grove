/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/remote__send.lean`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.remote__send
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
/-- The drop: the log (whether the peer is active or not), `sentFailures` counted. -/
local macro "send_drop" : tactic => `(tactic| (
  haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
  haveI : go.NotInterface go.uint64 := ⟨by unfold go.uint64; trivial⟩
  (try wp_auto)
  wp_apply hIsActive ps $$ [] as %_ -
  · iframe #
  (try wp_auto)
  repeat' (first
    | (wp_apply hGetType.1 ml _ _ _ st $$ [] as -; iframe #)
    | (wp_apply hGetFrom.1 ml _ _ _ st $$ [] as -; iframe #)
    | (ihave #HT := hTypeString st.msg.Type'
       iunfold fmt.stringMethodSpec at HT
       wp_apply HT as %_)
    | (wp_apply hIDString as %_ -)
    | (wp_apply hIDStringPtr _ DFrac.discard _ $$ [] as %_ -; iframe #)
    | (wp_apply hIsActive ps $$ [] as %_ -; iframe #)
    | (wp_apply hZString as %_ -)
    | (wp_apply hZBool as %_ -)
    | (wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field); isplitr; (ipureintro; rfl);
       iintro %_ ⟨-, -⟩)
    | (wp_apply hWarn lg _ _ $$ []; (iframe #; ipureintro; exact Hlgnn))
    | (wp_if_destruct; (try (exfalso; exact Hlgnn rfl)))
    | wp_auto)
  all_goals (
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
      iapply HΦ; itrivial)))

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
theorem rafthttp.remote.send.wp_proof
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
    rafthttp.remote.send.spec (GF := GF) (hG := hG) := by
  intro Rh lid pid R g ml
  wp_start as ⟨#Hg, Hpay⟩
  ihave #Hg' := Hg
  iunfold remoteOk at Hg'
  icases Hg' with ⟨%lg, %ps, %pl, #Hlg, %Hlgnn, #Hlid, #Hpid, #Hps, #Hpsok, #Hpl, #Hph⟩
  ihave #Hph' := Hph
  iunfold pipeHandleOk at Hph'
  icases Hph' with ⟨-, %ps', %fs', %r, %id', %γd', %wc, %γ, -, -, -, -, -, #Hmc, #Hb⟩
  iunfold pipeMsg at Hpay
  icases Hpay with ⟨%st, #Hm, #HP, HO, %Hst⟩
  ihave Hri : (go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.rafthttpInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hri with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, ⟨%vSF, #HSF, %HSFl⟩, -⟩
  ihave Hpay : pipeMsg Rh pid ml $$ [HO]
  · iunfold pipeMsg; iexists st; iframe; iframe #; ipureintro; exact Hst
  wp_auto_lc 1
  send_sel

end proof

end EtcdGrove
end Perennial
