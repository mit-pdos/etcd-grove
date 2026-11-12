/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/peer__pick.lean`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.peer__pick
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.streamWriter__writec
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.isMsgApp
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.isMsgSnap

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
/-- `pick`'s last branches: the message writer's channel if working, else the pipeline's. -/
local macro "pick_rest" : tactic => `(tactic| (
  (try wp_auto)
  wp_apply hWritec Rh .message lid pid R cw1 $$ [] as %wc1 %ok1 ⟨%γ1, #Hb1⟩
  · iframe #
  (try wp_auto)
  cases ok1
  · (try wp_auto)
    iapply HΦ; iright; iright; iexists _; iexact Hbag
  · (try wp_auto)
    iapply HΦ; iright; ileft; iexists _; iexact Hb1))

set_option maxHeartbeats 2000000 in
theorem rafthttp.peer.pick.wp_proof
    (hWritec : rafthttp.streamWriter.writec.spec (GF := GF) (hG := hG))
    (hIsApp : rafthttp.isMsgApp.spec (GF := GF) (hG := hG))
    (hIsSnap : rafthttp.isMsgSnap.spec (GF := GF) (hG := hG)) :
    rafthttp.peer.pick.spec (GF := GF) (hG := hG) := by
  intro Rh lid pid γd R p ml st
  wp_start as ⟨#Hp, #Hm⟩
  iunfold peerOk at Hp
  icases Hp with ⟨%lg, %ps, %pk, %cw2, %cw1, %pl, %ss, %cr2, %cr1, %r, %rc, %pc, -, -, -, -, -, -,
    -, -, -, -, #Hw2, #Hf2, #Hw1, #Hf1, #Hpl, #Hph, -⟩
  ihave #Hph' := Hph
  iunfold pipeHandleOk at Hph'
  icases Hph' with ⟨-, %ps', %fs', %r', %id', %γd', %mc, %γm, -, -, -, -, -, #Hmc, #Hbag⟩
  simp only [rafthttp.pipelineMsg, rafthttp.streamMsg, rafthttp.streamAppV2]
  wp_auto
  wp_apply hIsSnap ml st $$ []
  · iframe #
  (try wp_auto)
  by_cases hs : st.msg.Type' = MsgSnap
  · rw [_root_.decide_eq_true hs]
    (try wp_auto)
    iapply HΦ; iright; iright; iexists _; iexact Hbag
  rw [_root_.decide_eq_false hs]
  (try wp_auto)
  wp_apply hWritec Rh .msgAppV2 lid pid R cw2 $$ [] as %wc2 %ok2 ⟨%γ2, #Hb2⟩
  · iframe #
  (try wp_auto)
  cases ok2
  · pick_rest
  · (try wp_auto)
    wp_apply hIsApp ml st $$ []
    · iframe #
    by_cases ha : st.msg.Type' = MsgApp
    · rw [_root_.decide_eq_true ha]
      (try wp_auto)
      iapply HΦ; ileft; iexists _; iframe #; ipureintro; exact ha
    · rw [_root_.decide_eq_false ha]
      pick_rest

end proof

end EtcdGrove
end Perennial
