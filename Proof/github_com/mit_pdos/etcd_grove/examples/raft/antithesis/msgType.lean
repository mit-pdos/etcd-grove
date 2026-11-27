/-
Lean-first (no Rocq counterpart). #33 S4: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/msgType.lean`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.msgType

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]

theorem msgType.wp_proof : msgType.spec (GF := GF) (hG := hG) := by
  intro t
  wp_start
  wp_auto
  wp_if_destruct
  · rw [show msgTypeStr (W32 3) = go!"app" by decide]
    iapply HΦ
    ipureintro; trivial
  wp_if_destruct
  · rw [show msgTypeStr (W32 4) = go!"appresp" by decide]
    iapply HΦ
    ipureintro; trivial
  wp_if_destruct
  · rw [show msgTypeStr (W32 5) = go!"vote" by decide]
    iapply HΦ
    ipureintro; trivial
  wp_if_destruct
  · rw [show msgTypeStr (W32 6) = go!"voteresp" by decide]
    iapply HΦ
    ipureintro; trivial
  wp_if_destruct
  · rw [show msgTypeStr (W32 8) = go!"hb" by decide]
    iapply HΦ
    ipureintro; trivial
  wp_if_destruct
  · rw [show msgTypeStr (W32 9) = go!"hbresp" by decide]
    iapply HΦ
    ipureintro; trivial
  wp_if_destruct
  · rw [show msgTypeStr (W32 17) = go!"prevote" by decide]
    iapply HΦ
    ipureintro; trivial
  wp_if_destruct
  · rw [show msgTypeStr (W32 18) = go!"prevoteresp" by decide]
    iapply HΦ
    ipureintro; trivial
  wp_if_destruct
  · rw [show msgTypeStr (W32 7) = go!"snap" by decide]
    iapply HΦ
    ipureintro; trivial
  wp_if_destruct
  · rw [show msgTypeStr (W32 14) = go!"timeoutnow" by decide]
    iapply HΦ
    ipureintro; trivial
  wp_if_destruct
  · rw [show msgTypeStr (W32 15) = go!"readindex" by decide]
    iapply HΦ
    ipureintro; trivial
  wp_if_destruct
  · rw [show msgTypeStr (W32 16) = go!"readindexresp" by decide]
    iapply HΦ
    ipureintro; trivial
  wp_if_destruct
  · rw [show msgTypeStr (W32 2) = go!"prop" by decide]
    iapply HΦ
    ipureintro; trivial
  wp_if_destruct
  · rw [show msgTypeStr (W32 13) = go!"transfer" by decide]
    iapply HΦ
    ipureintro; trivial
  rw [show msgTypeStr t = go!"other" by
    simp only [msgTypeStr, MsgApp, MsgAppResp, MsgVote, MsgVoteResp, MsgHeartbeat, MsgHeartbeatResp,
      MsgPreVote, MsgPreVoteResp, MsgSnap, MsgTimeoutNow, MsgReadIndex, MsgReadIndexResp, MsgProp,
      MsgTransferLeader]; simp_all]
  iapply HΦ
  ipureintro; trivial

end proof

end AntHarness
end EtcdGrove
end Perennial
