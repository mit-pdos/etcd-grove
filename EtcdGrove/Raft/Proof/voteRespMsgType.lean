/-
Port of `election_proof/proof_voteRespMsgType.v`.
-/
import EtcdGrove.Raft.Spec.voteRespMsgType

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `voteRespMsgType` is a pure switch on the message type; it calls nothing. The
first `case` is a `decide` on the literal `5`; the second an `=` on the generated
constant `raftpb.MsgPreVote`, which is `#MsgPreVote` by `rfl`. -/
theorem voteRespMsgType.wp_proof : voteRespMsgType.spec (GF := GF) (hG := hG) := by
  intro t r Ht
  wp_start as _
  wp_auto
  rcases Ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [show MsgVote = W32 5 from rfl, decide_true]
    wp_auto
    rw [show raftpb.MsgVoteResp = #MsgVoteResp from rfl]
    iapply HΦ
    itrivial
  · simp only [show (MsgPreVote = W32 5) ↔ False by decide, decide_false]
    rw [show raftpb.MsgPreVote = #MsgPreVote from rfl]
    wp_auto
    rw [show raftpb.MsgPreVoteResp = #MsgPreVoteResp from rfl]
    iapply HΦ
    itrivial

end proof

end EtcdGrove
end Perennial
