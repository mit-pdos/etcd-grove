/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/register/deliverable.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.register.deliverable

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace register

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.register.Assumptions]

theorem deliverable.wp_proof : deliverable.spec (GF := GF) (hG := hG) := by
  intro m
  wp_start
  simp only [raftpb.MsgHeartbeatResp, raftpb.MsgHeartbeat, raftpb.MsgVoteResp, raftpb.MsgVote,
    raftpb.MsgAppResp, raftpb.MsgApp]
  have Hcases : (m.Type' ≠ W32 2 ∧ m.Type' ≠ W32 9 ∧ m.Type' ≠ W32 8 ∧ m.Type' ≠ W32 6 ∧
       m.Type' ≠ W32 5 ∧ m.Type' ≠ W32 4 ∧ m.Type' ≠ W32 3) ∨
      m.Type' = W32 2 ∨ m.Type' = W32 9 ∨ m.Type' = W32 8 ∨ m.Type' = W32 6 ∨
      m.Type' = W32 5 ∨ m.Type' = W32 4 ∨ m.Type' = W32 3 := by
    by_cases h2 : m.Type' = W32 2 <;> by_cases h9 : m.Type' = W32 9 <;>
    by_cases h8 : m.Type' = W32 8 <;> by_cases h6 : m.Type' = W32 6 <;>
    by_cases h5 : m.Type' = W32 5 <;> by_cases h4 : m.Type' = W32 4 <;>
    by_cases h3 : m.Type' = W32 3 <;> simp_all
  rcases Hcases with ⟨h2, h9, h8, h6, h5, h4, h3⟩ | Ht | Ht | Ht | Ht | Ht | Ht | Ht
  · wp_auto
    repeat (simp only [h2, h9, h8, h6, h5, h4, h3, decide_false]; wp_auto)
    iapply HΦ
    ipureintro; intro h; cases h
  all_goals (wp_auto; simp only [Ht]; wp_auto)
  all_goals (by_cases hF : m.From' = W64 0 <;> by_cases hFT : m.From' = m.To' <;>
    by_cases hT : m.Term' = W64 0)
  all_goals repeat (first |
    ((first | rw [decide_eq_true hF] | rw [decide_eq_false hF] | rw [decide_eq_true hFT] |
        rw [decide_eq_false hFT] | rw [decide_eq_true hT] | rw [decide_eq_false hT]);
      (try simp only [Bool.not_true, Bool.not_false]); wp_auto) | (wp_if_destruct <;> try wp_auto))
  all_goals (iapply HΦ; ipureintro; intro h)
  all_goals (first | (cases h; done) | skip)
  all_goals (unfold Deliverable netStepTypes; simp_all [MsgProp, MsgApp, MsgAppResp, MsgVote,
    MsgVoteResp, MsgHeartbeat, MsgHeartbeatResp])
  all_goals done

end proof

end register
end EtcdGrove
end Perennial
