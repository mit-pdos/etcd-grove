/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvwitness/deliverable.lean`. Lean-first (no
Rocq counterpart). raft v3.7 (2026-10-16, stage R6b): the scalars are read through the getters
(`wp_getter`), `m.Entries`/`m.Context` in place (`wp_field`: the fields of `msgPtsC` taken out
and put back; a `nil` slice holds no entries, no bytes, `msgPtsC_fields_acc`).
-/
module

public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.kvwitness.deliverable
public import RaftWitness.Spec.go_etcd_io.raft.v3.raftpb.Message__GetType
public import RaftWitness.Spec.go_etcd_io.raft.v3.raftpb.Message__GetTerm
public import RaftWitness.Spec.go_etcd_io.raft.v3.raftpb.Message__GetFrom
public import RaftWitness.Spec.go_etcd_io.raft.v3.raftpb.Message__GetTo

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvwitness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvwitness.Assumptions]

set_option hygiene false in
/-- A getter call on the message `Hm`, by the specs `wp_Get*` (the proof's hypotheses). -/
local macro "wp_getter" : tactic =>
  `(tactic| first
    | (wp_apply +noauto wp_GetType.1 m dq dqe cap st $$ [Hm] as Hm; iexact Hm)
    | (wp_apply +noauto wp_GetTerm.1 m dq dqe cap st $$ [Hm] as Hm; iexact Hm)
    | (wp_apply +noauto wp_GetFrom.1 m dq dqe cap st $$ [Hm] as Hm; iexact Hm)
    | (wp_apply +noauto wp_GetTo.1 m dq dqe cap st $$ [Hm] as Hm; iexact Hm))

set_option hygiene false in
/-- A read of `m.Entries` or `m.Context` in place: the fields out of `Hm`, the load, the
fields back. -/
local macro "wp_field" : tactic =>
  `(tactic| (icases msgPtsC_fields_acc _ _ _ _ _ $$ Hm with ⟨%es, %cs, HEs, HCx, %Hnil, Hback⟩
             wp_auto
             ihave Hm := Hback $$ HEs HCx))

set_option maxHeartbeats 4000000 in
theorem deliverable.wp_proof
    (wp_GetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG))
    (wp_GetTerm : raftpb.Message.GetTerm.spec (GF := GF) (hG := hG))
    (wp_GetFrom : raftpb.Message.GetFrom.spec (GF := GF) (hG := hG))
    (wp_GetTo : raftpb.Message.GetTo.spec (GF := GF) (hG := hG)) :
    deliverable.spec (GF := GF) (hG := hG) := by
  intro m dq dqe cap st
  wp_start as Hm
  ihave #Hpbinit : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  simp only [raftpb.MsgHeartbeatResp, raftpb.MsgHeartbeat, raftpb.MsgVoteResp, raftpb.MsgVote,
    raftpb.MsgAppResp, raftpb.MsgApp, raftpb.MsgReadIndex, raftpb.MsgReadIndexResp,
    raftpb.MsgTimeoutNow, raftpb.MsgProp]
  have Hcases : (st.msg.Type' ≠ W32 2 ∧ st.msg.Type' ≠ W32 15 ∧ st.msg.Type' ≠ W32 16 ∧
       st.msg.Type' ≠ W32 9 ∧ st.msg.Type' ≠ W32 8 ∧ st.msg.Type' ≠ W32 6 ∧
       st.msg.Type' ≠ W32 5 ∧ st.msg.Type' ≠ W32 4 ∧ st.msg.Type' ≠ W32 3 ∧
       st.msg.Type' ≠ W32 14) ∨
      st.msg.Type' = W32 2 ∨ st.msg.Type' = W32 15 ∨ st.msg.Type' = W32 16 ∨
      st.msg.Type' = W32 9 ∨ st.msg.Type' = W32 8 ∨ st.msg.Type' = W32 6 ∨
      st.msg.Type' = W32 5 ∨ st.msg.Type' = W32 4 ∨ st.msg.Type' = W32 3 ∨
      st.msg.Type' = W32 14 := by
    by_cases h2 : st.msg.Type' = W32 2
    · exact .inr (.inl h2)
    by_cases h15 : st.msg.Type' = W32 15
    · exact .inr (.inr (.inl h15))
    by_cases h16 : st.msg.Type' = W32 16
    · exact .inr (.inr (.inr (.inl h16)))
    by_cases h9 : st.msg.Type' = W32 9
    · exact .inr (.inr (.inr (.inr (.inl h9))))
    by_cases h8 : st.msg.Type' = W32 8
    · exact .inr (.inr (.inr (.inr (.inr (.inl h8)))))
    by_cases h6 : st.msg.Type' = W32 6
    · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl h6))))))
    by_cases h5 : st.msg.Type' = W32 5
    · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h5)))))))
    by_cases h4 : st.msg.Type' = W32 4
    · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h4))))))))
    by_cases h3 : st.msg.Type' = W32 3
    · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h3)))))))))
    by_cases h14 : st.msg.Type' = W32 14
    · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr h14)))))))))
    exact .inl ⟨h2, h15, h16, h9, h8, h6, h5, h4, h3, h14⟩
  wp_auto
  wp_getter
  rcases Hcases with ⟨h2, h15, h16, h9, h8, h6, h5, h4, h3, h14⟩ | Ht | Ht | Ht | Ht | Ht | Ht |
    Ht | Ht | Ht | Ht
  · wp_auto
    repeat (simp only [h2, h15, h16, h9, h8, h6, h5, h4, h3, h14, decide_false]; wp_auto)
    iapply HΦ
    iframe Hm
    ipureintro; intro h; cases h
  all_goals (wp_auto; simp only [Ht]; wp_auto)
  all_goals (by_cases hF : st.msg.From' = W64 0 <;> by_cases hFT : st.msg.From' = st.msg.To' <;>
    by_cases hT : st.msg.Term' = W64 0)
  all_goals repeat (first |
    (wp_getter; try wp_auto) |
    ((first | rw [decide_eq_true hF] | rw [decide_eq_false hF] | rw [decide_eq_true hFT] |
        rw [decide_eq_false hFT] | rw [decide_eq_true hT] | rw [decide_eq_false hT]);
      (try simp only [Bool.not_true, Bool.not_false]); wp_auto) |
    (wp_field; try wp_auto) |
    (wp_if_destruct <;> try wp_auto))
  all_goals (iapply HΦ; iframe Hm; ipureintro; intro h)
  all_goals (first | (cases h; done) | skip)
  all_goals (unfold Deliverable kvNetTypes; simp_all [MsgProp, MsgApp, MsgAppResp, MsgVote,
    MsgVoteResp, MsgHeartbeat, MsgHeartbeatResp, MsgReadIndex, MsgReadIndexResp, MsgTimeoutNow])
  all_goals done

end proof

end kvwitness
end EtcdGrove
end Perennial
