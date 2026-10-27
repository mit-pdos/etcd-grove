/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kv/deliverable.lean`. Lean-first (no
Rocq counterpart). raft v3.7 (2026-10-16, stage R6b): the scalars are read through the getters
(`wp_getter`), `m.Entries`/`m.Context` in place (`wp_field`: the fields of `msgPtsC` taken out
and put back; a `nil` slice holds no entries, no bytes, `msgPtsC_fields_acc`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.deliverable
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetType
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetTerm
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetFrom
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetTo
public import Spec.go_etcd_io.raft.v3.raftpb.Snapshot__GetMetadata
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetIndex
public import Proof.go_etcd_io.raft.v3.raft__Step.Dispatch

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kv

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]

open Lean Elab Tactic in
/-- A getter call on the message `Hm`, by the spec `wp_Get*` (the proof's hypotheses) of the
getter the next redex calls (`raft__Step/Dispatch.lean`); fails at once if the next redex is no
call of a message getter. (2026-10-22) It used to try the four specs in turn, and a spec that does
not fit costs a failed `wp_apply`: the proof's 80 cases spent most of their time there. -/
local elab "wp_getter" : tactic => do
  let some g ← StepProof.nextMethod? | throwError "wp_getter: the next redex is not a method call"
  unless ["GetType", "GetTerm", "GetFrom", "GetTo"].contains g do
    throwError "wp_getter: {g} is not a message getter"
  StepProof.evalTacticString s!"(wp_apply +noauto wp_{g}.1 m dq dqe cap st $$ [Hm] as Hm; iexact Hm)"

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
    (wp_GetTo : raftpb.Message.GetTo.spec (GF := GF) (hG := hG))
    (wp_Snapshot_GetMetadata : raftpb.Snapshot.GetMetadata.spec (GF := GF) (hG := hG))
    (wp_SnapshotMetadata_GetIndex : raftpb.SnapshotMetadata.GetIndex.spec (GF := GF) (hG := hG)) :
    deliverable.spec (GF := GF) (hG := hG) := by
  intro m dq dqe cap st
  wp_start as Hm
  ihave #Hpbinit : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  simp only [raftpb.MsgHeartbeatResp, raftpb.MsgHeartbeat, raftpb.MsgVoteResp, raftpb.MsgVote,
    raftpb.MsgAppResp, raftpb.MsgApp, raftpb.MsgReadIndex, raftpb.MsgReadIndexResp,
    raftpb.MsgTimeoutNow, raftpb.MsgProp, raftpb.MsgSnap]
  -- (D22 S-r) a snapshot, apart
  by_cases h7 : st.msg.Type' = W32 7
  · wp_auto
    wp_getter
    simp only [h7]
    wp_auto
    wp_getter
    try wp_auto
    by_cases hT : st.msg.Term' = W64 0
    · rw [decide_eq_true hT]
      wp_auto
      iapply HΦ
      iframe Hm
      ipureintro; intro h; cases h
    rw [decide_eq_false hT]
    wp_auto
    icases msgPtsC_snap_acc _ _ _ _ _ $$ Hm with ⟨%ps, HSn, Hsn, Hback⟩
    wp_auto
    cases Hs : st.snap with
    | none =>
      simp only [snapOpt]
      icases Hsn with %Hpn
      subst Hpn
      rw [decide_eq_true rfl]
      wp_auto
      iapply HΦ
      ihave Hm := Hback $$ HSn []
      · ipureintro; rfl
      iframe Hm
      ipureintro; intro h; cases h
    | some sv =>
      simp only [snapOpt]
      icases ownSnapM_not_null ps dq sv $$ Hsn with ⟨Hsn, %Hpn⟩
      rw [decide_eq_false Hpn]
      wp_auto
      wp_apply wp_Snapshot_GetMetadata.1 ps dq sv $$ [$Hsn] as %pm ⟨Hmd, Hsback⟩
      wp_apply wp_SnapshotMetadata_GetIndex pm dq _ $$ [$Hmd] as Hmd
      ihave Hsn := Hsback $$ Hmd
      ihave Hm := Hback $$ HSn Hsn
      try wp_auto
      by_cases hI : uint.Z (W64 2305843009213693952) ≤ uint.Z sv.Metadata'.Index'
      · rw [decide_eq_true hI]
        wp_auto
        iapply HΦ
        iframe Hm
        ipureintro; intro h; cases h
      rw [decide_eq_false hI]
      wp_auto
      have hI' : uint.Z sv.Metadata'.Index' < 2 ^ 61 := by
        have : uint.Z (W64 2305843009213693952) = 2 ^ 61 := by decide
        omega
      wp_getter
      try wp_auto
      by_cases hF : st.msg.From' = W64 0
      · rw [decide_eq_true hF]
        try wp_auto
        iapply HΦ
        iframe Hm
        ipureintro; intro h; cases h
      rw [decide_eq_false hF]
      try wp_auto
      wp_getter
      try wp_auto
      wp_getter
      try wp_auto
      by_cases hFT : st.msg.From' = st.msg.To'
      · rw [decide_eq_true hFT]
        try wp_auto
        iapply HΦ
        iframe Hm
        ipureintro; intro h; cases h
      rw [decide_eq_false hFT]
      try wp_auto
      wp_field
      iapply HΦ
      iframe Hm
      ipureintro
      intro hb
      refine ⟨.inr (.inr (.inr (.inr ⟨h7, hT, sv, Hs, hI'⟩))), hF, hFT, .inl (Hnil.2 ?_)⟩
      revert hb; simp
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
    repeat (simp only [h2, h15, h16, h9, h8, h6, h5, h4, h3, h14, h7, decide_false]; wp_auto)
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

end kv
end EtcdGrove
end Perennial
