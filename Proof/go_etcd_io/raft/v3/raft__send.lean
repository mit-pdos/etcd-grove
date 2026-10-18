/- Port of election_proof/proof_raft__send.v.

Lean notes: Rocq's `wp_if_join` on the `From` test is `wp_join`.

raft v3.7 (stage R4): the message is a pointer read through its getters (`GetFrom`, `GetType`,
`GetTerm`, `GetTo`, R1's specs over `msgPtsC`). `m.From = new(r.id)` and `m.Term = new(r.Term)`
are fresh frozen cells (`cellRO_alloc`) stored by `msgPtsC_store_From`/`_Term`; the queued pointer
goes to `ownRaftPhysC_msgs`/`_msgsAA` with the message owned. Instead of destructuring the
message record (the old proof), each case rewrites every getter's result by the case's facts
(`getters`), so that `wp_auto` decides the tests; the queued message's contribution
(`msgAbs`) and its `OutTermOk`/`AAMsgOk` are pure.
-/
module

public import Spec.go_etcd_io.raft.v3.raft__send
public import Spec.go_etcd_io.raft.v3.traceSendMessage
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetFrom
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetType
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetTerm
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetTo
public import Proof.go_etcd_io.raft.v3.InvPbMsg

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- Two message types differ. -/
local macro "tyne" : tactic => `(tactic| simp [MsgReadIndex, MsgProp, MsgVote, MsgVoteResp,
  MsgPreVote, MsgPreVoteResp, MsgApp, MsgAppResp, MsgHeartbeat, MsgHeartbeatResp,MsgCheckQuorum, MsgReadIndexResp,
  MsgSnap, MsgTransferLeader])

set_option hygiene false in
/-- A fact about the queued message's type, from the case's type equation `h` (the message in
`Hm` has been simplified by `getters`, so its `Type'` may be a literal). -/
local macro "tyfact " h:term : tactic => `(tactic| (
  have Hty' := Hty
  simp only [$h:term] at Hty'
  simp only [Hty1, $h:term, MsgVote, MsgVoteResp, MsgPreVote, MsgPreVoteResp, MsgApp, MsgAppResp, MsgHeartbeat, MsgHeartbeatResp,MsgCheckQuorum, MsgReadIndex, MsgReadIndexResp, MsgSnap, MsgProp] at Hty' ⊢
  first | exact Hty' | decide | tyne))

set_option hygiene false in
/-- Run the body through its getter calls (`GetType`, `GetTerm`, `GetTo` on the message `Hm`),
rewriting each result by the case's facts so that `wp_auto` decides the tests. -/
local macro "getters" "[" args:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  repeat (first
    | (wp_apply wp_GetType.1 $$ [Hm] as Hm
       (· iexact Hm)
       all_goals try simp +decide only [Hty1, Hte1, Hto1, _root_.decide_false, _root_.decide_true, MsgVote, MsgVoteResp, MsgPreVote, MsgPreVoteResp, MsgApp, MsgAppResp, MsgHeartbeat, MsgHeartbeatResp,MsgCheckQuorum, MsgReadIndex, MsgReadIndexResp, MsgSnap, MsgProp, $args,*])
    | (wp_apply wp_GetTerm.1 $$ [Hm] as Hm
       (· iexact Hm)
       all_goals try simp +decide only [Hty1, Hte1, Hto1, _root_.decide_false, _root_.decide_true, MsgVote, MsgVoteResp, MsgPreVote, MsgPreVoteResp, MsgApp, MsgAppResp, MsgHeartbeat, MsgHeartbeatResp,MsgCheckQuorum, MsgReadIndex, MsgReadIndexResp, MsgSnap, MsgProp, $args,*])
    | (wp_apply wp_GetTo.1 $$ [Hm] as Hm
       (· iexact Hm)
       all_goals try simp +decide only [Hty1, Hte1, Hto1, _root_.decide_false, _root_.decide_true, MsgVote, MsgVoteResp, MsgPreVote, MsgPreVoteResp, MsgApp, MsgAppResp, MsgHeartbeat, MsgHeartbeatResp,MsgCheckQuorum, MsgReadIndex, MsgReadIndexResp, MsgSnap, MsgProp, $args,*])
    | (wp_apply raft.wp_load_idC $$ Hphys as Hphys
       all_goals try simp +decide only [Hty1, Hte1, Hto1, _root_.decide_false, _root_.decide_true, MsgVote, MsgVoteResp, MsgPreVote, MsgPreVoteResp, MsgApp, MsgAppResp, MsgHeartbeat, MsgHeartbeatResp,MsgCheckQuorum, MsgReadIndex, MsgReadIndexResp, MsgSnap, MsgProp, $args,*])
    | (wp_apply raft.wp_load_TermC $$ Hphys as Hphys
       imod cellRO_alloc $$ «$r0» with #cTe
       icases msgPtsC_store_Term _ _ _ _ $$ Hm with ⟨%pte, HTe, HbackT⟩
       wp_auto
       ihave Hm := HbackT $$ %_ %s.term HTe cTe
       all_goals try simp +decide only [Hty1, Hte1, Hto1, _root_.decide_false, _root_.decide_true, MsgVote, MsgVoteResp, MsgPreVote, MsgPreVoteResp, MsgApp, MsgAppResp, MsgHeartbeat, MsgHeartbeatResp,MsgCheckQuorum, MsgReadIndex, MsgReadIndexResp, MsgSnap, MsgProp, $args,*])
    | wp_auto)))

set_option hygiene false in
/-- The common tail once the routing decision has been made: take the queue out of
`ownRaftPhys`, build the one-element slice literal, append it, store the queue back,
trace, and return. What is left is the queue accessor's wand `Hback`, which wants the
queued message (`Hm`) and its contribution to the abstract outbox (`msgAbs`). -/
local macro "send_tail " acc:term : tactic => `(tactic| (
  icases ($acc) $$ Hphys with ⟨%sl, %ls, Hf, Hq, Hq_cap, Hback⟩
  try wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %m_sl ⟨m_sl, -⟩
  try wp_auto
  wp_apply wp_slice_append $$ [Hq Hq_cap m_sl] as %q' ⟨Hq, Hq_cap, -⟩
  · iframe
  try wp_auto
  wp_apply wp_traceSendMessage
  iapply HΦ))

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1600000 in
theorem raft.send.wp_proof
    (wp_traceSendMessage : traceSendMessage.spec (GF := GF) (hG := hG))
    (wp_GetFrom : raftpb.Message.GetFrom.spec (GF := GF) (hG := hG))
    (wp_GetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG))
    (wp_GetTerm : raftpb.Message.GetTerm.spec (GF := GF) (hG := hG))
    (wp_GetTo : raftpb.Message.GetTo.spec (GF := GF) (hG := hG)) :
    raft.send.spec (GF := GF) (hG := hG) := by
  intro c r id s ml m ents sn ctx rs out Hfrom Hok Hsn
  wp_start as H
  iNamed H
  wp_auto
  wp_apply wp_GetFrom.1 $$ [$Hm] as Hm
  obtain ⟨src, Hsrc_eq⟩ : ∃ src, src = if m.From' = W64 0 then id else m.From' := ⟨_, rfl⟩
  wp_join iprop(r_ptr ↦ r ∗ m_ptr ↦ ml ∗ msgOwn ml (DFrac.own 1) ⟨{ m with From' := src }, ents, sn, ctx, rs⟩ ∗
      ownRaftPhysCV c c.voters r id s)
    with [r m Hm Hphys] as ⟨r, m, Hm, Hphys⟩
  · wp_apply raft.wp_load_idC $$ Hphys as Hphys
    imod cellRO_alloc $$ «$r0» with #c0
    icases msgPtsC_store_From _ _ _ _ $$ Hm with ⟨%pf, Hpf, Hback⟩
    wp_auto
    ihave Hm := Hback $$ %_ %id Hpf c0
    rw [show src = id by rw [Hsrc_eq, ite_eq_left (by simpa using Hif)]]
    iframe
    ipureintro; rfl
  · have Hmeq : { m with From' := src } = m := by
      have Hne : m.From' ≠ W64 0 := by simpa using Hif
      rw [Hsrc_eq, ite_eq_right Hne]
    rw [Hmeq]
    iframe
  generalize Hm1 : ({ m with From' := src } : MessageM) = m1 at *
  have Hty1 : m1.Type' = m.Type' := by rw [← Hm1]
  have Hte1 : m1.Term' = m.Term' := by rw [← Hm1]
  have Hto1 : m1.To' = m.To' := by rw [← Hm1]
  have Hsrc : m.Type' ≠ MsgReadIndex → m.Type' ≠ MsgTransferLeader → src = id := by
    intro Hne Hne2
    rcases Hfrom with Hf | Hf | Hf | Hf
    · rw [Hsrc_eq, ite_eq_left Hf]
    · rw [Hsrc_eq, Hf]; split <;> simp_all
    · exact absurd Hf Hne
    · exact absurd Hf Hne2
  unfold SendOk at Hok
  rcases Hok with ⟨ty, Hvoty, Hty, Hmterm, Hself, Hself2, Hpvt, Htc, rfl⟩ |
    ⟨ty, Hlty, Hty, Hmterm, Hself, rfl⟩ |
    (⟨HSnap, Hmterm, Hself⟩ | ⟨Hty, Hmterm, Hself, rfl⟩) | ⟨HAR, Hmterm, Hself2, rfl⟩ |
    (⟨HProp, Hmterm, Hself, rfl⟩ | ⟨HRI, Hmterm, Hself, rfl⟩)
  · -- (a) a vote message: `Term` is kept. A request goes onto `r.msgs`, a response onto
    -- `r.msgsAfterAppend`.
    have Hs := Hsrc (by rcases Hvoty with h | h | h | h <;> rw [h] <;> tyne)
      (by rcases Hvoty with h | h | h | h <;> rw [h] <;> tyne)
    subst Hs
    have Hot : OutTermOk s.prevote s.term s.gh.tc m1 :=
      ⟨by rw [Hte1]; exact Htc, fun h => by rw [Hte1, Hty1]; exact Hpvt h⟩
    have Hns : ty ≠ .snap := by
      rintro rfl; rcases Hvoty with h | h | h | h <;> rw [h] at Hty <;> exact absurd Hty (by decide)
    have Habs : msgAbs ⟨m1, ents, sn, ctx, rs⟩ (some (absMsg ty m1 ents ctx)) :=
      Or.inr (Or.inl ⟨ty, by rw [Hty1]; exact Hty, Hns, rfl⟩)
    rcases Hvoty with Hvt | Hvt | Hvt | Hvt
    · getters [Hvt, Hmterm, Hself (.inl Hvt)]
      send_tail ownRaftPhysC_msgs
      ihave Hphys := Hback $$ %q' %ml %_ %(some (absMsg ty m1 ents ctx)) Hf Hq Hq_cap Hm %Habs %Hot
      iapply ownRaftPhysC_eq _ _ _ _ ?_ $$ Hphys
      subst Hm1; rfl
    · getters [Hvt, Hmterm]
      send_tail ownRaftPhysC_msgsAA
      ihave Hphys := Hback $$ %q' %ml %_ %(some (absMsg ty m1 ents ctx)) Hf Hq Hq_cap Hm %Habs [] %Hot
      · ipureintro
        subst Hm1
        refine ⟨by simp only [Hvt]; tyne, rfl, fun Hto => ?_⟩
        obtain ⟨He, Hc, Ht⟩ := Hself2 Hto
        exact ⟨Hmterm, He, Hc, fun h => by simp [Hvt, MsgAppResp, MsgVoteResp] at h, Ht⟩
      iapply ownRaftPhysC_eq _ _ _ _ ?_ $$ Hphys
      subst Hm1; rfl
    · getters [Hvt, Hmterm, Hself (.inr Hvt)]
      send_tail ownRaftPhysC_msgs
      ihave Hphys := Hback $$ %q' %ml %_ %(some (absMsg ty m1 ents ctx)) Hf Hq Hq_cap Hm %Habs %Hot
      iapply ownRaftPhysC_eq _ _ _ _ ?_ $$ Hphys
      subst Hm1; rfl
    · getters [Hvt, Hmterm]
      send_tail ownRaftPhysC_msgsAA
      ihave Hphys := Hback $$ %q' %ml %_ %(some (absMsg ty m1 ents ctx)) Hf Hq Hq_cap Hm %Habs [] %Hot
      · ipureintro
        subst Hm1
        refine ⟨by simp only [Hvt]; tyne, rfl, fun Hto => ?_⟩
        obtain ⟨He, Hc, Ht⟩ := Hself2 Hto
        exact ⟨Hmterm, He, Hc, fun h => by simp [Hvt, MsgAppResp, MsgPreVoteResp] at h, Ht⟩
      iapply ownRaftPhysC_eq _ _ _ _ ?_ $$ Hphys
      subst Hm1; rfl
  · -- (b) `Term` must be unset and is stamped with `r.Term` (= `s.term`); not a
    -- response, so onto `r.msgs` after the self-address check.
    have Hs := Hsrc (by rcases Hlty with h | h | h | h <;> rw [h] <;> tyne)
      (by rcases Hlty with h | h | h | h <;> rw [h] <;> tyne)
    subst Hs
    have Hns : ty ≠ .snap := by
      rintro rfl; rcases Hlty with h | h | h | h <;> rw [h] at Hty <;> exact absurd Hty (by decide)
    rcases Hlty with Hvt | Hvt | Hvt | Hvt <;>
    · getters [Hvt, Hmterm, Hself]
      send_tail ownRaftPhysC_msgs
      ihave Hphys := Hback $$ %q' %ml %_ %_ Hf Hq Hq_cap Hm [] []
      · ipureintro
        exact Or.inr (Or.inl ⟨ty, by tyfact Hvt, Hns, rfl⟩)
      · ipureintro
        exact ⟨.inl (by first | exact Int.le_refl _ | (rw [Hte1, Hmterm]; word)), fun _ => ⟨Int.le_refl _, by tyfact Hvt⟩⟩
      iapply ownRaftPhysC_eq _ _ _ _ ?_ $$ Hphys
      subst Hm1; rfl
  · -- (c') `MsgSnap`: (b)'s path through the body; the abstract message is the
    -- snapshot's, `absSnapFrom`, at the message's snapshot `sv`.
    have Hs := Hsrc (by rw [HSnap]; tyne) (by rw [HSnap]; tyne)
    subst Hs
    obtain ⟨sv, rfl, rfl⟩ := Hsn HSnap
    getters [HSnap, Hmterm, Hself]
    send_tail ownRaftPhysC_msgs
    ihave Hphys := Hback $$ %q' %ml %_ %_ Hf Hq Hq_cap Hm [] []
    · ipureintro
      exact Or.inr (Or.inr ⟨sv, by simp only [Hty1, HSnap, MsgVote, MsgVoteResp, MsgPreVote, MsgPreVoteResp, MsgApp, MsgAppResp, MsgHeartbeat, MsgHeartbeatResp,MsgCheckQuorum, MsgReadIndex, MsgReadIndexResp, MsgSnap, MsgProp]; rfl, rfl, rfl⟩)
    · ipureintro
      exact ⟨.inl (by first | exact Int.le_refl _ | (rw [Hte1, Hmterm]; word)), fun _ => ⟨Int.le_refl _, by simp only [Hty1, HSnap, MsgVote, MsgVoteResp, MsgPreVote, MsgPreVoteResp, MsgApp, MsgAppResp, MsgHeartbeat, MsgHeartbeatResp,MsgCheckQuorum, MsgReadIndex, MsgReadIndexResp, MsgSnap, MsgProp]; tyne⟩⟩
    iapply ownRaftPhysC_eq _ _ _ _ ?_ $$ Hphys
    subst Hm1; rfl
  · -- (c) a type the model does not see: stamped, onto `r.msgs`, and it drops out of
    -- the abstract outbox.
    obtain ⟨HnProp, HnA, HnAR, HnV, HnVR, HnS, HnH, HnHR, HnRI, HnRIR, HnPV, HnPVR⟩ :=
      mtypeOf_None_ne _ Hty
    simp only [MsgVote, MsgVoteResp, MsgPreVote, MsgPreVoteResp, MsgApp, MsgAppResp, MsgHeartbeat, MsgHeartbeatResp,MsgCheckQuorum, MsgReadIndex, MsgReadIndexResp, MsgSnap, MsgProp] at HnProp HnAR HnV HnVR HnRI HnPV HnPVR
    getters [Hmterm, Hself, HnProp, HnAR, HnV, HnVR, HnRI, HnPV, HnPVR]
    send_tail ownRaftPhysC_msgs
    ihave Hphys := Hback $$ %q' %ml %_ %none Hf Hq Hq_cap Hm [] []
    · ipureintro
      exact Or.inl ⟨by simp only [Hty1]; exact Hty, rfl⟩
    · ipureintro
      exact ⟨.inl (by first | exact Int.le_refl _ | (rw [Hte1, Hmterm]; word)), fun _ => ⟨Int.le_refl _, by simp only [Hty1]; exact HnPVR⟩⟩
    iapply ownRaftPhysC_eq _ _ _ _ ?_ $$ Hphys
    rfl
  · -- (d) `MsgAppResp`: stamped, and a response, so onto `r.msgsAfterAppend`; it may
    -- be self-addressed (`appendEntry` does exactly that).
    have Hs := Hsrc (by rw [HAR]; tyne) (by rw [HAR]; tyne)
    subst Hs
    getters [HAR, Hmterm]
    send_tail ownRaftPhysC_msgsAA
    ihave Hphys := Hback $$ %q' %ml %_ %_ Hf Hq Hq_cap Hm [] [] []
    · ipureintro
      exact Or.inr (Or.inl ⟨.appResp, by simp only [Hty1, HAR, MsgVote, MsgVoteResp, MsgPreVote, MsgPreVoteResp, MsgApp, MsgAppResp, MsgHeartbeat, MsgHeartbeatResp,MsgCheckQuorum, MsgReadIndex, MsgReadIndexResp, MsgSnap, MsgProp]; rfl, by decide, rfl⟩)
    · ipureintro
      subst Hm1
      refine ⟨by simp [HAR, MsgVote, MsgVoteResp, MsgPreVote, MsgPreVoteResp, MsgApp, MsgAppResp, MsgHeartbeat, MsgHeartbeatResp,MsgCheckQuorum, MsgReadIndex, MsgReadIndexResp, MsgSnap, MsgProp], rfl, fun Hto => ?_⟩
      obtain ⟨He, Hc, Hnz, Hrj⟩ := Hself2 (by simpa using Hto)
      exact ⟨Hnz, He, Hc, fun _ => Hrj, by simp [HAR, MsgVote, MsgVoteResp, MsgPreVote, MsgPreVoteResp, MsgApp, MsgAppResp, MsgHeartbeat, MsgHeartbeatResp,MsgCheckQuorum, MsgReadIndex, MsgReadIndexResp, MsgSnap, MsgProp]⟩
    · ipureintro
      exact ⟨.inl (by first | exact Int.le_refl _ | (rw [Hte1, Hmterm]; word)), fun _ => ⟨Int.le_refl _, by simp [Hty1, HAR, MsgVote, MsgVoteResp, MsgPreVote, MsgPreVoteResp, MsgApp, MsgAppResp, MsgHeartbeat, MsgHeartbeatResp,MsgCheckQuorum, MsgReadIndex, MsgReadIndexResp, MsgSnap, MsgProp]⟩⟩
    iapply ownRaftPhysC_eq _ _ _ _ ?_ $$ Hphys
    subst Hm1; rfl
  · -- (e) a forwarded proposal: `Term` stays zero; not a response
    have Hs := Hsrc (by rw [HProp]; tyne) (by rw [HProp]; tyne)
    subst Hs
    getters [HProp, Hmterm, Hself]
    send_tail ownRaftPhysC_msgs
    ihave Hphys := Hback $$ %q' %ml %_ %(some (absMsg .propose m1 ents ctx)) Hf Hq Hq_cap Hm [] []
    · ipureintro
      exact Or.inr (Or.inl ⟨.propose, by rw [Hty1, HProp]; rfl, by decide, rfl⟩)
    · ipureintro
      exact ⟨.inl (by first | exact Int.le_refl _ | (rw [Hte1, Hmterm]; word)), fun _ => ⟨by rw [Hte1, Hmterm]; word, by rw [Hty1, HProp]; tyne⟩⟩
    iapply ownRaftPhysC_eq _ _ _ _ ?_ $$ Hphys
    subst Hm1; simp only [sendMsgs, absMsg, Hmterm]; rfl
  · -- (e') a forwarded `MsgReadIndex` (2026-10-12): as a proposal, from `src`
    getters [HRI, Hmterm, Hself]
    send_tail ownRaftPhysC_msgs
    ihave Hphys := Hback $$ %q' %ml %_ %(some (absMsg .readIndex m1 ents ctx)) Hf Hq Hq_cap Hm [] []
    · ipureintro
      exact Or.inr (Or.inl ⟨.readIndex, by rw [Hty1, HRI]; rfl, by decide, rfl⟩)
    · ipureintro
      exact ⟨.inl (by first | exact Int.le_refl _ | (rw [Hte1, Hmterm]; word)), fun _ => ⟨by rw [Hte1, Hmterm]; word, by rw [Hty1, HRI]; tyne⟩⟩
    iapply ownRaftPhysC_eq _ _ _ _ ?_ $$ Hphys
    subst Hm1 Hsrc_eq; simp only [sendMsgs, absMsg, Hmterm]; rfl

end proof

end EtcdGrove
end Perennial
