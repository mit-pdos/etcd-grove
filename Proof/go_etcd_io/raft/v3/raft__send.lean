/- Port of election_proof/proof_raft__send.v.

Lean notes: Rocq's `wp_if_join` on the `From` test is `wp_join`. Instead of rewriting
each `bool_decide (m.Type = …)` by hand, each case destructures `m` and substitutes its
`Type` (and, where pinned, `Term`) field, so `wp_auto` decides the type tests itself;
only the not-described case (c) rewrites with the inequalities of `mtypeOf_None_ne`.
-/
module

public import Spec.go_etcd_io.raft.v3.raft__send
public import Spec.go_etcd_io.raft.v3.traceSendMessage

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

set_option hygiene false in
/-- The common tail once the routing decision has been made: take the queue out of
`ownRaftPhys`, build the one-element slice literal, append it, store the queue back,
trace, and return. What is left is the queue accessor's wand `Hback`, which wants the
appended message's contribution to the abstract outbox (`msgAbs`). -/
local macro "send_tail " acc:term : tactic => `(tactic| (
  icases ($acc) $$ Hphys with ⟨%sl, %ms, Hf, Hq, Hq_cap, Hback⟩
  wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %m_sl ⟨m_sl, -⟩
  wp_auto
  wp_apply wp_slice_append $$ [Hq Hq_cap m_sl] as %q' ⟨Hq, Hq_cap, -⟩
  · iframe
  try wp_auto
  wp_apply wp_traceSendMessage
  iapply HΦ))

set_option hygiene false in
/-- The queued message's term bound (`OutTermOk`): the caller's (`SendOk`'s vote clause,
`Hpvt`), or the node's own term stamped in, or `0`. -/
local macro "out_term" : tactic => `(tactic| (
  first
    | exact Hpvt
    | (intro _
       refine ⟨?_, ?_⟩ <;>
         first
           | (simp only; omega)
           | (simp only; word)
           | (simp only [MsgPreVoteResp] at *; exact HnPVR)
           | simp [MsgPreVoteResp, MsgAppResp, MsgApp, MsgHeartbeat, MsgHeartbeatResp,
               MsgReadIndexResp, MsgSnap, MsgProp])))

set_option hygiene false in
/-- A described type other than `MsgSnap`: the wand gets the abstraction of the queued
message, whose `Entries` is `m`'s, and the outbox is then `sendMsgs s out` by
computation. -/
local macro "finish_some" : tactic => `(tactic| (
  ihave Hphys := Hback $$ %q' %_ %(some (absMsg ty _ ents ctx)) Hf Hq Hq_cap [] []
  · unfold msgAbs
    iright; ileft
    iexists ty, ents, ctx
    iframe Hents Hctx
    ipureintro
    refine ⟨Hty, ?_, rfl⟩
    rintro rfl
    exact absurd Hty (by decide)
  · ipureintro; out_term
  iapply ownRaftPhys_eq _ _ _ _ _ ?_ $$ Hphys
  rfl))

set_option hygiene false in
/-- A vote response, onto `r.msgsAfterAppend`: as `finish_some`, and the queued
message is `AAMsgOk` -- from `id`, and if self-addressed, as `SendOk`'s vote clause
says (`Hself2`). -/
local macro "finish_some_aa" : tactic => `(tactic| (
  ihave Hphys := Hback $$ %q' %_ %(some (absMsg ty _ ents ctx)) Hf Hq Hq_cap [] [] []
  · unfold msgAbs
    iright; ileft
    iexists ty, ents, ctx
    iframe Hents Hctx
    ipureintro
    refine ⟨Hty, ?_, rfl⟩
    rintro rfl
    exact absurd Hty (by decide)
  · ipureintro
    refine ⟨by simp [MsgAppResp, MsgVoteResp, MsgPreVoteResp], rfl, fun Hto => ?_⟩
    obtain ⟨He, Hc, Ht⟩ := Hself2 Hto
    exact ⟨Hmterm, He, Hc, fun h => by simp [MsgAppResp] at h, Ht⟩
  · ipureintro; out_term
  iapply ownRaftPhys_eq _ _ _ _ _ ?_ $$ Hphys
  rfl))

set_option hygiene false in
/-- An undescribed type: it contributes nothing. -/
local macro "finish_none" : tactic => `(tactic| (
  ihave Hphys := Hback $$ %q' %_ %none Hf Hq Hq_cap [] []
  · unfold msgAbs
    ileft
    ipureintro
    exact ⟨Hty, rfl⟩
  · ipureintro; out_term
  iapply ownRaftPhys_eq _ _ _ _ _ ?_ $$ Hphys
  rfl))

set_option linter.unusedSimpArgs false in
theorem raft.send.wp_proof
    (wp_traceSendMessage : traceSendMessage.spec (GF := GF) (hG := hG)) :
    raft.send.spec (GF := GF) (hG := hG) := by
  intro cfg r id s m ents ctx out Hfrom Hok
  wp_start as H
  iNamed H
  wp_auto
  -- `From` unset: `send` fills it in with `r.id`; already set (`r.id`, 2026-10-06, or a
  -- forwarded read request's requester, 2026-10-12): nothing is written. Either way `m`
  -- is then `m` with `From := src`, and `src = id` unless `m` is a `MsgReadIndex`.
  obtain ⟨src, Hsrc_eq⟩ : ∃ src, src = if m.From' = W64 0 then id else m.From' := ⟨_, rfl⟩
  have Hsrc : m.Type' ≠ MsgReadIndex → id = src := by
    intro Hne
    rcases Hfrom with Hf | Hf | Hf
    · rw [Hsrc_eq, ite_eq_left Hf]
    · rw [Hsrc_eq, Hf]; split <;> simp_all
    · exact absurd Hf Hne
  wp_join iprop(r_ptr ↦ r ∗ m_ptr ↦ { m with From' := src } ∗ ownRaftPhys cfg r id s)
    with [r m Hphys] as ⟨r, m, Hphys⟩
  · wp_apply raft.wp_load_id $$ Hphys as Hphys
    rw [show src = id by rw [Hsrc_eq, ite_eq_left (by simpa using Hif)]]
    iframe
    ipureintro; rfl
  · have Hmeq : { m with From' := src } = m := by
      have Hne : m.From' ≠ W64 0 := by simpa using Hif
      rw [Hsrc_eq, ite_eq_right Hne]
    rw [Hmeq]
    iframe
  unfold SendOk at Hok
  rcases Hok with ⟨ty, Hvoty, Hty, Hmterm, Hself, Hself2, Hpvt, rfl⟩ |
    ⟨ty, Hlty, Hty, Hmterm, Hself, rfl⟩ |
    (⟨HSnap, Hmterm, Hself⟩ | ⟨Hty, Hmterm, Hself, rfl⟩) | ⟨HAR, Hmterm, Hself2, rfl⟩ |
    (⟨HProp, Hmterm, Hself, rfl⟩ | ⟨HRI, Hmterm, Hself, rfl⟩)
  rotate_right
  · -- (e') a forwarded `MsgReadIndex` (2026-10-12): as a proposal, from `src`
    obtain ⟨mty, mto, mfrom, mterm, mlt, midx, ments, mcommit, mvote, msnap, mrej, mrh, mctx,
      mresp⟩ := m
    simp only [MsgReadIndex] at HRI Hmterm Hself Hsrc_eq ⊢
    subst HRI Hmterm
    rw [← Hsrc_eq]
    wp_auto
    wp_apply raft.wp_load_id $$ Hphys as Hphys
    rw [decide_eq_false Hself]
    wp_auto
    send_tail ownRaftPhys_msgs
    ihave Hphys := Hback $$ %q' %_ %(some (absMsg .readIndex _ ents ctx)) Hf Hq Hq_cap [] []
    · unfold msgAbs
      iright; ileft
      iexists .readIndex, ents, ctx
      iframe Hents Hctx
      ipureintro
      exact ⟨rfl, by decide, rfl⟩
    · ipureintro; out_term
    iapply ownRaftPhys_eq _ _ _ _ _ ?_ $$ Hphys
    rfl
  -- every other message has `From = id` once queued
  all_goals
    first
      | (have Hs := Hsrc (by
            intro h
            first
              | (rcases Hvoty with h' | h' | h' | h' <;> rw [h'] at h <;> simp [MsgReadIndex, MsgProp, MsgVote, MsgVoteResp, MsgPreVote, MsgPreVoteResp, MsgApp,
                  MsgAppResp, MsgHeartbeat, MsgHeartbeatResp, MsgReadIndexResp, MsgSnap] at h)
              | (rcases Hlty with h' | h' | h' | h' <;> rw [h'] at h <;> simp [MsgReadIndex, MsgProp, MsgVote, MsgVoteResp, MsgPreVote, MsgPreVoteResp, MsgApp,
                  MsgAppResp, MsgHeartbeat, MsgHeartbeatResp, MsgReadIndexResp, MsgSnap] at h)
              | (rw [h, show mtypeOf MsgReadIndex = some .readIndex from rfl] at Hty
                 exact absurd Hty (by simp))
              | (rw [h] at HSnap; simp [MsgReadIndex, MsgProp, MsgVote, MsgVoteResp, MsgPreVote, MsgPreVoteResp, MsgApp,
                  MsgAppResp, MsgHeartbeat, MsgHeartbeatResp, MsgReadIndexResp, MsgSnap] at HSnap)
              | (rw [h] at HAR; simp [MsgReadIndex, MsgProp, MsgVote, MsgVoteResp, MsgPreVote, MsgPreVoteResp, MsgApp,
                  MsgAppResp, MsgHeartbeat, MsgHeartbeatResp, MsgReadIndexResp, MsgSnap] at HAR)
              | (rw [h] at HProp; simp [MsgReadIndex, MsgProp, MsgVote, MsgVoteResp, MsgPreVote, MsgPreVoteResp, MsgApp,
                  MsgAppResp, MsgHeartbeat, MsgHeartbeatResp, MsgReadIndexResp, MsgSnap] at HProp))
         subst Hs)
  · -- (a) a vote message: `Term` is kept. `MsgVote` goes onto `r.msgs`, `MsgVoteResp`
    -- onto `r.msgsAfterAppend`; either way the abstract outbox grows by exactly that
    -- message -- up to permutation, since a `MsgVote` lands in front of whatever
    -- `msgsAfterAppend` holds.
    rcases Hvoty with Hvt | Hvt | Hvt | Hvt
    · -- `MsgVote` is not a response, so it goes onto `r.msgs`.
      obtain ⟨mty, mto, mfrom, mterm, mlt, midx, ments, mcommit, mvote, msnap, mrej, mrh, mctx,
        mresp⟩ := m
      simp only [MsgVote] at Hvt
      subst Hvt
      simp only at Hmterm Hself Hty Hpvt ⊢
      wp_auto
      rw [decide_eq_false Hmterm]
      wp_auto
      -- not self-addressed
      wp_apply raft.wp_load_id $$ Hphys as Hphys
      rw [decide_eq_false (Hself (.inl rfl))]
      wp_auto
      send_tail ownRaftPhys_msgs
      finish_some
    · -- `MsgVoteResp` is a response, so it goes onto `r.msgsAfterAppend`.
      obtain ⟨mty, mto, mfrom, mterm, mlt, midx, ments, mcommit, mvote, msnap, mrej, mrh, mctx,
        mresp⟩ := m
      simp only [MsgVoteResp] at Hvt
      subst Hvt
      simp only at Hmterm Hself Hself2 Hty Hpvt ⊢
      wp_auto
      rw [decide_eq_false Hmterm]
      wp_auto
      send_tail ownRaftPhys_msgsAA
      finish_some_aa
    · -- `MsgPreVote` (2026-10-04): a request, onto `r.msgs`, as `MsgVote`.
      obtain ⟨mty, mto, mfrom, mterm, mlt, midx, ments, mcommit, mvote, msnap, mrej, mrh, mctx,
        mresp⟩ := m
      simp only [MsgPreVote] at Hvt
      subst Hvt
      simp only at Hmterm Hself Hty Hpvt ⊢
      wp_auto
      rw [decide_eq_false Hmterm]
      wp_auto
      wp_apply raft.wp_load_id $$ Hphys as Hphys
      rw [decide_eq_false (Hself (.inr rfl))]
      wp_auto
      send_tail ownRaftPhys_msgs
      finish_some
    · -- `MsgPreVoteResp`: a response, onto `r.msgsAfterAppend`.
      obtain ⟨mty, mto, mfrom, mterm, mlt, midx, ments, mcommit, mvote, msnap, mrej, mrh, mctx,
        mresp⟩ := m
      simp only [MsgPreVoteResp] at Hvt
      subst Hvt
      simp only at Hmterm Hself Hself2 Hty Hpvt ⊢
      wp_auto
      rw [decide_eq_false Hmterm]
      wp_auto
      send_tail ownRaftPhys_msgsAA
      finish_some_aa
  · -- (b) `Term` must be unset and is stamped with `r.Term` (= `s.term`); not a
    -- response, so onto `r.msgs` after the self-address check.
    obtain ⟨mty, mto, mfrom, mterm, mlt, midx, ments, mcommit, mvote, msnap, mrej, mrh, mctx,
      mresp⟩ := m
    simp only at Hlty Hmterm Hself Hty ⊢
    subst Hmterm
    rcases Hlty with Hvt | Hvt | Hvt | Hvt <;>
    · simp only [MsgApp, MsgHeartbeat, MsgReadIndexResp, MsgHeartbeatResp] at Hvt
      subst Hvt
      wp_auto
      wp_apply raft.wp_load_Term $$ Hphys as Hphys
      wp_apply raft.wp_load_id $$ Hphys as Hphys
      rw [decide_eq_false Hself]
      wp_auto
      send_tail ownRaftPhys_msgs
      finish_some
  · -- (c') `MsgSnap`: (b)'s path through the body; the abstract message is the
    -- snapshot's, `absSnapFrom`, at the caller's `sv`/`voters`.
    obtain ⟨mty, mto, mfrom, mterm, mlt, midx, ments, mcommit, mvote, msnap, mrej, mrh, mctx,
      mresp⟩ := m
    simp only [MsgSnap] at HSnap Hmterm Hself ⊢
    subst HSnap Hmterm
    wp_auto
    wp_apply raft.wp_load_Term $$ Hphys as Hphys
    wp_apply raft.wp_load_id $$ Hphys as Hphys
    rw [decide_eq_false Hself]
    wp_auto
    icases Hsnap $$ %rfl with ⟨%sv, %voters, %Hout, #Hsv, #Hvoters⟩
    subst Hout
    send_tail ownRaftPhys_msgs
    ihave Hphys := Hback $$ %q' %_ %(some (absSnap _ sv voters)) Hf Hq Hq_cap [] []
    · unfold msgAbs
      iright; iright
      iexists sv, voters
      iframe Hsv Hvoters
      ipureintro
      exact ⟨rfl, rfl⟩
    · ipureintro; out_term
    iapply ownRaftPhys_eq _ _ _ _ _ ?_ $$ Hphys
    rfl
  · -- (c) a type the model does not see: stamped, onto `r.msgs`, and it drops out of
    -- the abstract outbox.
    obtain ⟨HnProp, HnA, HnAR, HnV, HnVR, HnS, HnH, HnHR, HnRI, HnRIR, HnPV, HnPVR⟩ :=
      mtypeOf_None_ne _ Hty
    obtain ⟨mty, mto, mfrom, mterm, mlt, midx, ments, mcommit, mvote, msnap, mrej, mrh, mctx,
      mresp⟩ := m
    simp only [MsgProp, MsgAppResp, MsgVote, MsgVoteResp, MsgReadIndex, MsgPreVote,
      MsgPreVoteResp] at HnProp HnAR HnV HnVR HnRI HnPV HnPVR
    simp only at Hmterm Hself Hty ⊢
    subst Hmterm
    repeat (first
      | (simp only [HnV, HnVR, HnPV, HnPVR, HnProp, HnRI, HnAR, decide_false]; wp_auto)
      | (wp_apply raft.wp_load_Term $$ Hphys as Hphys)
      | (wp_apply raft.wp_load_id $$ Hphys as Hphys)
      | (rw [decide_eq_false Hself]; wp_auto))
    send_tail ownRaftPhys_msgs
    finish_none
  · -- (d) `MsgAppResp`: stamped, and a response, so onto `r.msgsAfterAppend`; it may
    -- be self-addressed (`appendEntry` does exactly that).
    obtain ⟨mty, mto, mfrom, mterm, mlt, midx, ments, mcommit, mvote, msnap, mrej, mrh, mctx,
      mresp⟩ := m
    simp only [MsgAppResp] at HAR Hmterm ⊢
    subst HAR Hmterm
    simp only at Hself2
    wp_auto
    wp_apply raft.wp_load_Term $$ Hphys as Hphys
    have Hty : mtypeOf (W32 4) = some MsgType.appResp := rfl
    send_tail ownRaftPhys_msgsAA
    ihave Hphys := Hback $$ %q' %_ %(some (absMsg .appResp _ ents ctx)) Hf Hq Hq_cap [] [] []
    · unfold msgAbs
      iright; ileft
      iexists .appResp, ents, ctx
      iframe Hents Hctx
      ipureintro
      exact ⟨Hty, by decide, rfl⟩
    · -- stamped `From: id`, `Term: r.Term`; a self-addressed one as `AAMsgOk` asks
      ipureintro
      refine ⟨by simp [MsgAppResp], rfl, fun Hto => ?_⟩
      obtain ⟨He, Hc, Hnz, Hrj⟩ := Hself2 Hto
      exact ⟨Hnz, He, Hc, fun _ => Hrj, by simp only; split <;> omega⟩
    · ipureintro; out_term
    iapply ownRaftPhys_eq _ _ _ _ _ ?_ $$ Hphys
    rfl
  · -- (e) a forwarded proposal: `Term` stays zero; not a response
    obtain ⟨mty, mto, mfrom, mterm, mlt, midx, ments, mcommit, mvote, msnap, mrej, mrh, mctx,
      mresp⟩ := m
    simp only [MsgProp] at HProp Hmterm Hself ⊢
    subst HProp Hmterm
    wp_auto
    wp_apply raft.wp_load_id $$ Hphys as Hphys
    rw [decide_eq_false Hself]
    wp_auto
    send_tail ownRaftPhys_msgs
    ihave Hphys := Hback $$ %q' %_ %(some (absMsg .propose _ ents ctx)) Hf Hq Hq_cap [] []
    · unfold msgAbs
      iright; ileft
      iexists .propose, ents, ctx
      iframe Hents Hctx
      ipureintro
      exact ⟨rfl, by decide, rfl⟩
    · ipureintro; out_term
    iapply ownRaftPhys_eq _ _ _ _ _ ?_ $$ Hphys
    rfl

end proof

end EtcdGrove
end Perennial
