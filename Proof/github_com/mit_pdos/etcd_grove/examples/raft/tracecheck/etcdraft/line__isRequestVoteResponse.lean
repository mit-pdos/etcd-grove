/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `line__isRequestVoteResponse`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.line__isRequestVoteResponse
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.line__msgType

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

-- After the type check (`hT`): the line's message, its type in the table, the comparisons.
set_option hygiene false in
local macro "rvresp_tail" : tactic => `(tactic| (
  cases hm : x.ev.msg with
  | none =>
    simp only [Option.bind_none, Option.isSome_none, Bool.not_false]
    wp_auto
    iapply HΦ'; ipureintro; simp [Line.isRequestVoteResponse, hm]
  | some ev =>
    simp only [Option.bind_some]
    icases Hemsg with ⟨%gev, #Hgev, %Hem⟩
    icases typedPointsto_split _ _ _ $$ Hgev with Hgevf
    simp only [TypedPointsto.typedPointstoDef]
    iNamed Hgevf
    cases ho : raftMsgType ev.type with
    | none =>
      simp only [Option.isSome_none, Bool.not_false]
      wp_auto
      iapply HΦ'; ipureintro; simp [Line.isRequestVoteResponse, hm, ho]
    | some ty =>
      simp only [Option.isSome_some, Bool.not_true, Option.map_some, Option.getD_some]
      wp_auto
      rw [msgTypeW_decide Hv.1 ty]
      by_cases hty : m.type = ty
      rotate_left
      · rw [decide_eq_false hty]
        wp_auto
        iapply HΦ'; ipureintro; simp [Line.isRequestVoteResponse, hm, ho, Ne.symm hty]
      rw [decide_eq_true hty]
      wp_auto
      rw [decide_eq_decide.2 (uint_eq_iff _ _ _ _ Hv.2.2.2.2.2.2.2.2.2.2.2.2 Hlf.2.2.2.2)]
      by_cases h1 : m.dest = x.to
      rotate_left
      · rw [decide_eq_false h1]
        wp_auto
        iapply HΦ'; ipureintro; simp [Line.isRequestVoteResponse, hm, ho, hty, h1]
      rw [decide_eq_true h1]
      wp_auto
      rw [decide_eq_decide.2 (uint_eq_iff _ _ _ _ Hv.2.2.2.2.2.2.2.2.2.2.2.1 Hlf.2.2.2.1)]
      by_cases h2 : m.source = x.from
      rotate_left
      · rw [decide_eq_false h2]
        wp_auto
        iapply HΦ'; ipureintro; simp [Line.isRequestVoteResponse, hm, ho, hty, h1, h2]
      rw [decide_eq_true h2]
      wp_auto
      rw [decide_eq_decide.2 (sint_eq_iff _ _ _ _ Hv.2.2.1 Hem.2.1)]
      by_cases h3 : m.term = ev.term
      rotate_left
      · rw [decide_eq_false h3]
        wp_auto
        iapply HΦ'; ipureintro; simp [Line.isRequestVoteResponse, hm, ho, hty, h1, h2, h3]
      rw [decide_eq_true h3]
      wp_auto
      rw [Hv.2.2.2.2.2.1, Hem.2.2.2.2.2.2.2.2.2.1]
      iapply HΦ'; ipureintro
      subst hty
      simp only [Line.isRequestVoteResponse, hm, ho, h1, h2, h3, hT, beq_self_eq_true, Bool.true_and,
        Bool.and_true]
      cases m.voteGranted <;> cases ev.reject <;> rfl))

theorem line.isRequestVoteResponse.wp_proof (wp_msgType : line.msgType.spec (GF := GF) (hG := hG)) :
    line.isRequestVoteResponse.spec (GF := GF) (hG := hG) := by
  intro q x p m
  wp_start as ⟨#Hlp, #Hmsg⟩
  ihave HΦ' : (∀ b : Bool, ⌜b = x.isRequestVoteResponse m⌝ -∗ Φ #b) $$ [HΦ]
  · iintro %b %hb; rw [hb]; iapply HΦ; ipureintro; trivial
  read_msg
  wp_auto
  wp_apply wp_msgType q x $$ [Hlp]
  · iframe Hlp
  open_lineP
  try wp_auto
  rw [show decide (gm.Type' = W8 1) = decide (m.type = .requestVoteResponse) from
    msgTypeW_decide Hv.1 .requestVoteResponse]
  by_cases hA : m.type = .requestVoteResponse
  · rw [decide_eq_true hA]
    have hT : ((m.type == MsgType.requestVoteResponse) || (m.type == MsgType.preVoteResponse)) = true := by simp [hA]
    wp_auto
    rvresp_tail
  rw [decide_eq_false hA]
  wp_auto
  rw [show decide (gm.Type' = W8 5) = decide (m.type = .preVoteResponse) from
    msgTypeW_decide Hv.1 .preVoteResponse]
  by_cases hB : m.type = .preVoteResponse
  · rw [decide_eq_true hB]
    have hT : ((m.type == MsgType.requestVoteResponse) || (m.type == MsgType.preVoteResponse)) = true := by simp [hB]
    wp_auto
    rvresp_tail
  rw [decide_eq_false hB]
  wp_auto
  iapply HΦ'; ipureintro
  cases hm : x.ev.msg <;> simp [Line.isRequestVoteResponse, hm, hA, hB]

end proof

end Etcdraft
end EtcdGrove
end Perennial
