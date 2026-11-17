/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `line__isAppendEntriesResponse`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.line__isAppendEntriesResponse
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

theorem line.isAppendEntriesResponse.wp_proof (wp_msgType : line.msgType.spec (GF := GF) (hG := hG)) :
    line.isAppendEntriesResponse.spec (GF := GF) (hG := hG) := by
  intro q x p m
  wp_start as ⟨#Hlp, #Hmsg⟩
  ihave HΦ' : (∀ b : Bool, ⌜b = x.isAppendEntriesResponse m⌝ -∗ Φ #b) $$ [HΦ]
  · iintro %b %hb; rw [hb]; iapply HΦ; ipureintro; trivial
  ihave #Hinit := etcdraftInit_get $$ Hpkg
  icases Hinit with ⟨-, ⟨%msub, #Hmsub, #Hmsubm⟩, -⟩
  read_msg
  wp_auto
  wp_apply wp_msgType q x $$ [Hlp]
  · iframe Hlp
  open_lineP
  try wp_auto
  rw [show decide (gm.Type' = W8 3) = decide (m.type = .appendEntriesResponse) from
    msgTypeW_decide Hv.1 .appendEntriesResponse]
  by_cases hA : m.type = .appendEntriesResponse
  rotate_left
  · rw [decide_eq_false hA]
    wp_auto
    iapply HΦ'; ipureintro
    cases hm : x.ev.msg <;> simp [Line.isAppendEntriesResponse, hm, hA]
  rw [decide_eq_true hA]
  wp_auto
  cases hm : x.ev.msg with
  | none =>
    simp only [Option.bind_none, Option.isSome_none, Bool.not_false]
    wp_auto
    iapply HΦ'; ipureintro; simp [Line.isAppendEntriesResponse, hm]
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
    iapply HΦ'; ipureintro; simp [Line.isAppendEntriesResponse, hm, ho]
  | some ty =>
  simp only [Option.isSome_some, Bool.not_true, Option.map_some, Option.getD_some]
  wp_auto
  rw [msgTypeW_decide Hv.1 ty]
  by_cases hty : m.type = ty
  rotate_left
  · rw [decide_eq_false hty]
    wp_auto
    iapply HΦ'; ipureintro; simp [Line.isAppendEntriesResponse, hm, ho, Ne.symm hty]
  rw [decide_eq_true hty]
  subst hty
  wp_auto
  -- the subtype
  wp_apply wp_map_lookup2 $$ [Hmsubm] as -
  · iexact Hmsubm
  obtain ⟨hsome, hrel⟩ := raftMsgSubtypeMap_lookup Hem.1
  cases hs : raftMsgSubtype ev.type with
  | none =>
    rw [hs] at hsome
    have : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.raftMsgSubtypeMap !! gev.Type' = none := by
      cases h : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.raftMsgSubtypeMap !! gev.Type' <;> simp_all
    rw [this]
    wp_auto
    iapply HΦ'; ipureintro; simp [Line.isAppendEntriesResponse, hm, ho, hs]
  | some st =>
  obtain ⟨gsub, hgsub⟩ : ∃ g, github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.raftMsgSubtypeMap !! gev.Type' = some g := by
    rw [hs] at hsome; cases h : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.raftMsgSubtypeMap !! gev.Type' <;> simp_all
  have hgst := hrel gsub st hgsub hs
  rw [hgsub]
  simp only [Option.getD_some, Option.isSome_some, _root_.decide_true, Bool.not_true]
  wp_auto
  rw [decide_strRel Hv.2.1 hgst]
  by_cases hsub : m.subtype = st
  rotate_left
  · rw [decide_eq_false hsub]
    wp_auto
    iapply HΦ'; ipureintro; simp [Line.isAppendEntriesResponse, hm, ho, hs, Ne.symm hsub]
  rw [decide_eq_true hsub]
  subst hsub
  wp_auto
  rw [decide_eq_decide.2 (uint_eq_iff _ _ _ _ Hv.2.2.2.2.2.2.2.2.2.2.2.2 Hlf.2.2.2.2)]
  by_cases h1 : m.dest = x.to
  rotate_left
  · rw [decide_eq_false h1]
    wp_auto
    iapply HΦ'; ipureintro; simp [Line.isAppendEntriesResponse, hm, ho, hs, h1]
  rw [decide_eq_true h1]
  wp_auto
  rw [decide_eq_decide.2 (uint_eq_iff _ _ _ _ Hv.2.2.2.2.2.2.2.2.2.2.2.1 Hlf.2.2.2.1)]
  by_cases h2 : m.source = x.from
  rotate_left
  · rw [decide_eq_false h2]
    wp_auto
    iapply HΦ'; ipureintro; simp [Line.isAppendEntriesResponse, hm, ho, hs, h1, h2]
  rw [decide_eq_true h2]
  wp_auto
  rw [decide_eq_decide.2 (sint_eq_iff _ _ _ _ Hv.2.2.1 Hem.2.1)]
  by_cases h3 : m.term = ev.term
  rotate_left
  · rw [decide_eq_false h3]
    wp_auto
    iapply HΦ'; ipureintro; simp [Line.isAppendEntriesResponse, hm, ho, hs, h1, h2, h3]
  rw [decide_eq_true h3]
  wp_auto
  rw [Hv.2.2.2.2.2.2.2.2.2.1, Hem.2.2.2.2.2.2.2.2.2.1]
  by_cases h5 : m.success = !ev.reject
  rotate_left
  · rw [decide_eq_false h5]
    wp_auto
    iapply HΦ'; ipureintro
    simp only [Line.isAppendEntriesResponse, hm, ho, hs, h1, h2, h3, hA, beq_self_eq_true, Bool.true_and]
    cases hsc : m.success <;> cases hr : ev.reject <;> simp_all
  rw [decide_eq_true h5]
  wp_auto
  cases hr : ev.reject
  · simp only [Bool.not_false]
    wp_auto
    rw [decide_strRel Hv.2.1 strRel_heartbeat]
    by_cases hh : m.subtype = "heartbeat"
    · rw [decide_eq_true hh]
      wp_auto
      iapply HΦ'; ipureintro
      simp [Line.isAppendEntriesResponse, hm, ho, hs, h1, h2, h3, hA, hr, h5, hh]
    rw [decide_eq_false hh]
    wp_auto
    rw [decide_eq_decide.2 (sint_eq_iff _ _ _ _ Hv.2.2.2.2.2.2.2.2.2.2.1 Hem.2.2.2.2.2.2.1)]
    by_cases h6 : m.matchIndex = ev.index
    · rw [decide_eq_true h6]
      wp_auto
      iapply HΦ'; ipureintro
      simp [Line.isAppendEntriesResponse, hm, ho, hs, h1, h2, h3, hA, hr, h5, h6]
    · rw [decide_eq_false h6]
      wp_auto
      iapply HΦ'; ipureintro
      simp [Line.isAppendEntriesResponse, hm, ho, hs, h1, h2, h3, hA, hr, h5, hh, h6]
  · simp only [Bool.not_true]
    wp_auto
    iapply HΦ'; ipureintro
    simp [Line.isAppendEntriesResponse, hm, ho, hs, h1, h2, h3, hA, hr, h5]

end proof

end Etcdraft
end EtcdGrove
end Perennial
