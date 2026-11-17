/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `isMessageEvent`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.isMessageEvent

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

theorem isMessageEvent.wp_proof : isMessageEvent.spec (GF := GF) (hG := hG) := by
  intro name s
  wp_start as %Hs
  ihave #Hpi := etcdraftInit_get $$ Hpkg
  icases Hpi with ⟨-, -, ⟨%mr, #Hmr, #Hrnm⟩⟩
  wp_auto
  wp_apply wp_map_lookup1 $$ [Hrnm] as -
  · iexact Hrnm
  rw [show (zero_val Bool) = false from rfl, receiveNamesMap_lookup Hs]
  cases hr : isReceiveName s
  · wp_auto
    rw [decide_strRel Hs (show strRel go!"SendAppendEntriesRequest" "SendAppendEntriesRequest" by strRel_lit)]
    by_cases h1 : s = "SendAppendEntriesRequest"
    · rw [decide_eq_true h1]; wp_auto
      have : isMessageEvent s = true := by subst h1; rfl
      rw [this]; iapply HΦ; ipureintro; trivial
    rw [decide_eq_false h1]; wp_auto
    rw [decide_strRel Hs (show strRel go!"SendAppendEntriesResponse" "SendAppendEntriesResponse" by strRel_lit)]
    by_cases h2 : s = "SendAppendEntriesResponse"
    · rw [decide_eq_true h2]; wp_auto
      have : isMessageEvent s = true := by subst h2; rfl
      rw [this]; iapply HΦ; ipureintro; trivial
    rw [decide_eq_false h2]; wp_auto
    rw [decide_strRel Hs (show strRel go!"SendRequestVoteRequest" "SendRequestVoteRequest" by strRel_lit)]
    by_cases h3 : s = "SendRequestVoteRequest"
    · rw [decide_eq_true h3]; wp_auto
      have : isMessageEvent s = true := by subst h3; rfl
      rw [this]; iapply HΦ; ipureintro; trivial
    rw [decide_eq_false h3]; wp_auto
    rw [decide_strRel Hs (show strRel go!"SendRequestVoteResponse" "SendRequestVoteResponse" by strRel_lit)]
    by_cases h4 : s = "SendRequestVoteResponse"
    · rw [decide_eq_true h4]; wp_auto
      have : isMessageEvent s = true := by subst h4; rfl
      rw [this]; iapply HΦ; ipureintro; trivial
    rw [decide_eq_false h4]; wp_auto
    rw [decide_strRel Hs (show strRel go!"IgnoreRequestVoteRequest" "IgnoreRequestVoteRequest" by strRel_lit)]
    have : isMessageEvent s = decide (s = "IgnoreRequestVoteRequest") := by
      unfold isMessageEvent
      rw [hr]
      simp only [Bool.false_or, beq_eq_false_iff_ne.2 h1, beq_eq_false_iff_ne.2 h2, beq_eq_false_iff_ne.2 h3,
        beq_eq_false_iff_ne.2 h4]
      rfl
    rw [this]
    iapply HΦ; ipureintro; trivial
  · wp_auto
    have : isMessageEvent s = true := by unfold isMessageEvent; rw [hr]; rfl
    rw [this]
    iapply HΦ; ipureintro; trivial

end proof

end Etcdraft
end EtcdGrove
end Perennial
