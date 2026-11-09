/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `Trace__validatePreStates`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__validatePreStates
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__logline
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.line__stateMatches

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

theorem Trace.validatePreStates.wp_proof (wp_logline : Trace.logline.spec (GF := GF) (hG := hG))
    (wp_stateMatches : line.stateMatches.spec (GF := GF) (hG := hG)) :
    Trace.validatePreStates.spec (GF := GF) (hG := hG) := by
  intro t tr g ts i
  wp_start as ⟨#Ht, #Hts, %Hl1, %Hl2⟩
  open_ts
  wp_auto
  have hl : sint.Z (g.L' - W64 1) = ((ts.l - 1 : Nat) : Int) := by
    have h1 : (1 : Int) ≤ sint.Z g.L' := by rw [Hg.1]; exact_mod_cast Hl1
    have : ((ts.l - 1 : Nat) : Int) = (ts.l : Int) - 1 := by omega
    rw [this, ← Hg.1]; word
  rw [sint_decide_nat Hg.2 hl]
  by_cases hp : ts.pl = ts.l - 1
  · rw [decide_eq_true hp]
    wp_auto
    wp_apply wp_logline t tr g ts $$ [Ht Hts] as %q #Hlp
    · iframe Ht Hts; ipureintro; exact ⟨Hl1, Hl2⟩
    wp_apply wp_stateMatches q (tr.line ts.l) g.S' ts.s i $$ [Hlp Hst]
    · iframe Hlp Hst
    try wp_auto
    have : tr.validatePreStates ts (uint.nat i) = (tr.line ts.l).stateMatches ts.s (uint.nat i) := by
      simp [Trace.validatePreStates, hp]
    rw [this]
    iapply HΦ; ipureintro; trivial
  · rw [decide_eq_false hp]
    wp_auto
    have : tr.validatePreStates ts (uint.nat i) = true := by simp [Trace.validatePreStates, hp]
    rw [this]
    iapply HΦ; ipureintro; trivial

end proof

end Etcdraft
end EtcdGrove
end Perennial
