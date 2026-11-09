/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `Trace__preTimeoutIfLogged`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__preTimeoutIfLogged
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__loglineIsNodeEvent
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__validatePostStates
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__PreTimeout

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

theorem Trace.preTimeoutIfLogged.wp_proof
    (wp_loglineIsNodeEvent : Trace.loglineIsNodeEvent.spec (GF := GF) (hG := hG))
    (wp_validatePostStates : Trace.validatePostStates.spec (GF := GF) (hG := hG))
    (wp_PreTimeout : State.PreTimeout.spec (GF := GF) (hG := hG)) :
    Trace.preTimeoutIfLogged.spec (GF := GF) (hG := hG) := by
  intro t tr g ts i
  wp_start as ⟨#Ht, #Hts, %Hl1, %Hi, %Hpv⟩
  ihave HΦ' : (∀ out sts, ⌜sts = tr.preTimeoutIfLogged ts (uint.nat i)⌝ -∗ statesOut out sts -∗ Φ #out) $$ [HΦ]
  · iintro %out %sts %hs Hout; rw [hs]; iapply HΦ $$ Hout
  open_ts
  wp_auto
  wp_apply wp_loglineIsNodeEvent t tr g ts go!"BecomePreCandidate" "BecomePreCandidate" i $$ [Ht Hts]
  · iframe Ht Hts; ipureintro; exact ⟨by strRel_lit, Hl1⟩
  cases hne : tr.isNodeEvent ts "BecomePreCandidate" (uint.nat i)
  · ret_nil [Trace.preTimeoutIfLogged, hne]
  have hle : ts.l ≤ tr.len := Trace.isNodeEvent_le hne
  simp only [Bool.not_true]
  wp_auto
  wp_apply wp_PreTimeout g.S' ts.s i $$ [Hst] as %q Hsq
  · iframe Hst; ipureintro; exact ⟨Hi, Hpv⟩
  cases hb : ts.s.preTimeout (uint.nat i) with
  | none =>
    icases Hsq with %Hsq
    subst Hsq
    ret_nil [Trace.preTimeoutIfLogged, hne, hb]
  | some s2 =>
  icases Hsq with #Hsq
  ihave %Hqnn := stateRO_not_null $$ Hsq
  rw [decide_eq_false Hqnn]
  wp_auto
  wp_apply wp_validatePostStates t tr g ts q s2 i $$ [Ht Hts Hsq]
  · iframe Ht Hts Hsq; ipureintro; exact ⟨Hl1, hle⟩
  cases hv : tr.validatePostStates ts s2 (uint.nat i)
  · ret_nil [Trace.preTimeoutIfLogged, hne, hb, hv]
  ret_single q, s2, Hsq [Trace.preTimeoutIfLogged, hne, hb, hv]

end proof

end Etcdraft
end EtcdGrove
end Perennial
