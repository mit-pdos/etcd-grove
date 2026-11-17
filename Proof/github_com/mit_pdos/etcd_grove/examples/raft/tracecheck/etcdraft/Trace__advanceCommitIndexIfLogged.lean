/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `Trace__advanceCommitIndexIfLogged`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__advanceCommitIndexIfLogged
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__loglineIsNodeEvent
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__logline
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__validatePostStates
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__AdvanceCommitIndex

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

theorem Trace.advanceCommitIndexIfLogged.wp_proof
    (wp_loglineIsNodeEvent : Trace.loglineIsNodeEvent.spec (GF := GF) (hG := hG))
    (wp_logline : Trace.logline.spec (GF := GF) (hG := hG))
    (wp_validatePostStates : Trace.validatePostStates.spec (GF := GF) (hG := hG))
    (wp_AdvanceCommitIndex : State.AdvanceCommitIndex.spec (GF := GF) (hG := hG)) :
    Trace.advanceCommitIndexIfLogged.spec (GF := GF) (hG := hG) := by
  intro t tr g ts i
  wp_start as ⟨#Ht, #Hts, %Hl1, %Hi, %Hcfg, %Hlog⟩
  ihave HΦ' : (∀ out sts, ⌜sts = tr.advanceCommitIndexIfLogged ts (uint.nat i)⌝ -∗ statesOut out sts -∗ Φ #out) $$ [HΦ]
  · iintro %out %sts %hs Hout; rw [hs]; iapply HΦ $$ Hout
  open_ts
  wp_auto
  wp_apply wp_loglineIsNodeEvent t tr g ts go!"Commit" "Commit" i $$ [Ht Hts]
  · iframe Ht Hts; ipureintro; exact ⟨by strRel_lit, Hl1⟩
  cases hne : tr.isNodeEvent ts "Commit" (uint.nat i)
  · ret_nil [Trace.advanceCommitIndexIfLogged, hne]
  have hle : ts.l ≤ tr.len := by
    unfold Trace.isNodeEvent Trace.isEvent at hne; simp at hne; exact hne.1.1
  simp only [Bool.not_true]
  wp_auto
  wp_apply wp_AdvanceCommitIndex g.S' ts.s i $$ [Hst] as %q Hsq
  · iframe Hst; ipureintro; exact ⟨Hi, Hcfg, Hlog⟩
  cases hb : ts.s.advanceCommitIndex (uint.nat i) with
  | none =>
    icases Hsq with %Hsq
    subst Hsq
    ret_nil [Trace.advanceCommitIndexIfLogged, hne, hb]
  | some s2 =>
  icases Hsq with #Hsq
  ihave %Hqnn := stateRO_not_null $$ Hsq
  rw [decide_eq_false Hqnn]
  wp_auto
  wp_apply wp_validatePostStates t tr g ts q s2 i $$ [Ht Hts Hsq]
  · iframe Ht Hts Hsq; ipureintro; exact ⟨Hl1, hle⟩
  cases hv : tr.validatePostStates ts s2 (uint.nat i)
  · ret_nil [Trace.advanceCommitIndexIfLogged, hne, hb, hv]
  simp only [Bool.not_true]
  wp_auto
  wp_apply wp_logline t tr g ts $$ [Ht Hts] as %ql #Hlp
  · iframe Ht Hts; ipureintro; exact ⟨Hl1, hle⟩
  open_lineP
  simp only [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Leader]
  wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Role.TypeAssumptions.String_unfold.method_unfold]
  wp_auto
  rw [decide_strRel Hef.2.2.2.2.2.1 strRel_leader]
  by_cases hr : (tr.line ts.l).ev.role = leader
  rotate_left
  · rw [decide_eq_false hr]
    ret_nil [Trace.advanceCommitIndexIfLogged, hne, hb, hv, hr]
  rw [decide_eq_true hr]
  simp only [Bool.not_true]
  wp_auto
  -- server `i` of the state before
  ihave #Hq0 := Hst
  iunfold stateRO at Hq0
  icases Hq0 with ⟨%g1, %sm1, #Hp1, #Hsrv1, #Hm1, %Hkeys1, %Hnd1, #Hsrvs1, -, -, -⟩
  icases typedPointsto_split _ _ _ $$ Hp1 with Hpf1
  simp only [TypedPointsto.typedPointstoDef]
  icases Hpf1 with ⟨-, #S1, -⟩
  wp_auto
  icases servers_at ts.s sm1 i Hi $$ Hsrvs1 with ⟨%qv, %Hqv, #Hsv⟩
  wp_apply wp_map_lookup1 $$ [Hm1] as -
  · iexact Hm1
  rw [Hqv]
  simp only [Option.getD_some]
  iunfold serverRO at Hsv
  icases Hsv with ⟨%gv, %mv, #Hqv', %Hfv, -⟩
  icases typedPointsto_split _ _ _ $$ Hqv' with Hqvf
  simp only [TypedPointsto.typedPointstoDef]
  icases Hqvf with ⟨-, #SV1, -⟩
  wp_auto
  rw [decide_strRel Hfv.2.1 strRel_leader]
  by_cases hl : (ts.s.s (uint.nat i)).state = leader
  rotate_left
  · rw [decide_eq_false hl]
    ret_nil [Trace.advanceCommitIndexIfLogged, hne, hb, hv, hr, hl]
  rw [decide_eq_true hl]
  ret_single q, s2, Hsq [Trace.advanceCommitIndexIfLogged, hne, hb, hv, hr, hl]

end proof

end Etcdraft
end EtcdGrove
end Perennial
