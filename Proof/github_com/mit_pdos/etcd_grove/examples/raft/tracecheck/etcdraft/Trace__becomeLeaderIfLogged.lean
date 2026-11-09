/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `Trace__becomeLeaderIfLogged`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__becomeLeaderIfLogged
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__loglineIsNodeEvent
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__logline
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__validatePostStates
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__BecomeLeader

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

theorem Trace.becomeLeaderIfLogged.wp_proof
    (wp_loglineIsNodeEvent : Trace.loglineIsNodeEvent.spec (GF := GF) (hG := hG))
    (wp_logline : Trace.logline.spec (GF := GF) (hG := hG))
    (wp_validatePostStates : Trace.validatePostStates.spec (GF := GF) (hG := hG))
    (wp_BecomeLeader : State.BecomeLeader.spec (GF := GF) (hG := hG)) :
    Trace.becomeLeaderIfLogged.spec (GF := GF) (hG := hG) := by
  intro t tr g ts i
  wp_start as ⟨#Ht, #Hts, %Hl1, %Hi, %Hvg⟩
  ihave HΦ' : (∀ out sts, ⌜sts = tr.becomeLeaderIfLogged ts (uint.nat i)⌝ -∗ statesOut out sts -∗ Φ #out) $$ [HΦ]
  · iintro %out %sts %hs Hout; rw [hs]; iapply HΦ $$ Hout
  open_ts
  wp_auto
  wp_apply wp_loglineIsNodeEvent t tr g ts go!"BecomeLeader" "BecomeLeader" i $$ [Ht Hts]
  · iframe Ht Hts; ipureintro; exact ⟨by strRel_lit, Hl1⟩
  cases hne : tr.isNodeEvent ts "BecomeLeader" (uint.nat i)
  · simp only [Bool.not_false]
    wp_auto
    ihave Hn : statesOut (GF := GF) slice.nil [] $$ []
    · iapply statesOut_nil
    iapply HΦ' $$ [] Hn
    ipureintro; simp [Trace.becomeLeaderIfLogged, hne]
  have hle : ts.l ≤ tr.len := by
    unfold Trace.isNodeEvent Trace.isEvent at hne; simp at hne; exact hne.1.1
  simp only [Bool.not_true]
  wp_auto
  wp_apply wp_BecomeLeader g.S' ts.s i $$ [Hst] as %q Hsq
  · iframe Hst; ipureintro; exact ⟨Hi, Hvg⟩
  cases hb : ts.s.becomeLeader (uint.nat i) with
  | none =>
    icases Hsq with %Hsq
    subst Hsq
    wp_auto
    ihave Hn : statesOut (GF := GF) slice.nil [] $$ []
    · iapply statesOut_nil
    iapply HΦ' $$ [] Hn
    ipureintro; simp [Trace.becomeLeaderIfLogged, hne, hb]
  | some s2 =>
  icases Hsq with #Hsq
  ihave %Hqnn := stateRO_not_null $$ Hsq
  rw [decide_eq_false Hqnn]
  wp_auto
  wp_apply wp_validatePostStates t tr g ts q s2 i $$ [Ht Hts Hsq]
  · iframe Ht Hts Hsq; ipureintro; exact ⟨Hl1, hle⟩
  cases hv : tr.validatePostStates ts s2 (uint.nat i)
  · simp only [Bool.not_false]
    wp_auto
    ihave Hn : statesOut (GF := GF) slice.nil [] $$ []
    · iapply statesOut_nil
    iapply HΦ' $$ [] Hn
    ipureintro; simp [Trace.becomeLeaderIfLogged, hne, hb, hv]
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
    simp only [Bool.not_false]
    wp_auto
    ihave Hn : statesOut (GF := GF) slice.nil [] $$ []
    · iapply statesOut_nil
    iapply HΦ' $$ [] Hn
    ipureintro; simp [Trace.becomeLeaderIfLogged, hne, hb, hv, hr]
  rw [decide_eq_true hr]
  simp only [Bool.not_true]
  wp_auto
  -- server `i` of the successor (a server of it: the successor matched the line)
  have Hi2 : uint.nat i ∈ s2.server := by
    unfold Trace.validatePostStates Line.stateMatches at hv
    simp only [Bool.and_eq_true, List.contains_iff_mem] at hv
    exact hv.1.1.1.1.1.1.1
  ihave #Hq0 := Hsq
  iunfold stateRO at Hq0
  icases Hq0 with ⟨%g2, %sm2, #Hp2, #Hsrv2, #Hm2, %Hkeys2, %Hnd2, #Hsrvs2, -, -, -⟩
  icases typedPointsto_split _ _ _ $$ Hp2 with Hpf2
  simp only [TypedPointsto.typedPointstoDef]
  icases Hpf2 with ⟨-, #S2, -⟩
  wp_auto
  icases servers_at s2 sm2 i Hi2 $$ Hsrvs2 with ⟨%qv, %Hqv, #Hsv⟩
  wp_apply wp_map_lookup1 $$ [Hm2] as -
  · iexact Hm2
  rw [Hqv]
  simp only [Option.getD_some]
  iunfold serverRO at Hsv
  icases Hsv with ⟨%gv, %mv, #Hqv', %Hfv, -⟩
  icases typedPointsto_split _ _ _ $$ Hqv' with Hqvf
  simp only [TypedPointsto.typedPointstoDef]
  icases Hqvf with ⟨-, #SV2, -⟩
  wp_auto
  rw [decide_strRel Hfv.2.1 strRel_leader]
  by_cases hl : (s2.s (uint.nat i)).state = leader
  rotate_left
  · rw [decide_eq_false hl]
    simp only [Bool.not_false]
    wp_auto
    ihave Hn : statesOut (GF := GF) slice.nil [] $$ []
    · iapply statesOut_nil
    iapply HΦ' $$ [] Hn
    ipureintro; simp [Trace.becomeLeaderIfLogged, hne, hb, hv, hr, hl]
  rw [decide_eq_true hl]
  simp only [Bool.not_true]
  wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl0 ⟨Hsl0, Hcap0⟩
  wp_auto
  ihave Hout := statesOut_single _ q s2 $$ [Hsl0 Hcap0]
  · isplitl [Hsl0]
    · iexact Hsl0
    isplitl [Hcap0]
    · iexact Hcap0
    iexact Hsq
  iapply HΦ' $$ [] Hout
  ipureintro; simp [Trace.becomeLeaderIfLogged, hne, hb, hv, hr, hl]

end proof

end Etcdraft
end EtcdGrove
end Perennial
