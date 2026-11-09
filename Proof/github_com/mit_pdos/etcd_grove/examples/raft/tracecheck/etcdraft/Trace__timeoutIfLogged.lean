/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `Trace__timeoutIfLogged`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__timeoutIfLogged
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__loglineIsNodeEvent
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__logline
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__Timeout

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

theorem Trace.timeoutIfLogged.wp_proof
    (wp_loglineIsNodeEvent : Trace.loglineIsNodeEvent.spec (GF := GF) (hG := hG))
    (wp_logline : Trace.logline.spec (GF := GF) (hG := hG))
    (wp_Timeout : State.Timeout.spec (GF := GF) (hG := hG)) :
    Trace.timeoutIfLogged.spec (GF := GF) (hG := hG) := by
  intro t tr g ts i
  wp_start as ⟨#Ht, #Hts, %Hl1, %Hi, %Hterm, %Hvg⟩
  ihave HΦ' : (∀ out sts, ⌜sts = tr.timeoutIfLogged ts (uint.nat i)⌝ -∗ statesOut out sts -∗ Φ #out) $$ [HΦ]
  · iintro %out %sts %hs Hout; rw [hs]; iapply HΦ $$ Hout
  open_ts
  wp_auto
  wp_apply wp_loglineIsNodeEvent t tr g ts go!"BecomeCandidate" "BecomeCandidate" i $$ [Ht Hts]
  · iframe Ht Hts; ipureintro; exact ⟨by strRel_lit, Hl1⟩
  cases hne : tr.isNodeEvent ts "BecomeCandidate" (uint.nat i)
  · ret_nil [Trace.timeoutIfLogged, hne]
  have hle : ts.l ≤ tr.len := by
    unfold Trace.isNodeEvent Trace.isEvent at hne; simp at hne; exact hne.1.1
  simp only [Bool.not_true]
  wp_auto
  wp_apply wp_Timeout g.S' ts.s i $$ [Hst] as %q Hsq
  · iframe Hst; ipureintro; exact ⟨Hi, Hterm, Hvg⟩
  try wp_auto
  wp_apply wp_logline t tr g ts $$ [Ht Hts] as %ql #Hlp
  · iframe Ht Hts; ipureintro; exact ⟨Hl1, hle⟩
  cases hb : ts.s.timeout (uint.nat i) with
  | none =>
    icases Hsq with %Hsq
    subst Hsq
    ret_nil [Trace.timeoutIfLogged, hne, hb]
  | some s2 =>
  icases Hsq with #Hsq
  ihave %Hqnn := stateRO_not_null $$ Hsq
  rw [decide_eq_false Hqnn]
  open_lineP
  simp only [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Candidate]
  wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Role.TypeAssumptions.String_unfold.method_unfold]
  wp_auto
  rw [decide_strRel Hef.2.2.2.2.2.1 strRel_candidate]
  by_cases hr : (tr.line ts.l).ev.role = candidate
  rotate_left
  · rw [decide_eq_false hr]
    ret_nil [Trace.timeoutIfLogged, hne, hb, hr]
  rw [decide_eq_true hr]
  simp only [Bool.not_true]
  wp_auto
  rw [uint_decide Hlf.1 rfl]
  by_cases hn : (tr.line ts.l).nid = uint.nat i
  rotate_left
  · rw [decide_eq_false hn]
    ret_nil [Trace.timeoutIfLogged, hne, hb, hr, hn]
  rw [decide_eq_true hn]
  simp only [Bool.not_true]
  wp_auto
  -- server `i` of the successor (`Timeout` keeps the servers)
  have Hi2 : uint.nat i ∈ s2.server := by
    unfold State.timeout at hb
    split at hb
    · cases hb; exact Hi
    · cases hb
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
  icases Hqvf with ⟨#CT2, #SV2, -⟩
  wp_auto
  rw [decide_strRel Hfv.2.1 strRel_candidate]
  by_cases hc : (s2.s (uint.nat i)).state = candidate
  rotate_left
  · rw [decide_eq_false hc]
    ret_nil [Trace.timeoutIfLogged, hne, hb, hr, hn, hc]
  rw [decide_eq_true hc]
  simp only [Bool.not_true]
  wp_auto
  wp_apply wp_map_lookup1 $$ [Hm2] as -
  · iexact Hm2
  rw [Hqv]
  simp only [Option.getD_some]
  icases typedPointsto_split _ _ _ $$ State with Hesf
  simp only [TypedPointsto.typedPointstoDef]
  icases Hesf with ⟨#ES1, -⟩
  wp_auto
  rw [sint_decide Hfv.1 Hef.2.2.1]
  by_cases ht : (s2.s (uint.nat i)).currentTerm = (tr.line ts.l).ev.state.term
  rotate_left
  · rw [decide_eq_false ht]
    ret_nil [Trace.timeoutIfLogged, hne, hb, hr, hn, hc, ht]
  rw [decide_eq_true ht]
  ret_single q, s2, Hsq [Trace.timeoutIfLogged, hne, hb, hr, hn, hc, ht]

end proof

end Etcdraft
end EtcdGrove
end Perennial
