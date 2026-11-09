/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `Trace__appendEntriesToSelfIfLogged`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__appendEntriesToSelfIfLogged
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__loglineIsMessageEvent
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__logline
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__validatePostStates
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__AppendEntriesToSelf
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.newPending
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.line__isAppendEntriesResponse

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

theorem Trace.appendEntriesToSelfIfLogged.wp_proof
    (wp_loglineIsMessageEvent : Trace.loglineIsMessageEvent.spec (GF := GF) (hG := hG))
    (wp_logline : Trace.logline.spec (GF := GF) (hG := hG))
    (wp_validatePostStates : Trace.validatePostStates.spec (GF := GF) (hG := hG))
    (wp_AppendEntriesToSelf : State.AppendEntriesToSelf.spec (GF := GF) (hG := hG))
    (wp_newPending : newPending.spec (GF := GF) (hG := hG))
    (wp_isAppendEntriesResponse : line.isAppendEntriesResponse.spec (GF := GF) (hG := hG)) :
    Trace.appendEntriesToSelfIfLogged.spec (GF := GF) (hG := hG) := by
  intro t tr g ts i
  wp_start as ⟨#Ht, #Hts, %Hl1, %Hi, %Hok⟩
  ihave HΦ' : (∀ out sts, ⌜sts = tr.appendEntriesToSelfIfLogged ts (uint.nat i)⌝ -∗ statesOut out sts -∗ Φ #out) $$ [HΦ]
  · iintro %out %sts %hs Hout; rw [hs]; iapply HΦ $$ Hout
  open_ts
  wp_auto
  wp_apply wp_loglineIsMessageEvent t tr g ts go!"SendAppendEntriesResponse" "SendAppendEntriesResponse" i i $$ [Ht Hts]
  · iframe Ht Hts; ipureintro; exact ⟨by strRel_lit, Hl1⟩
  cases hne : tr.isMessageEvent ts "SendAppendEntriesResponse" (uint.nat i) (uint.nat i)
  · ret_nil [Trace.appendEntriesToSelfIfLogged, hne]
  have hle : ts.l ≤ tr.len := Trace.isMessageEvent_le hne
  simp only [Bool.not_true]
  wp_auto
  wp_apply wp_AppendEntriesToSelf g.S' ts.s i $$ [Hst] as %q Hsq
  · iframe Hst; ipureintro; exact ⟨Hi, Hok⟩
  try wp_auto
  wp_apply wp_logline t tr g ts $$ [Ht Hts] as %ql #Hlp
  · iframe Ht Hts; ipureintro; exact ⟨Hl1, hle⟩
  cases hb : ts.s.appendEntriesToSelf (uint.nat i) with
  | none =>
    icases Hsq with %Hsq
    subst Hsq
    ret_nil [Trace.appendEntriesToSelfIfLogged, hne, hb]
  | some s2 =>
  icases Hsq with #Hsq
  ihave %Hqnn := stateRO_not_null $$ Hsq
  rw [decide_eq_false Hqnn]
  wp_auto
  wp_apply wp_validatePostStates t tr g ts q s2 i $$ [Ht Hts Hsq]
  · iframe Ht Hts Hsq; ipureintro; exact ⟨Hl1, hle⟩
  cases hv : tr.validatePostStates ts s2 (uint.nat i)
  · ret_nil [Trace.appendEntriesToSelfIfLogged, hne, hb, hv]
  simp only [Bool.not_true]
  wp_auto
  ipersist ln
  wp_apply wp_newPending g.S' ts.s q s2 _
      (fun m => (tr.line ts.l).isAppendEntriesResponse m && m.source == m.dest) $$ [Hst Hsq Hlp ln]
  · iframe Hst Hsq
    imodintro
    iintro %q' %m' %Φ'
    imodintro
    iintro #Hm' HΦ'
    wp_auto
    wp_apply wp_isAppendEntriesResponse ql (tr.line ts.l) q' m' $$ [Hm' Hlp]
    · iframe Hm' Hlp
    cases hr : (tr.line ts.l).isAppendEntriesResponse m'
    · wp_auto
      iapply HΦ'; ipureintro; simp
    wp_auto
    iunfold msgRO at Hm'
    icases Hm' with ⟨%gm, #Hgm, %Hv, -⟩
    icases typedPointsto_split _ _ _ $$ Hgm with Hgmf
    simp only [TypedPointsto.typedPointstoDef]
    iNamed Hgmf
    wp_auto
    rw [uint_decide Hv.2.2.2.2.2.2.2.2.2.2.2.1 Hv.2.2.2.2.2.2.2.2.2.2.2.2]
    have e : (m'.source == m'.dest) = decide (m'.source = m'.dest) := by
      by_cases h : m'.source = m'.dest <;> simp [h]
    simp only [Bool.true_and, e]
    iapply HΦ'; ipureintro; trivial
  cases hp : newPending ts.s s2 (fun m => (tr.line ts.l).isAppendEntriesResponse m && m.source == m.dest)
  · ret_nil [Trace.appendEntriesToSelfIfLogged, hne, hb, hv, hp]
  ret_single q, s2, Hsq [Trace.appendEntriesToSelfIfLogged, hne, hb, hv, hp]

end proof

end Etcdraft
end EtcdGrove
end Perennial
