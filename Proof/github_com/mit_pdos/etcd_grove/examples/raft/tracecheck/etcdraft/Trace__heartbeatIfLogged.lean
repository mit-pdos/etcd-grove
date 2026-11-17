/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `Trace__heartbeatIfLogged`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__heartbeatIfLogged
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__loglineIsMessageEvent
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__logline
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__validateAfterAppendEntries
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__Heartbeat

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

theorem Trace.heartbeatIfLogged.wp_proof
    (wp_loglineIsMessageEvent : Trace.loglineIsMessageEvent.spec (GF := GF) (hG := hG))
    (wp_logline : Trace.logline.spec (GF := GF) (hG := hG))
    (wp_validateAfterAppendEntries : Trace.validateAfterAppendEntries.spec (GF := GF) (hG := hG))
    (wp_Heartbeat : State.Heartbeat.spec (GF := GF) (hG := hG)) :
    Trace.heartbeatIfLogged.spec (GF := GF) (hG := hG) := by
  intro t tr g ts i j sts
  wp_start as ⟨#Ht, #Hts, %Hl1, %Hi, %Hok, %Hev⟩
  ihave HΦ' : (∀ out sts', ⌜sts' = sts⌝ -∗ statesOut out sts' -∗ Φ #out) $$ [HΦ]
  · iintro %out %sts' %hs Hout; rw [hs]; iapply HΦ $$ Hout
  open_ts
  wp_auto
  wp_apply wp_loglineIsMessageEvent t tr g ts go!"SendAppendEntriesRequest" "SendAppendEntriesRequest" i j $$ [Ht Hts]
  · iframe Ht Hts; ipureintro; exact ⟨by strRel_lit, Hl1⟩
  cases hne : tr.isMessageEvent ts "SendAppendEntriesRequest" (uint.nat i) (uint.nat j)
  · ret_nil [Trace.heartbeatIfLogged, hne] at Hev
  have hle : ts.l ≤ tr.len := Trace.isMessageEvent_le hne
  simp only [Bool.not_true]
  wp_auto
  wp_apply wp_logline t tr g ts $$ [Ht Hts] as %ql #Hlp
  · iframe Ht Hts; ipureintro; exact ⟨Hl1, hle⟩
  open_lineP
  cases hm : (tr.line ts.l).ev.msg with
  | none => exact absurd (Trace.isMessageEvent_msg hne) (by simp [hm])
  | some ev =>
  icases Hemsg with ⟨%gev, #Hgev, %Hem⟩
  icases typedPointsto_split _ _ _ $$ Hgev with Hgevf
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hgevf
  wp_auto
  rw [decide_strRel Hem.1 (show strRel go!"MsgHeartbeat" "MsgHeartbeat" by strRel_lit)]
  by_cases h1 : ev.type = "MsgHeartbeat"
  rotate_left
  · rw [decide_eq_false h1]
    ret_nil [Trace.heartbeatIfLogged, hne, hm, h1] at Hev
  rw [decide_eq_true h1]
  simp only [Bool.not_true]
  wp_auto
  cases hae : ts.s.heartbeat (uint.nat i) (uint.nat j) with
  | error err =>
    exfalso
    simp [Trace.heartbeatIfLogged, hne, hm, h1, hae, Bind.bind, Except.bind] at Hev
  | ok o =>
  wp_apply wp_Heartbeat g.S' ts.s i j o $$ [Hst] as %q Hsq
  · iframe Hst; ipureintro; exact ⟨Hi, Hok, hae⟩
  cases o with
  | none =>
    icases Hsq with %Hsq
    subst Hsq
    ret_nil [Trace.heartbeatIfLogged, hne, hm, h1, hae] at Hev
  | some s2 =>
  icases Hsq with #Hsq
  ihave %Hqnn := stateRO_not_null $$ Hsq
  rw [decide_eq_false Hqnn]
  wp_auto
  wp_apply wp_validateAfterAppendEntries t tr g ts q s2 i $$ [Ht Hts Hsq]
  · iframe Ht Hts Hsq; ipureintro; exact ⟨Hl1, hle⟩
  cases hv : tr.validateAfterAppendEntries ts s2 (uint.nat i)
  · ret_nil [Trace.heartbeatIfLogged, hne, hm, h1, hae, hv] at Hev
  ret_single q, s2, Hsq [Trace.heartbeatIfLogged, hne, hm, h1, hae, hv] at Hev

end proof

end Etcdraft
end EtcdGrove
end Perennial
