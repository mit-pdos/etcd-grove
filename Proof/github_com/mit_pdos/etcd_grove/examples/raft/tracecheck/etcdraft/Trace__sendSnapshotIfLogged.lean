/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `Trace__sendSnapshotIfLogged`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__sendSnapshotIfLogged
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__loglineIsMessageEvent
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__logline

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

theorem Trace.sendSnapshotIfLogged.wp_proof
    (wp_loglineIsMessageEvent : Trace.loglineIsMessageEvent.spec (GF := GF) (hG := hG))
    (wp_logline : Trace.logline.spec (GF := GF) (hG := hG)) :
    Trace.sendSnapshotIfLogged.spec (GF := GF) (hG := hG) := by
  intro t tr g ts i j index
  wp_start as ⟨#Ht, #Hts, %Hl1, %Hsnap⟩
  have hres : tr.sendSnapshotIfLogged ts (uint.nat i) (uint.nat j) (sint.Z index) = .ok [] := by
    unfold Trace.sendSnapshotIfLogged
    cases hm : (tr.line ts.l).ev.msg with
    | none => simp [Pure.pure, Except.pure]
    | some ev =>
      have : ev.type ≠ "MsgSnap" := by rw [hm] at Hsnap; simpa using Hsnap
      simp [this, Pure.pure, Except.pure]
  ihave HΦ' : statesOut (GF := GF) slice.nil [] -∗ Φ #(slice.nil) $$ [HΦ]
  · iintro Hout; iapply HΦ; iframe Hout; ipureintro; exact hres
  open_ts
  wp_auto
  wp_apply wp_loglineIsMessageEvent t tr g ts go!"SendAppendEntriesRequest" "SendAppendEntriesRequest" i j $$ [Ht Hts]
  · iframe Ht Hts; ipureintro; exact ⟨by strRel_lit, Hl1⟩
  cases hne : tr.isMessageEvent ts "SendAppendEntriesRequest" (uint.nat i) (uint.nat j)
  · wp_auto
    iapply HΦ'; iapply statesOut_nil
  have hle : ts.l ≤ tr.len := Trace.isMessageEvent_le hne
  wp_auto
  wp_apply wp_logline t tr g ts $$ [Ht Hts] as %ql #Hlp
  · iframe Ht Hts; ipureintro; exact ⟨Hl1, hle⟩
  open_lineP
  cases hm : (tr.line ts.l).ev.msg with
  | none => exact absurd (Trace.isMessageEvent_msg hne) (by simp [hm])
  | some ev =>
  rw [hm] at Hsnap
  have h1 : ev.type ≠ "MsgSnap" := by simpa using Hsnap
  icases Hemsg with ⟨%gev, #Hgev, %Hem⟩
  icases typedPointsto_split _ _ _ $$ Hgev with Hgevf
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hgevf
  wp_auto
  rw [decide_strRel Hem.1 (show strRel go!"MsgSnap" "MsgSnap" by strRel_lit), decide_eq_false h1]
  wp_auto
  iapply HΦ'; iapply statesOut_nil

end proof

end Etcdraft
end EtcdGrove
end Perennial
