/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `Trace__loglineIsNodeEvent`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__loglineIsNodeEvent
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__loglineIsEvent
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

theorem Trace.loglineIsNodeEvent.wp_proof (wp_logline : Trace.logline.spec (GF := GF) (hG := hG))
    (wp_loglineIsEvent : Trace.loglineIsEvent.spec (GF := GF) (hG := hG)) :
    Trace.loglineIsNodeEvent.spec (GF := GF) (hG := hG) := by
  intro t tr g ts e es i
  wp_start as ⟨#Ht, #Hts, %He, %Hl1⟩
  wp_auto
  wp_apply wp_loglineIsEvent t tr g ts e es $$ [Ht Hts]
  · iframe Ht Hts; ipureintro; exact ⟨He, Hl1⟩
  cases hev : tr.isEvent ts es
  · wp_auto
    have : tr.isNodeEvent ts es (uint.nat i) = false := by unfold Trace.isNodeEvent; simp [hev]
    rw [this]; iapply HΦ; ipureintro; trivial
  have hle : ts.l ≤ tr.len := by unfold Trace.isEvent at hev; simp at hev; exact hev.1
  wp_auto
  wp_apply wp_logline t tr g ts $$ [Ht Hts] as %q ⟨%ln, #Hq, #Hln⟩
  · iframe Ht Hts; ipureintro; exact ⟨Hl1, hle⟩
  open_line
  wp_auto
  rw [decide_eq_decide.2 (uint_eq_iff _ _ _ _ Hlf.1 rfl)]
  have : tr.isNodeEvent ts es (uint.nat i) = decide ((tr.line ts.l).nid = uint.nat i) := by
    unfold Trace.isNodeEvent; simp [hev]; rfl
  rw [this]
  iapply HΦ; ipureintro; trivial

end proof

end Etcdraft
end EtcdGrove
end Perennial
