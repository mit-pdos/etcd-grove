/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `Trace__loglineIsMessageEvent`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__loglineIsMessageEvent
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

theorem Trace.loglineIsMessageEvent.wp_proof (wp_logline : Trace.logline.spec (GF := GF) (hG := hG))
    (wp_loglineIsEvent : Trace.loglineIsEvent.spec (GF := GF) (hG := hG)) :
    Trace.loglineIsMessageEvent.spec (GF := GF) (hG := hG) := by
  intro t tr g ts e es i j
  wp_start as ⟨#Ht, #Hts, %He, %Hl1⟩
  wp_auto
  wp_apply wp_loglineIsEvent t tr g ts e es $$ [Ht Hts]
  · iframe Ht Hts; ipureintro; exact ⟨He, Hl1⟩
  cases hev : tr.isEvent ts es
  · wp_auto
    have : tr.isMessageEvent ts es (uint.nat i) (uint.nat j) = false := by
      unfold Trace.isMessageEvent; simp [hev]
    rw [this]; iapply HΦ; ipureintro; trivial
  have hle : ts.l ≤ tr.len := by unfold Trace.isEvent at hev; simp at hev; exact hev.1
  wp_auto
  wp_apply wp_logline t tr g ts $$ [Ht Hts] as %q #Hlp
  · iframe Ht Hts; ipureintro; exact ⟨Hl1, hle⟩
  open_lineP
  wp_auto
  cases hm : (tr.line ts.l).ev.msg with
  | none =>
    icases Hemsg with %Hnull
    rw [Hnull]
    wp_auto
    have : tr.isMessageEvent ts es (uint.nat i) (uint.nat j) = false := by
      unfold Trace.isMessageEvent; simp [hm]
    rw [this]; iapply HΦ; ipureintro; trivial
  | some mm =>
    icases Hemsg with ⟨%gm, #Hgm, -⟩
    ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hgm
    rw [decide_eq_false Hnn]
    wp_auto
    rw [decide_eq_decide.2 (uint_eq_iff _ _ _ _ Hlf.2.2.2.1 rfl)]
    by_cases hf : (tr.line ts.l).from = uint.nat i
    · rw [decide_eq_true hf]
      wp_auto
      rw [decide_eq_decide.2 (uint_eq_iff _ _ _ _ Hlf.2.2.2.2 rfl)]
      have : tr.isMessageEvent ts es (uint.nat i) (uint.nat j) = decide ((tr.line ts.l).to = uint.nat j) := by
        unfold Trace.isMessageEvent; simp [hev, hm, hf]; rfl
      rw [this]; iapply HΦ; ipureintro; trivial
    · rw [decide_eq_false hf]
      wp_auto
      have : tr.isMessageEvent ts es (uint.nat i) (uint.nat j) = false := by
        unfold Trace.isMessageEvent; simp [hev, hm, hf]
      rw [this]; iapply HΦ; ipureintro; trivial

end proof

end Etcdraft
end EtcdGrove
end Perennial
