/-
Proof of `Spec/k8s_io/client_go/util/workqueue/newQueueWithConfig.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.workqueue.newQueueWithConfig
public import Spec.k8s_io.client_go.util.workqueue.DefaultQueue
public import Spec.k8s_io.client_go.util.workqueue.newQueueMetrics
public import Spec.k8s_io.client_go.util.workqueue.newQueue

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace workqueue

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.util.workqueue

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.util.workqueue.Assumptions]

theorem newQueueWithConfig.wp_proof
    (wp_DefaultQueue : DefaultQueue.spec (GF := GF) (hG := hG))
    (wp_newQueueMetrics : newQueueMetrics.spec (GF := GF) (hG := hG))
    (wp_newQueue : newQueue.spec (GF := GF) (hG := hG)) :
    newQueueWithConfig.spec (GF := GF) (hG := hG) := by
  intro K T _ cfg period Hcfg
  wp_start
  ihave #Hgp := globalProvider_noop $$ Hpkg
  wp_auto
  obtain ⟨hq, hm⟩ := Hcfg
  -- the provider: the configuration's, or the global (no-op) one
  wp_join iprop(∃ mp : MetricsProvider, metricsProvider_ptr ↦ mp ∗ config_ptr ↦ cfg ∗
      ⌜cfg.Name' = [] ∨ mp = noopProvider⌝)
    at next with [metricsProvider config] as ⟨%mp, metricsProvider, config, %Hmp⟩
  · cases hmp : cfg.MetricsProvider'
    · -- set: the configuration's
      wp_auto
      isplitr
      · ipureintro; rfl
      iexists _
      iframe
      ipureintro
      rw [hmp] at hm
      rcases hm with h | h | h
      · exact Or.inl h
      · cases h
      · exact Or.inr (hmp.trans h)
    · -- unset: the global one
      wp_auto
      isplitr
      · ipureintro; rfl
      iexists _
      iframe
      ipureintro; exact Or.inr rfl
  -- the clock: the configuration's, or the real one
  wp_join iprop(∃ cfg' : TypedQueueConfig K, config_ptr ↦ cfg' ∗
      ⌜cfg'.Queue' = cfg.Queue' ∧ cfg'.Name' = cfg.Name'⌝)
    at next with [config] as ⟨%cfg1, config, %Hcfg1⟩
  · cases hc : cfg.Clock'
    · wp_auto
      isplitr
      · ipureintro; rfl
      iexists _
      iframe
      ipureintro; exact ⟨rfl, rfl⟩
    · wp_auto
      isplitr
      · ipureintro; rfl
      iexists _
      iframe
      ipureintro; exact ⟨rfl, rfl⟩
  rw [Hcfg1.1, hq]
  wp_auto
  wp_apply wp_DefaultQueue (K := K) (T := T) as %l Hfifo
  wp_apply wp_newQueueMetrics (K := K) (T := T) mp cfg1.Name' _ (by rw [Hcfg1.2]; exact Hmp)
  wp_apply wp_newQueue $$ [$Hfifo] as %q %γ ⟨#Hq, Htoks⟩
  iapply HΦ
  iframe #; iframe

end proof

end workqueue
end EtcdGrove
end Perennial
