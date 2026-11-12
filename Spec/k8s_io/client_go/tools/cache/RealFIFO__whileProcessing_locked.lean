/-
`(*RealFIFO).whileProcessing_locked(process)` (`the_real_fifo.go:454`): run `process`, the lock released meanwhile when `unlockWhileProcessing` and the queue is short. Lean-first; phase 4 of `notes/k8s-daemonset-plan.md` (the informers' FIFO).
-/
module

public import Proof.k8s_io.client_go.tools.cache.FIFODefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI k8s_io.client_go.tools.cache

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- **`f.whileProcessing_locked(pf)`** (the caller holds the lock and the FIFO's resource): runs
`pf()`, which ends in `R err`; the lock and a FIFO resource (another state, when the lock was
released meanwhile) held again after. -/
abbrev RealFIFO.whileProcessing_locked.spec : Prop :=
  ∀ (f : Loc) (γ : FifoNames) (OK : GoInterface → IProp GF) (ch : GoChan) (uwp : Bool) (mp : Loc)
    (h : HistogramMetric) (pf : GoFunc) (R : GoInterface → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗
      sync.isRWMutexGuard (f.[RealFIFO, go!"lock"]) (fifoTok γ) ∗ fifoInv f γ OK ch ∗
      f.[RealFIFO, go!"unlockWhileProcessing"] ↦□ uwp ∗ f.[RealFIFO, go!"batchSize"] ↦□ (W64 1000) ∗
      f.[RealFIFO, go!"metrics"] ↦□ mp ∗ mp.[fifoMetrics, go!"processingLatency"] ↦□ h ∗ obsOk h ∗
      sync.ownRWMutexWLocked (f.[RealFIFO, go!"lock"]) (fifoTok γ) ∗ fifoRes f γ OK ch ∗
      WP (App (Val #pf) (Val #())) {{ r, ∃ err : GoInterface, ⌜r = #err⌝ ∗ R err }} }}
    (App (Val (f @!! go.GoType.PointerType RealFIFO.ty @!! go!"whileProcessing_locked")) (Val #pf))
  {{ (err : GoInterface), RET #err; sync.ownRWMutexWLocked (f.[RealFIFO, go!"lock"]) (fifoTok γ) ∗
      fifoRes f γ OK ch ∗ R err }}

end spec

end cache
end EtcdGrove
end Perennial
