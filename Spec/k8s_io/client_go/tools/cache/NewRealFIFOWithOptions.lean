/-
`cache.NewRealFIFOWithOptions(opts)` (`the_real_fifo.go`), as the informers configure it under
the `AtomicFIFO` gate (`newQueueFIFO`): atomic events and bookmark deltas, no known objects, no
transformer, no metrics provider (the no-op metrics), a key function meeting the FIFO's contract.
**Over preallocated state names** (the run's decision 2026-11-03, `InformerAlloc.lean`): it takes
the lock's halves of the queue's state ghost variables `st`/`sy` (`fifoPre`), allocated with the
informer invariant before the FIFO exists, and returns the FIFO over names with those `st`/`sy`
(the lock token, the exclusive token and the `synced` channel's names its own). Lean-first; the
DaemonSet run's track A.
-/
module

public import Proof.k8s_io.client_go.tools.cache.InformerAlloc

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI apimodel cache informer k8s_io.client_go.tools.cache

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- **`NewRealFIFOWithOptions(opts)`**: see the file header. -/
abbrev NewRealFIFOWithOptions.spec : Prop :=
  ∀ (OK : GoInterface → IProp GF) (o : RealFIFOOptions) (st sy : GName),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ fifoPre st sy ∗
      (⌜o.KnownObjects' = interface.nil ∧ o.Transformer' = func.nil ∧ o.AtomicEvents' = true ∧
        o.EmitDeltaTypeBookmark' = true ∧ o.MetricsProvider' = interface.nil ∧
        o.KeyFunction' ≠ func.nil⌝ ∗ keyNoErr OK o.KeyFunction' ∗ keyAny o.KeyFunction' ∗
      (⌜o.Logger' = null⌝ ∨ ∃ lg : github_com.go_logr.logr.Logger, o.Logger' ↦□ lg)) }}
    (App (Val (@! NewRealFIFOWithOptions)) (Val #o))
  {{ (f : Loc), RET #f; ∃ γf : FifoNames, ⌜γf.st = st ∧ γf.sy = sy⌝ ∗ isFIFO f γf OK }}

end spec

end cache
end EtcdGrove
end Perennial
