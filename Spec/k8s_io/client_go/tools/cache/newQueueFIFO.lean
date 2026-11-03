/-
`cache.newQueueFIFO(logger, objectType, clientState, transform, identifier, metricsProvider)`
(`controller.go`), with the gates `InOrderInformers` and `AtomicFIFO` on (`Main`'s): a
`RealFIFO` with atomic events and bookmarks, keyed by `MetaNamespaceKeyFunc`, no transformer or
metrics provider, over the preallocated state names (`NewRealFIFOWithOptions`). Lean-first; the
DaemonSet run's track A.
-/
module

public import Spec.k8s_io.client_go.tools.cache.NewRealFIFOWithOptions

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

/-- **`newQueueFIFO(…)`**: the informer's FIFO. -/
abbrev newQueueFIFO.spec : Prop :=
  ∀ (OK : GoInterface → IProp GF) (lg : github_com.go_logr.logr.Logger) (ot cs : GoInterface)
    (idn : InformerNameAndResource) (st sy : GName),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ fifoPre st sy ∗ keyNoErr OK (functions MetaNamespaceKeyFunc []) ∗
      keyAny (functions MetaNamespaceKeyFunc []) }}
    (App (App (App (App (App (App (Val (@! newQueueFIFO)) (Val #lg)) (Val #ot)) (Val #cs))
      (Val #(func.nil : TransformFunc))) (Val #idn)) (Val #(interface.nil : InformerMetricsProvider)))
  {{ (lg' : github_com.go_logr.logr.Logger) (f : Loc),
      RET (PairV #lg' #(interface.mkOk (go.GoType.PointerType RealFIFO.ty) #f : Queue));
      ∃ γf : FifoNames, ⌜γf.st = st ∧ γf.sy = sy⌝ ∗ isFIFO f γf OK }}

end spec

end cache
end EtcdGrove
end Perennial
