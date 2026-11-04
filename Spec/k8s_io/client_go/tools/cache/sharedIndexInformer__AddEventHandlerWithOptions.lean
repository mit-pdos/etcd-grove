/-
`(*sharedIndexInformer).AddEventHandlerWithOptions(handler, options)` (`shared_informer.go`):
under `startedLock`, an error once stopped; else a listener for the handler, added to the
processor (before the start: it receives every event from the first; after: under
`blockDeltas`, the store's items as initial adds first, then every later event). The handler's
contract (`handlerSpec`): each call with its event's facts, on the registering code's resource
`H`. No resync period (`handlerOptsOk`; scope). Lean-first; the DaemonSet run's track A.

**Specified before the informer's start only** (decision R6; the controller registers its handlers
before `Start`): it borrows a fraction of the not-started token (`infNotStarted`), so the informer
has neither started nor stopped and there is no error. After the start the call succeeds in Go too
(until the informer stops); the restriction is the spec's.
-/
module

public import Proof.k8s_io.client_go.tools.cache.SIIAt

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
variable [ctx_sem : _root_.Perennial.context.Assumptions]

/-- **`s.AddEventHandlerWithOptions(h, opts)`**: see the file header. -/
abbrev sharedIndexInformer.AddEventHandlerWithOptions.spec : Prop :=
  ∀ (s : Loc) (γa : ApiNames) (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config) (r : Res) (I : InfH) (Fam : Nat → Fn GF) (h : GoInterface) (opts : HandlerOptions) (H : List Ev → IProp GF),
  ∀ (q : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ siiAt s γa cfg r I Fam ∗ infNotStarted I.γi q ∗ handlerSpec γa r I.γi h H ∗ handlerOptsOk opts ∗ H [] }}
    (App (App (Val (s @!! go.GoType.PointerType sharedIndexInformer.ty @!! go!"AddEventHandlerWithOptions")) (Val #h)) (Val #opts))
  {{ (reg : GoInterface), RET (PairV #reg #(interface.nil : GoInterface)); infNotStarted I.γi q }}

end spec

end cache
end EtcdGrove
end Perennial
