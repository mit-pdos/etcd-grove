/-
`controller.AddPodNodeNameIndexer(podInformer)` (`controller_utils.go`, with body): if the pod
store has no indexer named `podNodeIndex`, adds one indexing a pod by the node name (`AddIndexers`). Lean-first,
track C of the DaemonSet run. Before the informer starts (decision R6: a fraction of its
not-started token, lent to `AddIndexers` and given back).

The index named `podNodeIndex` is registered for good (`infIdx`, its relation the family's
`FamN podNodeIndex`, which the caller fixes to `podNodeFn`), whether this call added it, found it already
there (the `GetIndexers` lookup; needs a lookup contract on the informer's indexers, the run's
report), or `AddIndexers` refused the name as already registered; the error (from `AddIndexers`
only) says nothing more.
-/
module

public import Proof.k8s_io.kubernetes.pkg.controller.daemon.LifeDefs

@[expose] public section

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI apimodel informer cache

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [ctl_sem : k8s_io.kubernetes.pkg.controller.Assumptions]
variable [cache_sem : k8s_io.client_go.tools.cache.Assumptions]
variable [ctx_sem : _root_.Perennial.context.Assumptions]

/-- `AddPodNodeNameIndexer(x)` for the pod informer `x`, its family's `podNodeFn` under `podNodeIndex`. -/
abbrev AddPodNodeNameIndexer.spec : Prop :=
  ∀ (x : GoInterface) (γa : ApiNames) (I : InfH) (FamN : GoString → Fn GF) (q : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller ∗
      isInformer x γa .pods I FamN ∗ ⌜FamN podNodeIndex = podNodeFn⌝ ∗ infNotStarted I.γi q }}
    (App (Val (@! k8s_io.kubernetes.pkg.controller.AddPodNodeNameIndexer)) (Val #x))
  {{ (err : GoInterface), RET #err; infNotStarted I.γi q ∗ infIdx I podNodeIndex }}

end spec

end dsctl
end EtcdGrove
end Perennial
