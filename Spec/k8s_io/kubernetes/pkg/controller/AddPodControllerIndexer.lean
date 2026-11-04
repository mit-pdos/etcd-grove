/-
`controller.AddPodControllerIndexer(podInformer)` (`controller_utils.go`, with body): if the pod
store has no indexer named `podCtlIndex`, adds one indexing a pod by the controller reference (`AddIndexers`). Lean-first,
track C of the DaemonSet run. Before the informer starts (decision R6: a fraction of its
not-started token, lent to `AddIndexers` and given back).

**The margin**: on `nil`, the index is registered (`infIdx`); its relation is `podCtlFn` when this call
added it (the store had none); an index already there is one whose relation the informer's API
does not say (`GetIndexers`' result is a map of functions), so the post does not either.
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

/-- `AddPodControllerIndexer(x)` for the pod informer `x`, its family's `podCtlFn` at `j`. -/
abbrev AddPodControllerIndexer.spec : Prop :=
  ∀ (x : GoInterface) (γa : ApiNames) (I : InfH) (Fam : Nat → Fn GF) (j : Nat) (q : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller ∗
      isInformer x γa .pods I Fam ∗ ⌜Fam j = podCtlFn⌝ ∗ infNotStarted I.γi q }}
    (App (Val (@! k8s_io.kubernetes.pkg.controller.AddPodControllerIndexer)) (Val #x))
  {{ (err : GoInterface), RET #err; infNotStarted I.γi q ∗
      (⌜err ≠ interface.nil⌝ ∨ (⌜err = interface.nil⌝ ∗ ∃ j', infIdx I podCtlIndex j')) }}

end spec

end dsctl
end EtcdGrove
end Perennial
