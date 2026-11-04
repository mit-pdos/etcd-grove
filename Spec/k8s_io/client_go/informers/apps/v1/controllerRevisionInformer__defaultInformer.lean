/-
`(*controllerRevisionInformer).defaultInformer(client, resyncPeriod)` (the factory's `newFunc` for `.revisions`):
`NewTypedControllerRevisionInformerWithOptions(client, f.namespace, {resync, Indexers{NamespaceIndex: MetaNamespaceIndexFunc},
f.factory.InformerName(), f.tweakListOptions})`: a new informer of `.revisions`, its store
indexed by namespace (relation `Fams .revisions "namespace" = nsIdxFn`). Lean-first; the DaemonSet run's
track A. The informer's not-started token is the caller's (`γns`: the factory's of the
resource, decision R6).
-/
module

public import Proof.k8s_io.client_go.informers.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace appsinformers

open Iris Iris.BI apimodel cache informer informers

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.informers.apps.v1.Assumptions]
variable [cache_sem : k8s_io.client_go.tools.cache.Assumptions]
variable [ctx_sem : _root_.Perennial.context.Assumptions]

/-- **`i.defaultInformer(client, 0)`**: a new informer of `.revisions`. -/
abbrev controllerRevisionInformer.defaultInformer.spec : Prop :=
  ∀ (l f : Loc) (γF : FacNames) (γa : ApiNames) (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config) (Fams : Res → GoString → Fn GF) (c : Loc) (γns : GName),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.informers.apps.v1 ∗ typedInfAt .revisions l f ∗ isFactory f γF γa cfg Fams ∗ clientsetAt c γa cfg false ∗ nsLock γns false }}
    (App (App (Val (l @!! go.GoType.PointerType k8s_io.client_go.informers.apps.v1.controllerRevisionInformer.ty @!! go!"defaultInformer"))
      (Val #(clientVal c))) (Val #(W64 0 : time.Duration)))
  {{ (x : GoInterface), RET #x; newInfOut γa .revisions (Fams .revisions) γns x }}

end spec

end appsinformers
end EtcdGrove
end Perennial
