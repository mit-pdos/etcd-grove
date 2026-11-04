/-
`(*podInformer).defaultInformer(client, resyncPeriod)` (the factory's `newFunc` for `.pods`):
`NewTypedPodInformerWithOptions(client, f.namespace, {resync, Indexers{NamespaceIndex: MetaNamespaceIndexFunc},
f.factory.InformerName(), f.tweakListOptions})`: a new informer of `.pods`, its store
indexed by namespace (relation `Fams .pods 0 = nsIdxFn`). Lean-first; the DaemonSet run's
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
namespace coreinformers

open Iris Iris.BI apimodel cache informer informers

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.informers.core.v1.Assumptions]
variable [cache_sem : k8s_io.client_go.tools.cache.Assumptions]
variable [ctx_sem : _root_.Perennial.context.Assumptions]

/-- **`i.defaultInformer(client, 0)`**: a new informer of `.pods`. -/
abbrev podInformer.defaultInformer.spec : Prop :=
  ∀ (l f : Loc) (γF : FacNames) (γa : ApiNames) (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config) (Fams : Res → Nat → Fn GF) (c : Loc) (γns : GName),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.informers.core.v1 ∗ typedInfAt .pods l f ∗ isFactory f γF γa cfg Fams ∗ clientsetAt c γa cfg false ∗ nsLock γns false }}
    (App (App (Val (l @!! go.GoType.PointerType k8s_io.client_go.informers.core.v1.podInformer.ty @!! go!"defaultInformer"))
      (Val #(clientVal c))) (Val #(W64 0 : time.Duration)))
  {{ (x : GoInterface), RET #x; newInfOut γa .pods (Fams .pods) γns x }}

end spec

end coreinformers
end EtcdGrove
end Perennial
