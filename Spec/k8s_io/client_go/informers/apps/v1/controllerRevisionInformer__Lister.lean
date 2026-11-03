/-
`(*controllerRevisionInformer).Lister()`: `NewControllerRevisionLister(f.Informer().GetIndexer())`: a lister over the factory's
informer's store (`riVal I.ca res []`, the names the factory's for good: the same store as
every `Informer()`'s). Lean-first; the DaemonSet run's track A.
-/
module

public import Proof.k8s_io.client_go.informers.Defs
public import Spec.k8s_io.client_go.listers.apps.v1.NewControllerRevisionLister

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

/-- **`i.Lister()`**: the lister of the factory's informer of `.revisions`. -/
abbrev controllerRevisionInformer.Lister.spec : Prop :=
  ∀ (l f : Loc) (γF : FacNames) (γa : ApiNames) (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config) (Fams : Res → Nat → Fn GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.informers.apps.v1 ∗ typedInfAt .revisions l f ∗ isFactory f γF γa cfg Fams }}
    (App (Val (l @!! go.GoType.PointerType k8s_io.client_go.informers.apps.v1.controllerRevisionInformer.ty @!! go!"Lister")) (Val #()))
  {{ (ll : Loc) (res : k8s_io.apimachinery.pkg.runtime.schema.GroupResource),
      RET #(interface.mkOk (go.GoType.PointerType k8s_io.client_go.listers.apps.v1.controllerRevisionLister.ty) #ll);
      ∃ I : InfH, facInf γF .revisions I ∗
        ll.[k8s_io.client_go.listers.apps.v1.controllerRevisionLister, go!"ResourceIndexer"] ↦ listers.riVal I.ca res [] }}

end spec

end appsinformers
end EtcdGrove
end Perennial
