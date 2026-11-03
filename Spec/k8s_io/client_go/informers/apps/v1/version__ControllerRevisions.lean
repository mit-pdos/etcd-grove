/-
`(*version).ControllerRevisions()`: the typed informer `&controllerRevisionInformer{factory, namespace,
tweakListOptions}` of the version's. Lean-first; the DaemonSet run's track A.
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

/-- **`v.ControllerRevisions()`**: resource `.revisions`'s typed informer of the factory. -/
abbrev version.ControllerRevisions.spec : Prop :=
  ∀ (v f : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.informers.apps.v1 ∗ facRefAt k8s_io.client_go.informers.apps.v1.version v f }}
    (App (Val (v @!! go.GoType.PointerType k8s_io.client_go.informers.apps.v1.version.ty @!! go!"ControllerRevisions"))
      (Val #()))
  {{ (l : Loc), RET #(interface.mkOk (go.GoType.PointerType k8s_io.client_go.informers.apps.v1.controllerRevisionInformer.ty) #l);
      typedInfAt .revisions l f }}

end spec

end appsinformers
end EtcdGrove
end Perennial
