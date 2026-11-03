/-
`(*InformerName).WithResource(gvr)` (`identity.go`) on a `nil` name (the factory's, no
`WithInformerName`): `InformerNameAndResource{gvr: gvr}`. Lean-first; the DaemonSet run's track A.
-/
module

public import Proof.k8s_io.client_go.tools.cache.InformerApi

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

/-- **`(nil).WithResource(gvr)`**: the resource, no name. -/
abbrev InformerName.WithResource.spec : Prop :=
  ∀ (gvr : k8s_io.apimachinery.pkg.runtime.schema.GroupVersionResource),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache }}
    (App (Val ((null : Loc) @!! go.GoType.PointerType InformerName.ty @!! go!"WithResource")) (Val #gvr))
  {{ RET #(InformerNameAndResource.mk go!"" gvr null); True }}

end spec

end cache
end EtcdGrove
end Perennial
