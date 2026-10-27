/-
`NewControllerRevisionLister(indexer)` (`listers/apps/v1/controllerrevision.go`): the ControllerRevision lister over `indexer`, a
`*controllerRevisionLister` holding `listers.New[*ControllerRevision](indexer, Resource("controllerrevision"))`. Lean-first.
-/
module

public import Proof.k8s_io.client_go.listers.Defs
public import GeneratedProof.k8s_io.client_go.listers.apps.v1

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace appslisters

open Iris Iris.BI k8s_io.client_go.listers.apps.v1

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.listers.apps.v1.Assumptions]

/-- **`NewControllerRevisionLister(idx)`** returns a fresh `*controllerRevisionLister` whose lister is over `idx`, not
namespaced (its `GroupResource` is `Resource`'s, unspecified). -/
abbrev NewControllerRevisionLister.spec : Prop :=
  ∀ (idx : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.listers.apps.v1 }}
    (App (Val (@! k8s_io.client_go.listers.apps.v1.NewControllerRevisionLister)) (Val #idx))
  {{ (l : Loc) (res : k8s_io.apimachinery.pkg.runtime.schema.GroupResource),
      RET #(interface.mkOk (go.GoType.PointerType controllerRevisionLister.ty) #l);
      l.[controllerRevisionLister, go!"ResourceIndexer"] ↦ (⟨idx, res, []⟩ : k8s_io.client_go.listers.ResourceIndexer Loc) }}

end spec

end appslisters
end EtcdGrove
end Perennial
