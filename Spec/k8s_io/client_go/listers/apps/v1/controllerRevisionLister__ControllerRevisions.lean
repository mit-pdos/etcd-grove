/-
`(*controllerRevisionLister).ControllerRevisions(namespace)` (`listers/apps/v1/controllerrevision.go`): the lister's namespaced lister,
`controllerRevisionNamespaceLister{listers.NewNamespaced(s.ResourceIndexer, namespace)}`. Lean-first.
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

/-- **`s.ControllerRevisions(ns)`** returns the namespace lister of `s`'s lister restricted to `ns`. -/
abbrev controllerRevisionLister.ControllerRevisions.spec : Prop :=
  ∀ (s : Loc) (dq : DFrac) (ri : k8s_io.client_go.listers.ResourceIndexer Loc) (ns : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.listers.apps.v1 ∗
      s.[controllerRevisionLister, go!"ResourceIndexer"] ↦{dq} ri }}
    (App (Val (s @!! go.GoType.PointerType controllerRevisionLister.ty @!! go!"ControllerRevisions")) (Val #ns))
  {{ RET #(interface.mkOk controllerRevisionNamespaceLister.ty
        #(⟨{ ri with namespace' := ns }⟩ : k8s_io.client_go.listers.apps.v1.controllerRevisionNamespaceLister));
      s.[controllerRevisionLister, go!"ResourceIndexer"] ↦{dq} ri }}

end spec

end appslisters
end EtcdGrove
end Perennial
