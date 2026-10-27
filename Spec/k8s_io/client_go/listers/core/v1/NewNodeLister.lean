/-
`NewNodeLister(indexer)` (`listers/core/v1/node.go`): the Node lister over `indexer`, a
`*nodeLister` holding `listers.New[*Node](indexer, Resource("node"))`. Lean-first.
-/
module

public import Proof.k8s_io.client_go.listers.Defs
public import GeneratedProof.k8s_io.client_go.listers.core.v1

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace corelisters

open Iris Iris.BI k8s_io.client_go.listers.core.v1

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.listers.core.v1.Assumptions]

/-- **`NewNodeLister(idx)`** returns a fresh `*nodeLister` whose lister is over `idx`, not
namespaced (its `GroupResource` is `Resource`'s, unspecified). -/
abbrev NewNodeLister.spec : Prop :=
  ∀ (idx : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.listers.core.v1 }}
    (App (Val (@! k8s_io.client_go.listers.core.v1.NewNodeLister)) (Val #idx))
  {{ (l : Loc) (res : k8s_io.apimachinery.pkg.runtime.schema.GroupResource),
      RET #(interface.mkOk (go.GoType.PointerType nodeLister.ty) #l);
      l.[nodeLister, go!"ResourceIndexer"] ↦ (⟨idx, res, []⟩ : k8s_io.client_go.listers.ResourceIndexer Loc) }}

end spec

end corelisters
end EtcdGrove
end Perennial
