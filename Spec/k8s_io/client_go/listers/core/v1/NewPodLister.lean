/-
`NewPodLister(indexer)` (`listers/core/v1/pod.go`): the Pod lister over `indexer`, a
`*podLister` holding `listers.New[*Pod](indexer, Resource("pod"))`. Lean-first.
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

/-- **`NewPodLister(idx)`** returns a fresh `*podLister` whose lister is over `idx`, not
namespaced (its `GroupResource` is `Resource`'s, unspecified). -/
abbrev NewPodLister.spec : Prop :=
  ∀ (idx : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.listers.core.v1 }}
    (App (Val (@! k8s_io.client_go.listers.core.v1.NewPodLister)) (Val #idx))
  {{ (l : Loc) (res : k8s_io.apimachinery.pkg.runtime.schema.GroupResource),
      RET #(interface.mkOk (go.GoType.PointerType podLister.ty) #l);
      l.[podLister, go!"ResourceIndexer"] ↦ (⟨idx, res, []⟩ : k8s_io.client_go.listers.ResourceIndexer Loc) }}

end spec

end corelisters
end EtcdGrove
end Perennial
