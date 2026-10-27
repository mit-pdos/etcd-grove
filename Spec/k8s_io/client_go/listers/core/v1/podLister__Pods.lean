/-
`(*podLister).Pods(namespace)` (`listers/core/v1/pod.go`): the lister's namespaced lister,
`podNamespaceLister{listers.NewNamespaced(s.ResourceIndexer, namespace)}`. Lean-first.
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

/-- **`s.Pods(ns)`** returns the namespace lister of `s`'s lister restricted to `ns`. -/
abbrev podLister.Pods.spec : Prop :=
  ∀ (s : Loc) (dq : DFrac) (ri : k8s_io.client_go.listers.ResourceIndexer Loc) (ns : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.listers.core.v1 ∗
      s.[podLister, go!"ResourceIndexer"] ↦{dq} ri }}
    (App (Val (s @!! go.GoType.PointerType podLister.ty @!! go!"Pods")) (Val #ns))
  {{ RET #(interface.mkOk podNamespaceLister.ty
        #(⟨{ ri with namespace' := ns }⟩ : k8s_io.client_go.listers.core.v1.podNamespaceLister));
      s.[podLister, go!"ResourceIndexer"] ↦{dq} ri }}

end spec

end corelisters
end EtcdGrove
end Perennial
