/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8sdaemonset/apimodel/copyObject.lean`. Lean-first.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.copyObject

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apimodel

open Iris Iris.BI Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8sdaemonset

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : apimodel.Assumptions]

/-- **Not proved: the model's type assertion to `object`** (`o.DeepCopyObject().(object)`). Goose,
at the pinned Perennial, writes the interface `object` (which embeds `runtime.Object` and
`metav1.Object`) with the embedded interfaces as type terms (`TypeElem [TypeTerm Object.ty]`),
and Perennial's `typeSetContains` reads a type term as that exact type: the assertion of a
`*corev1.Pod` to `object` panics in the model, where Go's succeeds. Perennial's `lean` has the fix
(an interface written as all its methods, the embedded ones included, and method sets emitted:
8ef540a62, d30f71f36, after the pin): with the pin bump this is `DeepCopyObject`'s spec
(`Spec/k8s_io/api/{core,apps}/v1/*__DeepCopyObject.lean`) per type and the method-set fact.
(`notes/k8s-apimodel-goose.md`, gap C8.) -/
theorem copyObject.wp_proof : copyObject.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end apimodel
end EtcdGrove
end Perennial
