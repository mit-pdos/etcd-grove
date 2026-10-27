/-
Proof of `Spec/k8s_io/api/core/v1/Resource.lean`. Trust boundary (names-only).
-/
module

public import Spec.k8s_io.api.core.v1.Resource

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace corev1

open Iris Iris.BI Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.api.core.v1.Assumptions]

/-- Trust boundary: `Resource` is names-only (`k8s.io/api/core/v1`); it builds a struct literal
and returns. -/
axiom Resource.wp_proof : Resource.spec (GF := GF) (hG := hG)

end proof

end corev1
end EtcdGrove
end Perennial
