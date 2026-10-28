/-
Proof of `Spec/k8s_io/api/apps/v1/Resource.lean`. Trust boundary (names-only).
-/
module

public import Spec.k8s_io.api.apps.v1.Resource

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace appsv1

open Iris Iris.BI Iris.ProofMode 

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.api.apps.v1.Assumptions]

/-- Trust boundary: `Resource` is names-only (`k8s.io/api/apps/v1`); it builds a struct
literal and returns. -/
axiom Resource.wp_proof : Resource.spec (GF := GF) (hG := hG)

end proof

end appsv1
end EtcdGrove
end Perennial
