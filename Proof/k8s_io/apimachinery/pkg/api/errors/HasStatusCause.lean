/-
The trust boundary of `apierrors.HasStatusCause` (see its spec).
-/
module

public import Spec.k8s_io.apimachinery.pkg.api.errors.HasStatusCause

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apierrors

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.api.errors.Assumptions]

axiom HasStatusCause.wp_proof : HasStatusCause.spec (GF := GF) (hG := hG)

end proof

end apierrors
end EtcdGrove
end Perennial
