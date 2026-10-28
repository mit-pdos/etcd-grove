/-
The trust boundary: `apierrors.NewConflict` (names only: its message `Sprintf`s an error). Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apimachinery.pkg.api.errors.NewConflict

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apierrors

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.api.errors.Assumptions]

axiom NewConflict.wp_proof : NewConflict.spec (GF := GF) (hG := hG)

end proof

end apierrors
end EtcdGrove
end Perennial
