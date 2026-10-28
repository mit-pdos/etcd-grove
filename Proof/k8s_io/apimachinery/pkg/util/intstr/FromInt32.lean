/-
The trust boundary: `intstr.FromInt32` (names only; returns `IntOrString{Type: Int, IntVal: n}`, a value of the axiomatized struct). Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apimachinery.pkg.util.intstr.FromInt32

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace intstr

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.util.intstr.Assumptions]

axiom FromInt32.wp_proof : FromInt32.spec (GF := GF) (hG := hG)

end proof

end intstr
end EtcdGrove
end Perennial
