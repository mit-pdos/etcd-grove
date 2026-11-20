/-
The trust boundary: `(*Node).DeepCopyObject()` (`zz_generated.deepcopy.go`, names only). A deep
copy: fresh cells for every pointer, slice and map the value reaches, the basic values copied, a
`time.Time`'s `*Location` shared (`metav1.Time.DeepCopyInto` is `*out = *in`). The deep values
(`Proof/k8s_io/api/Deep.lean`) are generated from the same type definitions; what they do not own
(an `intstr.IntOrString`, a `Quantity`, `RawExtension.Object`) is required nil or not owned (a
pointer to a `Quantity` or a `FieldsV1` nil), which
`DeepCopy` keeps (`if in.X != nil`). Lean-first (no Rocq counterpart).

Not proved yet: `etc/gen-k8s-deep.py` proves the deep copies of the structs this object reaches
(`Proof/k8s_io/api/DeepCopy/`) but `NodeStatus.DeepCopyInto`'s `out.DaemonEndpoints = in.DaemonEndpoints` copies a
`NodeDaemonEndpoints`, a struct of integers, between two memory places, which goose's guard refuses
(Perennial `docs/design/unsafe-memory.md`, R4), so the function is not translated.
-/
module

public import Spec.k8s_io.api.core.v1.Node__DeepCopyObject

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace corev1

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.api.core.v1.Assumptions]

axiom Node.DeepCopyObject.wp_proof : Node.DeepCopyObject.spec (GF := GF) (hG := hG)

end proof

end corev1
end EtcdGrove
end Perennial
