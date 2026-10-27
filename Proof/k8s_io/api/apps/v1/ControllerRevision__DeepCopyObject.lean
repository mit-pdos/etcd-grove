/-
The trust boundary: `(*ControllerRevision).DeepCopyObject()` (`zz_generated.deepcopy.go`, names only). A deep
copy: fresh cells for every pointer, slice and map the value reaches, the basic values copied, a
`time.Time`'s `*Location` shared (`metav1.Time.DeepCopyInto` is `*out = *in`). The deep values
(`Proof/k8s_io/api/Deep.lean`) are generated from the same type definitions; what they do not own
(an `intstr.IntOrString`, a `Quantity`, `RawExtension.Object`) is required nil or not owned, which
`DeepCopy` keeps (`if in.X != nil`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.api.apps.v1.ControllerRevision__DeepCopyObject

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace appsv1

open Iris Iris.BI Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.api.apps.v1.Assumptions]

axiom ControllerRevision.DeepCopyObject.wp_proof : ControllerRevision.DeepCopyObject.spec (GF := GF) (hG := hG)

end proof

end appsv1
end EtcdGrove
end Perennial
