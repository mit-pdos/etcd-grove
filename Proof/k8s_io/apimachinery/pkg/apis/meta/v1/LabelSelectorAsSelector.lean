/-
The trust boundary of `metav1.LabelSelectorAsSelector` (see its spec).
-/
module

public import Spec.k8s_io.apimachinery.pkg.apis.meta.v1.LabelSelectorAsSelector

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace labels

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The trust boundary (see the spec's file header). -/
axiom LabelSelectorAsSelector.wp_proof : LabelSelectorAsSelector.spec (GF := GF) (hG := hG)

end proof

end labels
end EtcdGrove
end Perennial
