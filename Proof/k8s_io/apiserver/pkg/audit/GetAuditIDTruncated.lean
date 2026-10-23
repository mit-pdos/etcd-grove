/-
The trust boundary of `audit.GetAuditIDTruncated` (see its spec).
-/
module

public import Spec.k8s_io.apiserver.pkg.audit.GetAuditIDTruncated

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The trust boundary (see the spec's file header). -/
axiom audit.GetAuditIDTruncated.wp_proof : audit.GetAuditIDTruncated.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
