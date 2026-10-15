/-
**Trust boundary**: `status.Code` of an error grpc accepts returns (an axiom; see `Spec/google_golang_org/grpc/status/Code.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.google_golang_org.grpc.status.Code

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **Trust boundary**: `status.Code` of an error grpc accepts returns. -/
axiom status.Code.wp_proof : status.Code.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
