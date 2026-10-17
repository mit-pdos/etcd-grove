/-
Trust boundary: `grpc.MaxRecvMsgSize` (an axiom; see `Spec/google_golang_org/grpc/MaxRecvMsgSize.lean`).
-/
module

public import Spec.google_golang_org.grpc.MaxRecvMsgSize

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

/-- **Trust boundary** (item 4, the server start): a request over the limit is refused before its
handler runs (`ResourceExhausted` for the client). -/
axiom grpc.MaxRecvMsgSize.wp_proof : grpc.MaxRecvMsgSize.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
