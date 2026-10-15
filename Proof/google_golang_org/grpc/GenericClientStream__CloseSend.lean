/-
Trust boundary: `(*GenericClientStream[Req, Res]).CloseSend()`, promoted from the embedded `ClientStream` (an axiom; see
`Spec/google_golang_org/grpc/GenericClientStream__CloseSend.lean`: Goose does not translate methods of generic types).
-/
module

public import Spec.google_golang_org.grpc.GenericClientStream__CloseSend

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

/-- **Trust boundary** (W-W): `(*GenericClientStream[Req, Res]).CloseSend()`, promoted from the embedded `ClientStream`: `x.ClientStream.CloseSend()`. -/
axiom grpc.GenericClientStream.CloseSend.wp_proof : grpc.GenericClientStream.CloseSend.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
