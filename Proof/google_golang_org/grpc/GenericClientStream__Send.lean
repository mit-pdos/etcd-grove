/-
Trust boundary: `(*GenericClientStream[Req, Res]).Send(m)` (an axiom; see
`Spec/google_golang_org/grpc/GenericClientStream__Send.lean`: Goose does not translate methods of generic types).
-/
module

public import Spec.google_golang_org.grpc.GenericClientStream__Send

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

/-- **Trust boundary** (W-W): `(*GenericClientStream[Req, Res]).Send(m)` (`stream_interfaces.go`): `x.ClientStream.SendMsg(m)`. -/
axiom grpc.GenericClientStream.Send.wp_proof : grpc.GenericClientStream.Send.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
