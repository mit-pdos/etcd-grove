/-
Trust boundary: `(*GenericServerStream[Req, Res]).Send(m)` (an axiom; see
`Spec/google_golang_org/grpc/GenericServerStream__Send.lean`: Goose does not translate methods of generic types).
-/
module

public import Spec.google_golang_org.grpc.GenericServerStream__Send

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

/-- **Trust boundary** (W-W): `(*GenericServerStream[Req, Res]).Send(m)` (`stream_interfaces.go`): `x.ServerStream.SendMsg(m)`. -/
axiom grpc.GenericServerStream.Send.wp_proof : grpc.GenericServerStream.Send.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
