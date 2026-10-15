/-
Trust boundary: `(*GenericServerStream[Req, Res]).Recv()` (an axiom; see
`Spec/google_golang_org/grpc/GenericServerStream__Recv.lean`: Goose does not translate methods of generic types).
-/
module

public import Spec.google_golang_org.grpc.GenericServerStream__Recv

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

/-- **Trust boundary** (W-W): `(*GenericServerStream[Req, Res]).Recv()` (`stream_interfaces.go`): `m := new(Req)`, then `x.ServerStream.RecvMsg(m)`; `(m, nil)` if it returns `nil`, else `(nil, err)`. -/
axiom grpc.GenericServerStream.Recv.wp_proof : grpc.GenericServerStream.Recv.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
