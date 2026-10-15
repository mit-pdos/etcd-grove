/-
Trust boundary: `(*GenericClientStream[Req, Res]).Recv()` (an axiom; see
`Spec/google_golang_org/grpc/GenericClientStream__Recv.lean`: Goose does not translate methods of generic types).
-/
module

public import Spec.google_golang_org.grpc.GenericClientStream__Recv

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

/-- **Trust boundary** (W-W): `(*GenericClientStream[Req, Res]).Recv()` (`stream_interfaces.go`): `m := new(Res)`, then `x.ClientStream.RecvMsg(m)`; `(m, nil)` if it returns `nil`, else `(nil, err)`. -/
axiom grpc.GenericClientStream.Recv.wp_proof : grpc.GenericClientStream.Recv.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
