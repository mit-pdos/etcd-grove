/-
Trust boundary: `(*grpc.ClientConn).NewStream` (an axiom; see
`Spec/google_golang_org/grpc/ClientConn__NewStream.lean`).
-/
module

public import Spec.google_golang_org.grpc.ClientConn__NewStream

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

/-- **Trust boundary** (unit W-W): a client stream through grpc's `ClientConn` is the stream
interceptor (etcd's, at no retry) over grpc's streamer, which opens a stream of a registered
streaming method: the network, grpc's client and server, the protobuf codec, the server's
runtime, which runs the method's handler on the stream's server end (`grpc.serveStream`);
`InvGrpcStream.lean`'s header states the transport's claims. -/
axiom grpc.ClientConn.NewStream.wp_proof : grpc.ClientConn.NewStream.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
