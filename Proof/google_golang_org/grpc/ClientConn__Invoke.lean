/-
**Trust boundary**: grpc's `(*ClientConn).Invoke` of the KV service's `Put` and `Range`, the
retry interceptor included (an axiom; see `Spec/google_golang_org/grpc/ClientConn__Invoke.lean`
and `notes/decisions.md`, "The client meets the server (unit C1)").
-/
module

public import Spec.google_golang_org.grpc.ClientConn__Invoke

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
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **Trust boundary**: a unary call of the KV service through grpc's `ClientConn` (the
network, the gRPC client and server, the client's retry interceptor, the server's
runtime) is a run of the server's handler on a copy of the request, whose reply the
client receives as a copy, or an error. -/
axiom grpc.ClientConn.Invoke.wp_proof : grpc.ClientConn.Invoke.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
