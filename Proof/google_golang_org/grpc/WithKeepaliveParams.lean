module

public import Spec.google_golang_org.grpc.WithKeepaliveParams

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

/-- **Trust boundary** (D28): `WithKeepaliveParams(kp)` returns a `funcDialOption` that sets
`dopts.copts.KeepaliveParams = kp`, its `Time` raised to 10 seconds if below (grpc v1.84.0). It sets
no interceptor and no resolver. At run time the HTTP/2 transport pings after `Time` without a read
and, without an ACK within `Timeout`, closes the connection with a connection error: every stream
on it fails (`Unavailable`), which the attempt's and the streams' axioms allow; keepalive never
re-sends a request (D21j). -/
axiom grpc.WithKeepaliveParams.wp_proof : grpc.WithKeepaliveParams.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
