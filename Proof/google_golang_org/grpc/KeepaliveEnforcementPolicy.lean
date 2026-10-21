module

public import Spec.google_golang_org.grpc.KeepaliveEnforcementPolicy

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

/-- **Trust boundary** (D28): `KeepaliveEnforcementPolicy(kep)` sets the server's
`keepalivePolicy` (grpc v1.84.0): when a client's pings come faster than `MinTime` (or on an idle
connection, unless `PermitWithoutStream`), the server sends a `GOAWAY` and closes the connection.
It decides when a connection closes, never which handler runs for a method nor what a run is
given; a closed connection is an error for the client. -/
axiom grpc.KeepaliveEnforcementPolicy.wp_proof :
  grpc.KeepaliveEnforcementPolicy.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
