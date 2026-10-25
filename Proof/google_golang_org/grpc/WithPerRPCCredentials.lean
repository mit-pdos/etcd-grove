/-
**Trust boundary**: `grpc.WithPerRPCCredentials(creds)` returns a dial option adding per-RPC
credentials (an axiom; see `Spec/google_golang_org/grpc/WithPerRPCCredentials.lean`). Lean-first (no
Rocq counterpart).
-/
module

public import Spec.google_golang_org.grpc.WithPerRPCCredentials

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

/-- **Trust boundary** (the auth plan's E2d): `WithPerRPCCredentials(creds)` returns a
`funcDialOption` that appends `creds` to `dopts.copts.PerRPCCredentials` (grpc v1.84.0). It sets no
interceptor and no resolver. At run time the transport calls each credentials'
`GetRequestMetadata` for every stream and adds the pairs to the stream's headers, failing the
stream with its error (`Unauthenticated`/`Unavailable`), which the attempt's and the streams' axioms
allow; `NewClient` fails the dial if credentials require transport security on an insecure
connection, which its axiom allows (etcd's do not: `RequireTransportSecurity` is `false`). -/
axiom grpc.WithPerRPCCredentials.wp_proof : grpc.WithPerRPCCredentials.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
