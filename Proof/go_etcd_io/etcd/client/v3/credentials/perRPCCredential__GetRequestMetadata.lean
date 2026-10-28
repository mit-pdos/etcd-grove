/-
**Trust boundary**: the credentials' `GetRequestMetadata` (the auth plan's C1, 2026-10-28;
`notes/c1-plan.md`, finding 2). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.credentials.perRPCCredential__GetRequestMetadata

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.credentials.Assumptions]

/-- **Trust boundary**: `GetRequestMetadata` reads `rc.authToken` under `authTokenMu.RLock()`
and returns `nil, nil` for `""`, else `map[string]string{"token": t}, nil`
(`rpctypes.TokenFieldNameGRPC`); the token it reads is one `credTokInv` allows. Untranslated:
Perennial's `RLock` needs a reader token (or a thread token), which grpc's call for each attempt
cannot give; true of Go below `RWMutex`'s 2^30 concurrent readers. -/
axiom credentials.perRPCCredential.GetRequestMetadata.wp_proof :
  credentials.perRPCCredential.GetRequestMetadata.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
