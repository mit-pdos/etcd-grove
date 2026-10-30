/-
**Trust boundary**: the credentials' `UpdateAuthToken` (the auth plan's C1, 2026-10-28;
`notes/c1-plan.md`, finding 2). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.credentials.perRPCCredential__UpdateAuthToken

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

/-- **Trust boundary**: `UpdateAuthToken(t)` stores `t` in `rc.authToken` under
`authTokenMu.Lock()` (one store, so `credTokInv` holds throughout). Untranslated with
`GetRequestMetadata`, whose read lock Perennial cannot give per attempt. -/
axiom credentials.perRPCCredential.UpdateAuthToken.wp_proof :
  credentials.perRPCCredential.UpdateAuthToken.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
