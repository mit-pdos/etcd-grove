/-
`(*credentials.perRPCCredential).UpdateAuthToken` (`client/v3/credentials/credentials.go`).

Users: the bundle's `UpdateAuthToken`.

Proof sketch: `authTokenMu.Lock` (its invariant: the token with `tokFor`), the write, `Unlock`.

Changes: from `specs-ref`.

Margin: none.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.credentials.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Credentials

open Iris Iris.BI EtcdModel ClientV3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.credentials.Assumptions]

/-- `rc.UpdateAuthToken(tok)`. -/
def perRPCCredential.UpdateAuthToken.spec : Prop :=
  ∀ (rc : Loc) (γ : Cluster) (who : Principal) (tok : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.credentials ∗ rpcCredsAt (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.credentials.perRPCCredential.ty) #rc) γ who ∗ tokFor γ who tok }}
    (App (Val (rc @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.credentials.perRPCCredential.ty @!! go!"UpdateAuthToken")) (Val #tok))
  {{ RET #(); True }}

end spec

end Credentials
end EtcdGrove
end Perennial
