/-
`(*credentials.perRPCCredentialBundle).UpdateAuthToken` (`client/v3/credentials/credentials.go`).

Users: `Client.getToken`.

Proof sketch: `b.rc` (never `nil`: `bundleAt_unfold`), `rc.UpdateAuthToken(tok)`.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/credentials/perRPCCredentialBundle__UpdateAuthToken.lean`.

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

/-- `b.UpdateAuthToken(tok)` of a token `who` may send. -/
def perRPCCredentialBundle.UpdateAuthToken.spec : Prop :=
  ∀ (b : Loc) (γ : Cluster) (who : Principal) (tok : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.credentials ∗ bundleAt (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.credentials.perRPCCredentialBundle.ty) #b) γ who ∗ tokFor γ who tok }}
    (App (Val (b @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.credentials.perRPCCredentialBundle.ty @!! go!"UpdateAuthToken")) (Val #tok))
  {{ RET #(); True }}

end spec

end Credentials
end EtcdGrove
end Perennial
