/-
`(*credentials.perRPCCredentialBundle).PerRPCCredentials` (`client/v3/credentials/credentials.go`).

Users: `Client.dial` (`grpc.WithPerRPCCredentials`).

Proof sketch: returns `b.rc` (`bundleAt_unfold`).

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

/-- `b.PerRPCCredentials()`: the credentials attaching `who`'s tokens. -/
def perRPCCredentialBundle.PerRPCCredentials.spec : Prop :=
  ∀ (b : Loc) (γ : Cluster) (who : Principal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.credentials ∗ bundleAt (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.credentials.perRPCCredentialBundle.ty) #b) γ who }}
    (App (Val (b @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.credentials.perRPCCredentialBundle.ty @!! go!"PerRPCCredentials")) (Val #()))
  {{ (v : GoInterface), RET #v; rpcCredsAt v γ who }}

end spec

end Credentials
end EtcdGrove
end Perennial
