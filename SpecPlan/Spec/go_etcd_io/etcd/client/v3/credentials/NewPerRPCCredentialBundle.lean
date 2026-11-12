/-
`credentials.NewPerRPCCredentialBundle` (`client/v3/credentials/credentials.go`).

Users: `newClient` (a user name and password, or a token).

Proof sketch: a fresh `perRPCCredential` (token `""`, its `RWMutex` invariant allocated with
`tokFor`), the bundle over it.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/credentials/NewPerRPCCredentialBundle.lean`.

Margin: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.credentials.Api

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

/-- `NewPerRPCCredentialBundle()`: a bundle for any principal (its token `""`). -/
def NewPerRPCCredentialBundle.spec : Prop :=
  ∀ (γ : Cluster) (who : Principal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.credentials }}
    (App (Val (@! go_etcd_io.etcd.client.v3.credentials.NewPerRPCCredentialBundle)) (Val #()))
  {{ (b : GoInterface), RET #b; bundleAt b γ who }}

end spec

end Credentials
end EtcdGrove
end Perennial
