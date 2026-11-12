/-
`(*credentials.perRPCCredential).RequireTransportSecurity` (`client/v3/credentials/credentials.go`).

Users: grpc (at dial).

Proof sketch: `false`.

Changes: from `specs-ref`.

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

/-- `rc.RequireTransportSecurity()`: `false`. -/
def perRPCCredential.RequireTransportSecurity.spec : Prop :=
  ∀ (rc : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.credentials }}
    (App (Val (rc @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.credentials.perRPCCredential.ty @!! go!"RequireTransportSecurity")) (Val #()))
  {{ RET #false; True }}

end spec

end Credentials
end EtcdGrove
end Perennial
