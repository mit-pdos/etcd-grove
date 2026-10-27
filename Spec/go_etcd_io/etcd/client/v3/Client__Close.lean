/-
`c.Close()` (`client/v3/client.go`, names only; the auth plan's E2d, 2026-10-25): `newClient` closes
the client it built when the token's fetch fails (a client with a user name, `getToken`'s
`Authenticate`).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvClientNew

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `c.Close()` on a client `clientv3.New` builds (`clientCoreAt`): it returns, with some error. -/
abbrev Client.Close.spec : Prop :=
  ∀ (c : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ clientCoreAt c }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"Close"))
      (Val #()))
  {{ (err : GoInterface), RET #err; True }}

end spec

end EtcdGrove
end Perennial
