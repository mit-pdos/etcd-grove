/-
`c.getToken(ctx)` (`client/v3/client.go`, names only; unit P3a): the client's auth part (the
retry interceptor's `refreshToken`): with a token, `c.authTokenBundle.UpdateAuthToken(c.Token)`;
with a user name and password, `c.Auth.Authenticate` (a gRPC call through the same connection, its
retry interceptor included) and the bundle's update. (Item 5, client construction, 2026-10-17:
with no user name, `nil`: `newClient` calls it with no credentials and closes the client on an
error.)
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvRetry
public import Proof.go_etcd_io.etcd.client.v3.InvClientAuth

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3
open go_etcd_io.etcd.cache.v3 (statusErrOk)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `c.getToken(ctx)` on a client `clientv3.New` built (`retryClientOk`: a bundle whenever a
token), ready (`clientReady`: its `Auth` over the connection `conn` to `eps`; the bundle's tokens
`""` or meeting some `P`, and `Authenticate`'s reply to its user name and password a token meeting
`P`: the token it stores keeps the bundle's invariant, `clientAuthAt`) returns `nil` or a client error grpc's `status` accepts (`clientErrOk`: `Authenticate`'s,
through the client's retry interceptor). -/
abbrev Client.getToken.spec : Prop :=
  ∀ (c conn : Loc) (eps : List GoString) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ retryClientOk c ∗
      -- (the auth plan's C1, 2026-10-28) the client ready (`c.Auth` over `conn`, the token's
      -- facts), its connection (later: the retry interceptor's refresh path calls this under its
      -- own induction hypothesis)
      clientReady c conn eps ∗ ▷ isEtcdConn conn eps ∗ ctxOk ctx cd }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"getToken"))
      (Val #(GoInterface.ok ctx)))
  {{ (err : GoInterface), RET #err; clientErrOk err ∗
      -- (item 5) with no user name (read-only), `nil`: a token is set without a call, and no
      -- token and no user name returns at once
      □ (structFieldRef go_etcd_io.etcd.client.v3.Client go!"Username" c ↦□ ([] : GoString) -∗
        ⌜err = GoInterface.nil⌝) }}

end spec

end EtcdGrove
end Perennial
