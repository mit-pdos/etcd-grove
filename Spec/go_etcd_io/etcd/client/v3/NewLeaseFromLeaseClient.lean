/-
`clientv3.NewLeaseFromLeaseClient` (`client/v3/lease.go`).

Users: `NewLease` (`cr = c`: the retry wrapper over the client being built, ready only once
`newClient` sets `c.Auth`); the in-process client (`v3client.New`, `cr = null`: the adapter's
remote needs no readiness; snippet `clientv3client/inproc.go`); (outside scope: the gRPC proxy, with
a client).

Proof sketch: allocates the lessor (fresh `donec`, map; `firstKeepAliveTimeout` from the argument),
reads the client's logger (`GetLogger`: `isLogger`) and `callOpts` (`callOptsOk _ false`), a
require-leader context (`WithRequireLeader(context.Background())`, W0's spec) and its cancellable child
(`stopCtx`); allocates the lessor's invariant (`lessorHandle`), which keeps the remote's
readiness-gated contract and its per-member form (`remoteVia`) for the methods to use once
`clientReady cr` holds (`lessorHandle_leaseAt`).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/NewLeaseFromLeaseClient.lean`: restated over
`clientCore`, `remoteLeaseAt`.
verify-round (A2-provability L1): the remote's contract is taken gated by the readiness of the
handle's client `cr` (`□ (clientReady cr -∗ remoteLeaseAt …)`), and the handle records `cr`, the
caller's choice of `c` or `null`: `NewLease` passes its client (`retryLeaseHandle_remoteLeaseAt`
needs `clientReady c`, which `newClient` mints only after `c.Auth` is set) and gets `lessorHandle l c`
(the post `NewLease.spec` promises); the in-process client passes `null`, its adapter's contract
holding at once, so that `lessorHandle_leaseAt` needs no `clientReady c` before
`clientBare_assemble` mints it. The per-member form (A2-provability L2): `remoteVia` of the remote
once `cr` is frozen at an endpoint (trivial for `cr = null`: `epsTok_null`).

Margin: **a `nil` client is excluded**: the lessor's `lg` stays `nil`, and the receive and send loops
call `l.lg.Warn` on a stream error, which dereferences the `nil` logger (zap's `Logger.Warn` reads
`log.core`): a panic once a lessor made so has a keep-alive and its stream fails. Found by code
reading (batch 1c, `notes/specs-only/batch-1c.md`); `recvKeepAlive` guards its `Warn` with
`l.lg != nil`, the loops do not.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.ApiLease

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ClientV3

open Iris Iris.BI EtcdModel EtcdWire
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `NewLeaseFromLeaseClient(remote, c, timeout)`: a lessor over `remote` with `c`'s logger and
options. -/
def NewLeaseFromLeaseClient.spec : Prop :=
  ∀ (remote : GoInterface) (c : Loc) (γ : Cluster) (who : Principal) (t : w64),
  ∀ cr : Loc, (cr = c ∨ cr = null) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      □ (clientReady cr -∗ remoteLeaseAt remote γ who) ∗
      □ (∀ ep, clientVia cr ep -∗ remoteVia remote ep) ∗ clientBase c who }}
    (App (App (App (Val (@! go_etcd_io.etcd.client.v3.NewLeaseFromLeaseClient)) (Val #remote))
      (Val #c)) (Val #t))
  {{ (v : GoInterface), RET #v; ∃ l : Loc,
      ⌜v = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty) #l⌝ ∗
      lessorHandle l cr γ who }}

end spec

end ClientV3
end EtcdGrove
end Perennial
