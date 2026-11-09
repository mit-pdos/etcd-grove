/-
`clientv3.NewLeaseFromLeaseClient` (`client/v3/lease.go`).

Users: `NewLease`; (outside scope: the gRPC proxy, with a client).

Proof sketch: allocates the lessor (fresh `donec`, map; `firstKeepAliveTimeout` from the argument),
reads the client's logger (`GetLogger`: `isLogger`) and `callOpts` (`callOptsOk _ false`), a
require-leader context (`WithRequireLeader(context.Background())`, W0's spec) and its cancellable child
(`stopCtx`); allocates the lessor's invariant (`lessorHandle`).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/NewLeaseFromLeaseClient.lean`: restated over
`clientCore`, `remoteLeaseAt`.

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
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ remoteLeaseAt remote γ who ∗ clientBase c who }}
    (App (App (App (Val (@! go_etcd_io.etcd.client.v3.NewLeaseFromLeaseClient)) (Val #remote))
      (Val #c)) (Val #t))
  {{ (v : GoInterface), RET #v; ∃ l : Loc,
      ⌜v = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty) #l⌝ ∗
      lessorHandle l null γ who }}

end spec

end ClientV3
end EtcdGrove
end Perennial
