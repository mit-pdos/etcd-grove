/-
`clientv3.NewWatchFromWatchClient(wc, c)` (`client/v3/watch.go`).

**Users**: `NewWatcher`; the in-process client (`E server/v3/etcdserver/api/v3client/v3client.go:40`,
over the adapter's `WatchClient`, which then must meet `remoteWatchAt`). **Proof sketch**: allocate
the `*watcher` (an empty map), read `c.callOpts` (`clientBase`, 1c: `callOptsOk _ false`) and
`c.GetLogger()` (`Client.GetLogger.spec` under `clientBase`: a logger, `Zap.isLogger`), make the
lock invariant (`watcherHandle`). **Changes** from `specs-ref/.../NewWatchFromWatchClient.lean`:
over `remoteWatchAt` and 1c's `clientBase` (integration: was W0's `clientConnOk`, which an
in-process client, `NewCtxClient`'s, cannot give: 1c's `clientBare_base` gives `clientBase`, as for
1c's other `From*Client` constructors); the old `⌜c ≠ null⌝` stays, folded in `clientBase`: a `nil`
client gives a `nil` logger, and `run`'s `w.lg.Debug(...)` on a failed send would dereference it
(`zap.Logger.check` reads `log.core`): no caller passes `nil`. verify-round (A2-provability W3): the stub is taken gated on the readiness of a client
`rc` (ghost: `NewWatcher` passes its `c`, whose stub works only once `c.Auth` is set; the in-process
caller passes `null` with its own `remoteWatchAt`, `clientReady_null`: its `c` is a `NewCtxClient`'s,
whose readiness `clientBare_assemble` mints only after the watcher is built), and the handle records
`rc`. **Margin**: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.ApiWatch
public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.ApiClient

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

/-- `NewWatchFromWatchClient(wc, c)`: a watcher over the stub `wc` (meeting the wire contract once
the client `rc` is ready) with the client's call options and logger. -/
def NewWatchFromWatchClient.spec : Prop :=
  ∀ (wc : GoInterface) (c rc : Loc) (γ : Cluster) (who : Principal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      □ (clientReady rc -∗ remoteWatchAt wc γ who) ∗ clientBase c who }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.NewWatchFromWatchClient)) (Val #wc)) (Val #c))
  {{ (v : GoInterface), RET #v; ∃ w : Loc,
      ⌜v = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.watcher.ty) #w⌝ ∗
      watcherHandle w rc γ who }}

end spec

end ClientV3
end EtcdGrove
end Perennial
