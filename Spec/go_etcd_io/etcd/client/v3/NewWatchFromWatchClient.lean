/-
`clientv3.NewWatchFromWatchClient(wc, c)` (`client/v3/watch.go`).

**Users**: `NewWatcher`; the in-process client (`E server/v3/etcdserver/api/v3client/v3client.go:40`,
over the adapter's `WatchClient`, which then must meet `remoteWatchAt`). **Proof sketch**: allocate
the `*watcher` (an empty map), read `c.callOpts` (`clientConnOk`: `callOptsOk _ false`) and
`c.GetLogger()` (1c's spec under `clientConnOk`: a logger, `Zap.isLogger`), make the lock invariant
(`watcherHandle`). **Changes** from `specs-ref/.../NewWatchFromWatchClient.lean`: over
`remoteWatchAt` and `clientConnOk`; the old `⌜c ≠ null⌝` stays, folded in `clientConnOk`: a `nil`
client gives a `nil` logger, and `run`'s `w.lg.Debug(...)` on a failed send would dereference it
(`zap.Logger.check` reads `log.core`): no caller passes `nil`. **Margin**: none.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.ApiWatch

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

/-- `NewWatchFromWatchClient(wc, c)`: a watcher over the stub `wc` with the client's call options and
logger. -/
def NewWatchFromWatchClient.spec : Prop :=
  ∀ (wc : GoInterface) (c : Loc) (γ : Cluster) (who : Principal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ remoteWatchAt wc γ who ∗
      clientConnOk c γ who }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.NewWatchFromWatchClient)) (Val #wc)) (Val #c))
  {{ (v : GoInterface), RET #v; ∃ w : Loc,
      ⌜v = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.watcher.ty) #w⌝ ∗
      watcherHandle w γ who }}

end spec

end ClientV3
end EtcdGrove
end Perennial
