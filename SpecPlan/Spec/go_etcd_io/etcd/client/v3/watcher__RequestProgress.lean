/-
`(*clientv3.watcher).RequestProgress(ctx)` (`client/v3/watch.go`).

**Users**: the cache's progress requestor (`E cache/v3/progress_requestor.go:94`, errors printed),
Kubernetes (`K etcd3/store.go:108` `RequestWatchProgress` with the cacher's metadata, `K
etcd3/watcher.go:303`): they wait for the progress notification on the watch whose context has
the same metadata (liveness) and use it as a bookmark (`watchStep`'s progress case). Snippet
`clientv3watch/progress.go` `ReqRequestProgress`.

**Proof sketch.** `streamKeyFromCtx.spec`; under `mu` (the lock invariant), `nil` streams → an
error from `errors.New`; else get or make the stream (`newWatcherGRPCStream.spec`), then `select`:
send a `*progressRequest` on `reqc` (`wgsAt`'s protocol: nothing travels with it), or
`ctx.Done()` (`ctx.Err()`), or `donec` (the published `closeErr`, or a recursive call: the same
spec, by Löb induction).

**Changes** from `specs-ref/.../watcher__RequestProgress.lean`: over `watcherHandle` and any
context. verify-round (A2-provability W2, W3): over `watcherHandle w c γ who` and `clientReady c`
(it may open a stream: `newWatcherGRPCStream.spec` takes it); `streamKeyFromCtx.spec` with the
caller's `ctxPrin` (a joined stream's principal from `ctxStreamKey_prin`, as in `Watch`).
**Margin**: the error's value is not modelled (every user only logs or returns it).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.ApiWatch

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

/-- `watcher.RequestProgress` meets `Watcher.RequestProgressTriple`. -/
def watcher.RequestProgress.spec : Prop :=
  ∀ (w c : Loc) (γ : Cluster) (who : Principal),
  Watcher.RequestProgressTriple (w @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watcher.ty @!! go!"RequestProgress")
    (iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ watcherHandle w c γ who ∗
      clientReady c)) who

end spec

end ClientV3
end EtcdGrove
end Perennial
