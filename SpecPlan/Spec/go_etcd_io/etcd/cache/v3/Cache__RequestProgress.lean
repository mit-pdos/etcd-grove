/-
`(*Cache).RequestProgress(ctx)` (`cache/cache.go`): a progress notification to every active watcher.

Users: `examples/etcd/cache/cachekv.go` (`c.RequestProgress(wctx)`, then `awaitProgress`); etcd's
`TestCacheRequestProgress`. Snippet: `cache/watch.go` `ReqProgressQuiet`.

Proof sketch: `demux.BroadcastProgress.spec`: under the demux's lock, a notification at the demux's
latest revision to each active watcher, which the demux's invariant certifies quiet from the
watcher's position (every batch from it up to the latest revision was enqueued to it).

Changes: from `specs-ref`'s `Cache__RequestProgress.lean`: no internal handle; the context is unused
(any value).

Margin: whether a notification is sent (the cache is ready, the watcher active, its buffer not
full) is not stated: a consumer waits for one (`cachekv`'s `awaitProgress` returns `WatchEnded` if
the channel closes first).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.cache.v3.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Cache

open Iris Iris.BI EtcdModel EtcdWire ClientV3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- **`c.RequestProgress(ctx)`**: always `nil`. -/
def Cache.RequestProgress.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal) (pfx : GoString) (ctx : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ isCache c γ who pfx }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.cache.v3.Cache.ty @!! go!"RequestProgress")) (Val #ctx))
  {{ RET #GoInterface.nil; True }}

end spec

end Cache
end EtcdGrove
end Perennial
