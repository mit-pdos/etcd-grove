/-
`(*Cache).WaitForNextResync(ctx)` (`cache/cache.go`): wait for the demux's next resync pass.

Users: etcd's integration tests (`TestCacheLaggingWatcher`: twice, before reading a lagging watch).
Snippet: `cache/watch.go` `ReqWatchEnds` (called before reading).

Proof sketch: `demux.WaitForNextResync.spec` (the demux's `notifier`: `notifier.wait.spec`): `nil` once
a notification happened after the call, or the context's error once done.

Changes: (round 1) a thread token, given back, for the read lock's reader slot. from `specs-ref`'s `Cache__WaitForNextResync.lean`: W0's context bundle; no internal handle.

Margin: `nil` means a resync pass completed after the call started (lagging watchers were offered
the history): no client-visible fact follows from it, so none is stated.
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

/-- **`c.WaitForNextResync(ctx)`**: `nil`, or the context's error once it is done. -/
def Cache.WaitForNextResync.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal) (pfx : GoString) (ctx : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ isCache c γ who pfx ∗ Context.ctxOk ctx ∗ threadTok }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.cache.v3.Cache.ty @!! go!"WaitForNextResync")) (Val #ctx))
  {{ (err : GoInterface), RET #err; threadTok ∗
      ⌜err = GoInterface.nil⌝ ∨ (Context.ctxDone ctx ∗ context.isCtxErr err) }}

end spec

end Cache
end EtcdGrove
end Perennial
