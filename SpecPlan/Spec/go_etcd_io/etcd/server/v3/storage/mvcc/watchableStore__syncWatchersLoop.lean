/-
`(*watchableStore).syncWatchersLoop()` (internal, a goroutine of `New`): `syncWatchers` while
watchers are unsynced, every `resyncDelay`, until `stopc` is closed.

**Proof sketch.** Loop invariant `wsLoopS s γ`: `s.mu.RLock` (the loop's reader) for the unsynced
count; `syncWatchers` (its spec); `time.Since`, `resyncDelay` (positive: `Ticker.Reset` does not
panic); the `select` on the ticker and `stopc`: closed, `Done` deposits the loop's reader and the
goroutine ends.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.mvcc.WatchInternal
public import SpecPlan.Spec.go_uber_org.zap.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI EtcdModel EtcdWire go_etcd_io.etcd.server.v3.storage.mvcc Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

def watchableStore.syncWatchersLoop.spec : Prop :=
  ∀ (s : Loc) (γ : MvccName),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ wsInv s γ ∗ wsLoopS s γ }}
    (App (Val (s @!! go.GoType.PointerType watchableStore.ty @!! go!"syncWatchersLoop")) (Val #()))
  {{ RET #(); True }}

end spec

end Mvcc
end EtcdGrove
end Perennial
