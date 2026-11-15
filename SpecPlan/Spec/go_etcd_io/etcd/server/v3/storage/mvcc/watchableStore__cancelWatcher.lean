/-
`(*watchableStore).cancelWatcher(wa)` (internal; the cancel closure): removes the watcher from
its group, or from its victim batch (retrying, with a sleep, while `moveVictims` holds it); `ch`
cleared. Idempotent (a second call finds `ch` `nil`).

**Proof sketch.** Under `s.mu`: `unsynced.delete`, `synced.delete` (`watcherGroup.delete`), the
record's `ch`, `compacted`; else the victim batches (the invariant: a watcher out of the groups,
not compacted and not cancelled, is a victim, in a batch of `victims` or held by `moveVictims`: the
`panic` unreachable); `time.Sleep` and retry. After it no response of the watcher is sent: the
sends so far bound them (`wsCanceled`).
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

def watchableStore.cancelWatcher.spec : Prop :=
  ∀ (s : Loc) (γ : MvccName) (ι : WsNames) (wa : Loc) (id : w64) (W : WatcherM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ wsInv s γ ∗ watcherAt wa ι id W }}
    (App (Val (s @!! go.GoType.PointerType watchableStore.ty @!! go!"cancelWatcher")) (Val #wa))
  {{ RET #(); ∃ n : Nat, wsCanceled ι id n }}

end spec

end Mvcc
end EtcdGrove
end Perennial
