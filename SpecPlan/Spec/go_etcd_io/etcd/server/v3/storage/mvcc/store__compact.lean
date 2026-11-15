/-
`(*store).compact(trace, rev, prevCompactRev, prevCompactionCompleted)` (`kvstore.go:234`).
Internal: `Compact` and `compactLockfree`, after `updateCompactRev` succeeded.

**Proof sketch**: `make(chan struct{})` (its close right, `compactCh`, to the job); `NewJob` of the
closure (`Schedule.funcOk`: under the scheduler's context, `schedCtx ... (storeStopped s γ)`, it runs
`scheduleCompaction` with `compactJobRes`, then `s.hashes.Store` and `close(ch)`, or the barrier on
an error or a done context); `s.fifoSched.Schedule(j)` (`schedRight`: the open token's share, so not
after `Close`); `trace.Step`.

**Changes** from `specs-ref`'s file: over `InternalStore.lean` (`schedRight`, `compactJobRes`); the
channel's contract the API's `compactChanOk`.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.mvcc.InternalStore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `s.compact(trace, rev, prev, pcc)`: the compaction job at `rev` scheduled; its channel. -/
def store.compact.spec : Prop :=
  ∀ (s : Loc) (γ : MvccName) (trace : Loc) (rev prev : w64) (pcc : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ isStore s γ ∗
      schedRight s γ ∗ compactJobRes s γ rev prev ∗ ⌜trace ≠ null⌝ ∗ traceOwn trace }}
    (App (App (App (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"compact")) (Val #trace))
      (Val #rev)) (Val #prev)) (Val #pcc))
  {{ (ch : GoChan), RET #ch; schedRight s γ ∗ traceOwn trace ∗ compactChanOk ch }}

end spec
end Mvcc
end EtcdGrove
end Perennial
