/-
`(*store).Compact(trace, rev)` (`kvstore.go:272`).

**Users**: `KV.Compact` on the server's watchable store (promoted): the apply of a compaction
(`apply/backend.go:73`), whose request `EtcdServer.Compact` (2c) requires `rev ≥ 1`. Snippets
`ReqCompact`, `ReqCompactErrors` (`examples/specreq/mvcc/compact.go`).

**Proof sketch**: `s.mu.Lock()` (`storeW`: no reader, writer or restore);
`checkPrevCompactionCompleted` (a `ReadTx` read of the compaction keys: a slot of the open token's);
`updateCompactRev(rev)` under `s.revMu`: at or below `compactMainRev`, the barrier job and
`ErrCompacted`; above `currentRev`, `ErrFutureRev` and `nil`; else the caller's update fires
(`σ.compactTo rev`: the invariant's `compactMainRev`), `SetScheduledCompact` (`LockInsideApply`:
the hook, `Pre` to `Q'`; `UnsafePut` of the scheduled key; `Unlock` with `Pk` from
`Q' ={⊤}=∗ Pk ∗ Post`) and `ForceCommit` (`X` to `Y`); in the error arms the update fires
unchanged. `s.mu.Unlock()`; `compact(...)` schedules the job (the open token's `compactJobRes`:
the job's reader slot, the delete right) and returns its channel. The open token is given back
(only its holder compacts: the marked scope restriction).

**Changes** from `specs-ref`'s `store__Compact.lean`: the contract at `*store`; any state, over W0's
history.

**Margin**: the job's deletions are not stated: they change nothing the API models.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api

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

/-- `KV.Compact`'s contract at `*store`. -/
def store.Compact.spec : Prop :=
  ∀ s : Loc, KV.Compact.contract (GF := GF) (go.GoType.PointerType store.ty) #s

end spec
end Mvcc
end EtcdGrove
end Perennial
