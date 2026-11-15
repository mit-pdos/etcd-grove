/-
`(*store).Range(ctx, key, end, ro)` (`kv_view.go:38`). Promoted from the store's `ReadView` field (`&readView{s}`, set by `NewStore`, read-only): the method value at `*store` is `readView.Range` on that field.

**Users**: `KV.Range` on the server's store: `applierV3backend.Compaction`'s header revision
(`apply/backend.go:78`: only `rr.Rev` is read, the result never `nil` under `context.TODO()`'s
`ctxOk`), the watch server's previous key-value (`v3rpc/watch.go`, 2b's item 5: a read at
`ModRevision - 1`). Snippet `ReqViews`.

**Proof sketch**: `Read(ConcurrentReadTxMode, TODO())` (the caller's update fired at its LP), the
transaction's `Range` (`Txn.Range.contract` at `*metricsTxnWrite`, over `.read σ`:
`rangeOut σ.kv σ.crev`), the deferred `End()`.

**Changes** from `specs-ref`'s `readView__Range.lean` (its client form): the contract at `*store`,
over W0's history, any context (`Context.ctxOk`).

**Margin**: none.
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

/-- `KV.Range`'s contract at `*store`. -/
def store.Range.spec : Prop :=
  ∀ s : Loc, KV.Range.contract (GF := GF) (go.GoType.PointerType store.ty) #s

end spec
end Mvcc
end EtcdGrove
end Perennial
