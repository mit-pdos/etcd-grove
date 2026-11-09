/-
`(*storeTxnCommon).rangeKeys(ctx, key, end, curRev, ro)` (`kvstore_txn.go:73`): a range of the
transaction's view at `ro.Rev` (the current revision `curRev` for `ro.Rev ≤ 0`). Internal: the
`Range`s of both transactions.

**Proof sketch**: `ro.Rev > curRev`: `ErrFutureRev` (`{nil, curRev, -1}`); `rev < s.compactMainRev`
(fixed: the transaction holds `s.mu` for reading; `txnCommon` ties it to `k.state.crev`):
`ErrCompacted` (`{nil, 0, -1}`). Count only: `treeIndex.CountRevisions.spec` (atomic over
`idxAt` (`InternalIdx.lean`), which the store's invariant keeps at the index of `k.readHist`'s events). Keys only:
`treeIndex.Range.spec`, then fresh `KeyValue`s sharing the index's key slices (read-only; value
`nil`, lease `0`: `keysOnlyM`). Full: `treeIndex.Revisions.spec`, `sliceCapWithLimit.spec`, then
for each revision a `select` on `ctx.Done()` (`Context.doneRecv`/`Done.spec`: closed only once the
context is done: the `ctxErr` arm, `nil` result) and `tr.tx.UnsafeRange(Key, revBytes, nil, 0)`
(`keyBackend`'s `rangeOk` on the snapshot `kbRead`/the batch's `kbLocked`; on a concurrent read
transaction the single-key row, `KeyData.linger`, exact for a key the snapshot has; the bytes lent
against a share of the transaction's liveness `kbLive`, which `txnCommon` holds, and given back once
unmarshalled): exactly one value,
because `txnCommon`'s realization keeps the storage's data at an image of `k.readHist` containing
every revision the index returns at a revision at or above the compaction (so `lg.Fatal("range
failed to find revision pair")` is unreachable: the pinned fork carries the doCompact fix of
`issues/etcd-compaction-delete-then-put.md`); `proto.Unmarshal` of it (2a's boundary: the encoding
the put wrote) gives `KeyValueM.ofKV` of the record. Each step steps the trace (`traceOwn`).

**Changes** from `specs-ref`'s file: over `txnCommon`, `rangeOut` (W0's history) and the context's
bundle (`Context.ctxOk`); no certificates, revision tokens or bucket maps.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.InternalTxn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI EtcdModel EtcdWire go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- A range of the transaction's view (`MTxn.readHist`) at `curRev`, its current revision. -/
def storeTxnCommon.rangeKeys.spec : Prop :=
  ∀ (c : Loc) (γ : MvccName) (trace : Loc) (k : MTxn) (ctx : GoInterface) (key endk : GoSlice)
    (kk e : Bytes) (dk de : DFrac) (curRev : w64) (ro : RangeOptions),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      txnCommon c γ trace k ∗ ⌜curRev = W64 k.readHist.rev⌝ ∗ traceOwn trace ∗ Context.ctxOk ctx ∗
      key ↦*{dk} kk ∗ endk ↦*{de} e }}
    (App (App (App (App (App (Val (c @!! go.GoType.PointerType storeTxnCommon.ty @!! go!"rangeKeys"))
      (Val #ctx)) (Val #key)) (Val #endk)) (Val #curRev)) (Val #ro))
  {{ (r : Loc) (err : GoInterface), RET (PairV #r #err);
      txnCommon c γ trace k ∗ traceOwn trace ∗ key ↦*{dk} kk ∗ endk ↦*{de} e ∗
      ∃ out : RangeOut, ⌜rangeOut k.readHist k.state.crev (mrange kk endk e) ro out⌝ ∗
        rangeResOwn ctx r err out }}

end spec
end Mvcc
end EtcdGrove
end Perennial
