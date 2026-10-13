/-
`storeTxnCommon__rangeKeys` (`kvstore_txn.go`). Lean-first (no Rocq counterpart); see `InvStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.TxnRange

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `txc.rangeKeys(ctx, key, end, curRev, ro)` of a transaction at revision `curRev` of the log
`log` answers `rangeOutcome`: the index's answers at that revision, with the key-values the
bucket holds for them. What it uses of the `storeTxnCommon` at `txc`: its fields `s`, `tx` and
`trace` (at any fraction, given back); of its reader `tx`: a reader (`keyReader`) of a bucket
`m` holding `log`'s, with the reader's own resource `R` (given back); of the index: what the
transaction knows of it (`idxKnows`: a committed log's certificate for a read transaction,
the writer's handle for a write transaction, with its pending revision; given back), and
`curRev` a revision of `log`. The context is an `isContext` or `context.TODO()`'s (`rangeCtx`,
`TxnRange.lean`), which is never done: at it, the result is not `nil` (no context error).
The compaction revision `c` (`compactMainRev`, read under `s.mu`, which the transaction holds
shared: part of its points-to and of the revision's authority, given back) makes a read below
it `ErrCompacted` (`rangeOutcomeC`; 2026-10-13, compaction's unit 5a). -/
abbrev mvcc.storeTxnCommon.rangeKeys.spec : Prop :=
  ∀ (txc s trace ti : Loc) (rt : GoInterfaceOk) (dq : DFrac) (m : mvcc.Bucket) (R : IProp GF)
    (γ : mvcc.StoreNames) (kn : mvcc.IdxKnow) (log : mvcc.Log) (rev : w64)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (todo : Bool)
    (key endk : GoSlice) (k e : GoString) (ro : RangeOptions) (qm qc : Qp) (c : Int),
  trace ≠ null →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isStore s γ ∗
      txc.[storeTxnCommon, go!"s"] ↦{dq} s ∗
      txc.[storeTxnCommon, go!"tx"] ↦{dq} (GoInterface.ok rt : GoInterface) ∗
      txc.[storeTxnCommon, go!"trace"] ↦{dq} trace ∗
      mvcc.keyReader rt m R ∗ R ∗ ⌜GMap.Subseteq (mvcc.bucketMap log) m⌝ ∗
      mvcc.idxKnows γ.idx kn ∗ ⌜kn.log = log⌝ ∗ ⌜log ≠ []⌝ ∗
      ⌜0 ≤ sint.Z rev ∧ sint.Z rev < log.length⌝ ∗
      s.[store, go!"kvindex"] ↦□ (interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti : GoInterface) ∗
      mvcc.idxReader ti γ.idx ∗ mvcc.rangeCtx todo ctx cd ∗ key ↦*□ k ∗ endk ↦*□ e ∗
      s.[store, go!"compactMainRev"] ↦{DFrac.own qm} (W64 c : w64) ∗ mvcc.crevUB γ.idx qc c ∗
      ⌜-1 ≤ c ∧ c < 2 ^ 63⌝ }}
    (App (App (App (App (App (Val (txc @!! go.GoType.PointerType storeTxnCommon.ty @!!
      go!"rangeKeys")) (Val #(GoInterface.ok ctx))) (Val #key)) (Val #endk)) (Val #rev)) (Val #ro))
  {{ (r : Loc) (err : GoInterface), RET (PairV #r #err);
      ⌜todo = true → r ≠ null⌝ ∗
      txc.[storeTxnCommon, go!"s"] ↦{dq} s ∗
      txc.[storeTxnCommon, go!"tx"] ↦{dq} (GoInterface.ok rt : GoInterface) ∗
      txc.[storeTxnCommon, go!"trace"] ↦{dq} trace ∗
      R ∗ mvcc.idxKnows γ.idx kn ∗ mvcc.idxReader ti γ.idx ∗
      s.[store, go!"compactMainRev"] ↦{DFrac.own qm} (W64 c : w64) ∗ mvcc.crevUB γ.idx qc c ∗
      mvcc.rangeOutcomeC r err log rev c (decide (endk = slice.nil)) k e ro }}

end spec

end EtcdGrove
end Perennial
