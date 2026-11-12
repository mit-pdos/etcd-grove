/-
# mvcc's transactions' internals (batch 3e): the vocabulary of `kvstore_txn.go`'s helpers

Imported by mvcc's own spec files only.

* `txnCommon c γ trace k` (exclusive): `c` is a `*storeTxnCommon` (the embedded part of a
  `storeTxnRead` or `storeTxnWrite`) of a transaction at `k`: its `s` (an `isStore`), its `tx` (a
  read transaction's snapshot `kbRead`, or the batch's `kbLocked`, with its liveness `kbLive`, a share
  of which each range lends), its `firstRev`/`rev` fields
  (`MTxn`'s compaction and current revision for a read transaction, `0`/`0` for a write one), its
  `trace`; and, in the realization, `s.mu` held for reading and the index and the storage's data at
  the image of `k.readHist` (so `rangeKeys` never reaches its `lg.Fatal`: every revision the index
  returns is in the storage the transaction sees). `storeTxnR_common`/`storeTxnW_common` lend it from
  the whole transaction.
* `storeTxnWNC t γ trace σ pend` (exclusive): a `*storeTxnWrite` whose change records were handed
  out (`Changes`): what `End` takes (`storeTxnW_nc` drops them).
* `changesSl t sl` (persistent): `sl` is `t`'s `changes` slice (`Changes`' result);
  `storeTxnW_changes` hands out the records (`keyValueOwn` of each, `changesM`).
* `changesM σ pend`: the change records' models: a put's key-value, a delete's key alone (zero
  revisions and version: `delete` writes `KeyValue{Key: key}`; the watchable store writes its
  `ModRevision` later).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI EtcdModel EtcdWire
open go_etcd_io.etcd.server.v3.storage.mvcc

section pure
variable [GooseExts]

/-- The record of one change (`tw.changes`' element). -/
def changeM : Event → KeyValueM
  | .put k r => KeyValueM.ofKV (KV.ofRec k r)
  | .delete k => { key := k, createRevision := W64 0, modRevision := W64 0, version := W64 0,
                   value := [], lease := W64 0 }

/-- The change records of a write transaction's events. -/
def changesM (pend : List Event) : List KeyValueM := pend.map changeM

end pure

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- `c` is the common part of a transaction at `k` (exclusive). -/
opaque txnCommon [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (c : Loc) (γ : MvccName) (trace : Loc) (k : MTxn) : IProp GF := iprop(True)

/-- A `*storeTxnWrite` whose change records were handed out (exclusive). -/
opaque storeTxnWNC [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (t : Loc) (γ : MvccName) (trace : Loc) (σ : MvccState) (pend : List Event) :
    IProp GF := iprop(True)

/-- `sl` is `t`'s change slice (persistent). -/
opaque changesSl [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (t : Loc) (sl : GoSlice) : IProp GF := iprop(True)

end vocab

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

def changesSl_persistent.spec : Prop := ∀ t sl, Persistent (changesSl (GF := GF) t sl)

/-- A read transaction's common part, lent. -/
def storeTxnR_common.spec : Prop :=
  ∀ (t : Loc) γ trace σ, storeTxnR (GF := GF) t γ trace σ ⊢
    txnCommon (structFieldRef storeTxnRead go!"storeTxnCommon" t) γ trace (.read σ) ∗
    (txnCommon (structFieldRef storeTxnRead go!"storeTxnCommon" t) γ trace (.read σ) -∗
      storeTxnR t γ trace σ)

/-- A write transaction's common part, lent (at its events so far). -/
def storeTxnW_common.spec : Prop :=
  ∀ (t : Loc) γ trace σ pend, storeTxnW (GF := GF) t γ trace σ pend ⊢
    txnCommon (structFieldRef storeTxnWrite go!"storeTxnCommon" t) γ trace (.write σ pend) ∗
    (txnCommon (structFieldRef storeTxnWrite go!"storeTxnCommon" t) γ trace (.write σ pend) -∗
      storeTxnW t γ trace σ pend)

/-- The change records handed out. -/
def storeTxnW_changes.spec : Prop :=
  ∀ (t : Loc) γ trace σ pend sl, storeTxnW (GF := GF) t γ trace σ pend ∗ changesSl t sl ⊢
    storeTxnWNC t γ trace σ pend ∗ msgsOwn keyValueOwn sl (DFrac.own 1) (changesM pend)

/-- **The change records of a plain write transaction taken** (3f's `watchableStoreTxnWrite.End`:
`tw.Changes()`, the records, which it rewrites, then `tw.TxnWrite.End()`): only of the
`*metricsTxnWrite` handle `store.Write` returns (the watchable one's `End` reads the records itself). -/
def mvccTxn_changes.spec : Prop :=
  ∀ (mw : Loc) γ trace σ pend sl,
    mvccTxn (GF := GF) (interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw) γ trace
        (.write σ pend) ∗
      mvccTxnChs (interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw) sl ⊢
      mvccTxnNC (interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw) γ trace σ pend ∗
        msgsOwn keyValueOwn sl (DFrac.own 1) (changesM pend)

/-- Dropping the change records. -/
def storeTxnW_nc.spec : Prop :=
  ∀ (t : Loc) γ trace σ pend, storeTxnW (GF := GF) t γ trace σ pend ⊢ storeTxnWNC t γ trace σ pend

end laws

end Mvcc
end EtcdGrove
end Perennial
