/-
`Txn` (`txn.go`). Lean-first; see `TxnRun.lean`, `InvTxn.lean`, `SoleWriter.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.InvTxn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.SoleWriter

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3.etcdserver.txn
  go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-- **`Txn(ctx, lg, rt, sharedBuf, kv, lessor, skip)` at the sole writer** of the committed log
`log` (the apply thread; `soleWriter`), at a context never canceled, the request `rt` denoting
`t`: either one of `checkTxn`'s errors (no response, no trace, nothing written, the sole writer
unchanged), or the server's transaction (`srvRunTxn`: the comparisons' verdict and the chosen
branch's run, nested branches by their verdicts at the state after `log`) at the next revision
on the state after `log`, committed (`soleWriter` of `commitLog log chs`; nothing for a
read-only request, which runs on the read transaction), its response with header revision
`writeRev log chs` (`skip`: ranges header-only), the state's leases still known. Premises
(`TxnPre`): room for a revision, the run's premises (`OpsOk`, weak: an `IgnoreValue`/`IgnoreLease`
put whose key is missing at `log` fails the check instead), room for the run's changes; and every
lease of the state after `log` known (`leasesKnown`). A write request's transaction runs under the
store's batch lock by the critical-section contract (`csContract P f Pre Q Post`, the store's hook
`hookIs γ P f`): `Post`; a failed check or a read-only request takes no lock: `Pre`. A success's
response header has its id fields owned (`respHdrOwn`: `newTxnResp` allocates it, the gRPC
layer's `header.fill` writes them; 2026-10-12, the request path's unit 3b). It spends a write
token (`mvcc.storeWT γ`, whether or not it writes; 2026-10-13, unit 6). -/
abbrev txn.Txn.specSole : Prop :=
  ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (lg rt : Loc) (shared : Bool)
    (kv le : GoInterface) (skip : Bool) (s : Loc) (γ : mvcc.StoreNames) (log : mvcc.Log)
    (t : TxnModel) (P Pre Q Post : IProp GF) (f : val) (L : List w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ txn.isKV kv s γ ∗ mvcc.storeReader s γ ∗ txn.soleWriter γ log ∗
      mvcc.storeWT γ ∗ txn.isTxnLessor le γ.leases ∗ txn.txnRequestIs rt t ∗ mvcc.txnCtx ctx cd ∗
      mvcc.neverDone cd ∗ txn.leasesKnown L (mvcc.stateAfter log) ∗ lease.lessorUser γ.leases L ∗
      ⌜txn.TxnPre log t⌝ ∗
      mvcc.csContract P f Pre Q Post ∗ mvcc.hookIs γ P f }}
    (App (App (App (App (App (App (App (Val (@! txn.Txn)) (Val #(GoInterface.ok ctx))) (Val #lg))
      (Val #rt)) (Val #shared)) (Val #kv)) (Val #le)) (Val #skip))
  {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
      mvcc.storeReader s γ ∗ lease.lessorUser γ.leases L ∗
      ((⌜resp = null ∧ trace = null ∧ err ≠ GoInterface.nil⌝ ∗ txn.checkErrIs err ∗
          txn.soleWriter γ log ∗ Pre) ∨
       (⌜err = GoInterface.nil ∧ trace ≠ null ∧
          (txn.txnReadonly t = true →
            (txn.srvRunTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).2.1 = [])⌝ ∗
        txn.txnResponseIs skip resp
          (W64 (mvcc.writeRev log (txn.srvRunTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).2.1
            : Int)) t
          (txn.srvRunTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).1
          (txn.srvRunTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).2.2 ∗
        txn.respHdrOwn (structFieldRef etcdserverpb.TxnResponse go!"Header" resp) ∗
        txn.soleWriter γ (mvcc.commitLog log
          (txn.srvRunTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).2.1) ∗
        txn.leasesKnown L (mvcc.stateAfter (mvcc.commitLog log
          (txn.srvRunTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).2.1)) ∗
        (if txn.txnReadonly t then Pre else Post))) }}

/-- **`Txn(ctx, lg, rt, sharedBuf, kv, lessor, skip)` at a reader** (2026-10-12, the request
path's unit 3b: the server's read-only transaction, `EtcdServer.Txn` through `doSerialize`): a
read-only request `rt` denoting `t` (`txnReadonly`), on the store `kv` with a reader's slots
(`storeReader`), `m` revision tokens and a certificate of `log₀`, at any context (`txnCtx`: it
may be done). The read transaction reads a committed log `log` pinned between `log₀` and the
tokens (`store.Read`), and the answer is one of `checkTxn`'s errors (no response, no trace); or
the server's run of `t` on the state after `log` (`srvRunTxn`: no change, a read-only request),
its response with header revision `log`'s last (`log.length - 1`), its header's id fields owned
(`respHdrOwn`); or, the context done during a range, `executeTxn`'s `fmt.Errorf` error
(`mvcc.errorfIs`; the response, partly filled, is returned too but unspecified). Premises: the
gets within the model (`txnGetsOk`: revision `0`, a sort not cut early, a valid sort target),
and the sort's premise (`LogSmall`) of the certified logs the read may see. -/
abbrev txn.Txn.specRead : Prop :=
  ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (lg rt : Loc) (shared : Bool)
    (kv le : GoInterface) (skip : Bool) (s : Loc) (γ : mvcc.StoreNames) (m : Nat)
    (log₀ : mvcc.Log) (t : TxnModel),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗
      txn.isKV kv s γ ∗ mvcc.storeReader s γ ∗ ownToks γ.revs m ∗ mvcc.idxCert γ.idx log₀ ∗
      txn.isTxnLessor le γ.leases ∗ txn.txnRequestIs rt t ∗ mvcc.txnCtx ctx cd ∗
      ⌜lg ≠ null ∧ txn.txnReadonly t = true ∧ txn.txnGetsOk t⌝ ∗
      (□ ∀ log : mvcc.Log, ⌜log₀ <+: log ∧ log.length + m + 3 ≤ 2 ^ 63⌝ -∗
        mvcc.idxCert γ.idx log -∗ ⌜txn.LogSmall log⌝) }}
    (App (App (App (App (App (App (App (Val (@! txn.Txn)) (Val #(GoInterface.ok ctx))) (Val #lg))
      (Val #rt)) (Val #shared)) (Val #kv)) (Val #le)) (Val #skip))
  {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
      mvcc.storeReader s γ ∗ ownToks γ.revs m ∗
      ∃ log : mvcc.Log, mvcc.idxCert γ.idx log ∗
        ⌜log₀ <+: log ∧ log.length + m + 3 ≤ 2 ^ 63 ∧ log ≠ []⌝ ∗
        ((⌜resp = null ∧ trace = null ∧ err ≠ GoInterface.nil⌝ ∗ txn.checkErrIs err) ∨
         (⌜err = GoInterface.nil ∧ trace ≠ null⌝ ∗
           txn.txnResponseIs skip resp (W64 ((log.length : Int) - 1)) t
             (txn.srvRunTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).1
             (txn.srvRunTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).2.2 ∗
           txn.respHdrOwn (structFieldRef etcdserverpb.TxnResponse go!"Header" resp)) ∨
         (⌜trace ≠ null⌝ ∗ mvcc.errorfIs err)) }}

/-- **`Txn`'s spec**: at the sole writer (`specSole`, the apply thread) and at a reader
(`specRead`, the server's read-only transactions); one function's two triples, by caller
(2026-10-12, the request path's unit 3b). -/
abbrev txn.Txn.spec : Prop := txn.Txn.specSole (GF := GF) ∧ txn.Txn.specRead (GF := GF)

end spec

end EtcdGrove
end Perennial
