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
`hookIs γ P f`): `Post`; a failed check or a read-only request takes no lock: `Pre`. -/
abbrev txn.Txn.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (lg rt : Loc) (shared : Bool)
    (kv le : GoInterface) (skip : Bool) (s : Loc) (γ : mvcc.StoreNames) (log : mvcc.Log)
    (t : TxnModel) (P Pre Q Post : IProp GF) (f : val),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ txn.isKV kv s γ ∗ mvcc.storeReader s γ ∗ txn.soleWriter γ log ∗
      txn.isTxnLessor le γ.leases ∗ txn.txnRequestIs rt t ∗ mvcc.txnCtx ctx cd ∗
      mvcc.neverDone cd ∗ txn.leasesKnown γ.leases (mvcc.stateAfter log) ∗ ⌜txn.TxnPre log t⌝ ∗
      mvcc.csContract P f Pre Q Post ∗ mvcc.hookIs γ P f }}
    (App (App (App (App (App (App (App (Val (@! txn.Txn)) (Val #(GoInterface.ok ctx))) (Val #lg))
      (Val #rt)) (Val #shared)) (Val #kv)) (Val #le)) (Val #skip))
  {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
      mvcc.storeReader s γ ∗
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
        txn.soleWriter γ (mvcc.commitLog log
          (txn.srvRunTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).2.1) ∗
        txn.leasesKnown γ.leases (mvcc.stateAfter (mvcc.commitLog log
          (txn.srvRunTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).2.1)) ∗
        (if txn.txnReadonly t then Pre else Post))) }}

end spec

end EtcdGrove
end Perennial
