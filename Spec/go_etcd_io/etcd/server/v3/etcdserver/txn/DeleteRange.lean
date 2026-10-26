/-
`txn.DeleteRange` (delete.go). Lean-first (no Rocq counterpart); see `Proof/.../etcdserver/txn/Write.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Write

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-- **`DeleteRange(ctx, lg, kv, dr)`**: the delete request `o` as one write transaction, opened
with a revision token, at a committed log `ilog` the caller's other tokens and certificate pin
(`Pinned`; at the sole writer, its own log), spending a write token (until D19c, 2026-10-18,
with fewer than `mvcc.putMax γ` keys in the request's range there, which the store's receipts now
give: `mvcc.storeTxnWriteIs_small`) (`mvcc.storeWT γ`). The keys of the
request's range at `ilog`'s state deleted (`delChanges`; the client's delete there:
`stateAfter_commit_delete`): the committed log `commitLog` (no revision, the token back, if
nothing was deleted), the response with their number, the revision (`writeRev`: the new one, or
`ilog`'s last if nothing was deleted) and (`PrevKv`) the deleted key-values; or, with `PrevKv`,
the range read's context error (`ctx` done): nothing deleted, the token back. The trace is not
`nil`. The write transaction runs under the store's batch lock by the critical-section contract
(`csContract P f Pre Q Post`, the store's hook `hookIs γ P f`): `Post`. At a context never
canceled (`nd`: `neverDone`), no context error (2026-10-12: for the apply package's backend).
2026-10-14 (unit P1b): the context's trace `ot` (`ctxTraceIs`) and its ownership taken
(`EnsureTrace`); the trace returned owned, the context's if it had a non-empty one.
2026-10-14 (unit T1): the caller certifies the log the delete commits (`certOkNext`). 2026-10-17 (unit N4, D14a): `kv` the plain store or a watchable store over it (`isKV`); for a
watchable store the caller is the sole writer of the notified log `Lw` (`wlogOwn`), and gets the
writer's part back at the log it leaves. -/
abbrev txn.DeleteRange.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (nd : Bool) (lg : Loc) (kv : GoInterface)
    (s : Loc) (γ : mvcc.StoreNames) (dr : Loc) (o : OpFull) (m : Nat) (log₀ : mvcc.Log)
    (P Pre Q Post : IProp GF) (f : val) (ot : Option Loc) (te : Bool) (Lw : mvcc.Log) (L : List w64)
    (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ txn.isKV kv s γ ∗ mvcc.storeReader s γ ∗ mvcc.revToken γ ∗
      mvcc.storeWT γ ∗ ownToks γ.revs m ∗ mvcc.idxCert γ.idx log₀ ∗
      txn.wlogOwn s γ Lw ∗ ⌜γ.watchQ = true → m + 1 = txn.soleBudget Lw ∧ Lw.length + 4 ≤ 2 ^ 63⌝ ∗
      txn.deleteRangeRequestIs dr o ∗
      lease.leaseOwn γ.leases L I ∗
      □ (∀ ilog : mvcc.Log, ⌜txn.Pinned log₀ m ilog⌝ -∗
        ⌜I = mvcc.leaseItemsOf (mvcc.stateAfter ilog)⌝) ∗
      mvcc.txnCtx ctx cd ∗ traceutil.ctxTraceIs ctx ot ∗ traceutil.ownTraceOpt ot te ∗ (if nd then mvcc.neverDone cd else iprop(True)) ∗
      □ (∀ ilog : mvcc.Log, ⌜txn.Pinned log₀ m ilog⌝ -∗
        mvcc.certOkNext γ ilog (txn.delChanges (mvcc.stateAfter ilog) o)) ∗
      mvcc.csContract P f Pre Q Post ∗ mvcc.hookIs γ P f }}
    (App (App (App (App (Val (@! txn.DeleteRange)) (Val #(GoInterface.ok ctx))) (Val #lg))
      (Val #kv)) (Val #dr))
  {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
      mvcc.storeReader s γ ∗ mvcc.hookIs γ P f ∗ ownToks γ.revs m ∗ ⌜trace ≠ null⌝ ∗ Post ∗
      (∃ te' : Bool, traceutil.ownTrace trace te') ∗ ⌜∀ t0, ot = some t0 → te = false → trace = t0⌝ ∗
      ∃ ilog : mvcc.Log, ⌜txn.Pinned log₀ m ilog ∧ ilog ≠ []⌝ ∗
        ((⌜err = GoInterface.nil⌝ ∗
            txn.deleteRangeResponseIs resp
              (W64 ((mvcc.writeRev ilog (txn.delChanges (mvcc.stateAfter ilog) o) : Nat) : Int))
              (rangeIn (mvcc.stateAfter ilog) o).length
              (if o.base.prevKV then rangeIn (mvcc.stateAfter ilog) o else []) ∗
            txn.respHdrOwn (structFieldRef go_etcd_io.etcd.api.v3.etcdserverpb.DeleteRangeResponse go!"Header" resp) ∗
            mvcc.idxCert γ.idx (mvcc.commitLog ilog (txn.delChanges (mvcc.stateAfter ilog) o)) ∗
            (if txn.delChanges (mvcc.stateAfter ilog) o = [] then mvcc.revToken γ else True) ∗
            txn.wlogOwn s γ (mvcc.commitLog ilog (txn.delChanges (mvcc.stateAfter ilog) o)) ∗
            lease.leaseOwn γ.leases L (mvcc.leaseItemsOf (mvcc.stateAfter
              (mvcc.commitLog ilog (txn.delChanges (mvcc.stateAfter ilog) o))))) ∨
         (⌜err ≠ GoInterface.nil ∧ o.base.prevKV = true ∧ resp = null ∧ nd = false⌝ ∗
            mvcc.revToken γ ∗ mvcc.idxCert γ.idx ilog ∗ txn.wlogOwn s γ ilog ∗
            lease.leaseOwn γ.leases L I)) }}

end spec

end EtcdGrove
end Perennial
