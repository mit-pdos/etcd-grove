/-
`txn.Put` (put.go). Lean-first (no Rocq counterpart); see `Proof/.../etcdserver/txn/Write.lean`.
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

/-- **`Put(ctx, lg, lessor, kv, p)`**: the put request `o` as one write transaction, opened with a
revision token. The caller's `m` other tokens and its certificate of `log₀` pin the committed log
`ilog` the transaction finds (`Pinned`: at the sole writer, its own log, `Results.lean`); at it,
the lease the put would keep (`IgnoreLease`) is one it may attach. Either the request's lease is
not found (`lease.ErrLeaseNotFound`, no transaction: the token back); or, at `ilog`, an ignore
flag and no previous key-value (`errors.ErrKeyNotFound`: nothing written, the token back with
the certificate of `ilog`); or the put committed: `ilog` with the revision of its one change
(`putChangeOf`, the client's `putTxnOp` there: `stateAfter_put`), the response at that revision
with the previous key-value if `PrevKv` asked for it. The trace is not `nil`.
The write transaction runs under the store's batch lock by the critical-section contract
(`csContract P f Pre Q Post`, the store's hook `hookIs γ P f`): `Post` once it was opened, `Pre`
if the lease check failed first. -/
abbrev txn.Put.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (lg : Loc) (le kv : GoInterface)
    (s : Loc) (γ : mvcc.StoreNames) (p : Loc) (o : OpFull) (m : Nat) (log₀ : mvcc.Log)
    (P Pre Q Post : IProp GF) (f : val),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ txn.isKV kv s γ ∗ mvcc.storeReader s γ ∗ mvcc.revToken γ ∗
      ownToks γ.revs m ∗ mvcc.idxCert γ.idx log₀ ∗ txn.isTxnLessor le γ.leases ∗
      txn.putRequestIs p o ∗ context.isContext ctx cd ∗
      □ (∀ ilog : mvcc.Log, ⌜txn.Pinned log₀ m ilog ∧ o.ignoreLease = true⌝ -∗
        txn.leaseOk γ.leases (txn.putLeaseOf o (mvcc.findKey o.key (mvcc.stateAfter ilog)))) ∗
      mvcc.csContract P f Pre Q Post ∗ mvcc.hookIs γ P f }}
    (App (App (App (App (App (Val (@! txn.Put)) (Val #(GoInterface.ok ctx))) (Val #lg)) (Val #le))
      (Val #kv)) (Val #p))
  {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
      mvcc.storeReader s γ ∗ ownToks γ.revs m ∗ ⌜trace ≠ null⌝ ∗
      ((⌜o.leaseID ≠ W64 0 ∧ resp = null⌝ ∗
          txn.errVarIs go_etcd_io.etcd.server.v3.lease.ErrLeaseNotFound err ∗ mvcc.revToken γ ∗
          Pre) ∨
       ∃ ilog : mvcc.Log, ⌜txn.Pinned log₀ m ilog ∧ ilog ≠ []⌝ ∗ Post ∗
        ((⌜txn.needsPrev o = true ∧ mvcc.findKey o.key (mvcc.stateAfter ilog) = none ∧ resp = null⌝ ∗
            txn.errVarIs go_etcd_io.etcd.server.v3.etcdserver.errors.ErrKeyNotFound err ∗
            mvcc.revToken γ ∗ mvcc.idxCert γ.idx ilog) ∨
         (⌜err = GoInterface.nil⌝ ∗
            txn.putResponseIs resp (W64 (ilog.length : Int))
              (if o.base.prevKV then mvcc.findKey o.key (mvcc.stateAfter ilog) else none) ∗
            mvcc.idxCert γ.idx (ilog ++ [[txn.putChangeOf o (mvcc.findKey o.key (mvcc.stateAfter ilog))]]) ∗
            txn.leaseOk γ.leases (txn.putLeaseOf o (mvcc.findKey o.key (mvcc.stateAfter ilog)))))) }}

end spec

end EtcdGrove
end Perennial
