/-
`Range` (`range.go`): a range request on the store.
Lean-first; see `InvRange.lean`, `RangeModel.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.InvRange
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.TxnRange

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3.etcdserver.txn
  go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-- `Range(ctx, lg, kv, r, withTotalCount)` on the store `kv`: a read transaction of a
committed log `log` pinned between the caller's certificate `log₀` and its `m` revision tokens
(`store.Read`), at its last revision `rev`, and `rangeResult` there; the trace is not `nil`.
Premises: a valid sort target, and the sort's premise (`sortOk`) on every log the read may
see. -/
abbrev txn.Range.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (lg : Loc) (kv : GoInterface)
    (s : Loc) (γ : mvcc.StoreNames) (r : Loc) (o : OpFull) (withTotal : Bool) (m : Nat)
    (log₀ : mvcc.Log),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗
      txn.isKV kv s γ ∗ mvcc.storeReader s γ ∗ ownToks γ.revs m ∗ mvcc.idxCert γ.idx log₀ ∗
      txn.rangeRequestIs r o ∗ mvcc.txnCtx ctx cd ∗ ⌜lg ≠ null⌝ ∗
      ⌜txn.validSortTarget o ∧
        ∀ log : mvcc.Log, log₀ <+: log → log.length + m + 3 ≤ 2 ^ 63 → txn.sortOk o log⌝ }}
    (App (App (App (App (App (Val (@! txn.Range)) (Val #(GoInterface.ok ctx))) (Val #lg)) (Val #kv))
      (Val #r)) (Val #withTotal))
  {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
      mvcc.storeReader s γ ∗ ownToks γ.revs m ∗ ⌜trace ≠ null⌝ ∗
      ∃ (log : mvcc.Log) (rev : w64), mvcc.idxCert γ.idx log ∗
        ⌜log₀ <+: log ∧ log.length + m + 3 ≤ 2 ^ 63 ∧ log ≠ [] ∧
          rev = W64 ((log.length : Int) - 1)⌝ ∗
        txn.rangeResult resp err log rev o withTotal }}

end spec

end EtcdGrove
end Perennial
