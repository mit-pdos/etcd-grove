/-
`Count` (`range.go`): the number of keys in a range.
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
  go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-- `Count(ctx, lg, kv, key, rangeEnd, revision)`: `Range` of the count-only request
`countOp k (rangeEndOf rangeEnd e) revision`: the number of keys of the range in the state at the
revision read (`rangeRev`: the transaction's if `revision ≤ 0`), or `ErrFutureRev` and `0`.
2026-10-14 (unit P1b): the context's trace `ot` (`ctxTraceIs`) and its ownership taken
(`EnsureTrace`; `Range`'s trace dropped). 2026-10-14 (unit A2): the key shorter than `2 ^ 63 - 1`
(the request it builds states it: `txn.rangeRequestIs`). -/
abbrev txn.Count.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (lg : Loc) (kv : GoInterface)
    (s : Loc) (γ : mvcc.StoreNames) (key rangeEnd : GoSlice) (k e : GoString) (revision : w64)
    (m : Nat) (log₀ : mvcc.Log) (ot : Option Loc) (te : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗
      txn.isKV kv s γ ∗ mvcc.storeReader s γ ∗ ownToks γ.revs m ∗ mvcc.idxCert γ.idx log₀ ∗
      key ↦*□ k ∗ rangeEnd ↦*□ e ∗ mvcc.txnCtx ctx cd ∗
      traceutil.ctxTraceIs ctx ot ∗ traceutil.ownTraceOpt ot te ∗ ⌜lg ≠ null⌝ ∗
      ⌜sint.Z key.len < 2 ^ 63 - 1⌝ }}
    (App (App (App (App (App (App (Val (@! txn.Count)) (Val #(GoInterface.ok ctx))) (Val #lg))
      (Val #kv)) (Val #key)) (Val #rangeEnd)) (Val #revision))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      mvcc.storeReader s γ ∗ ownToks γ.revs m ∗
      ∃ (log : mvcc.Log) (rev : w64) (crev : Int), mvcc.idxCert γ.idx log ∗ mvcc.crevLb γ.idx crev ∗
        ⌜log₀ <+: log ∧ log.length + m + 3 ≤ 2 ^ 63 ∧ log ≠ [] ∧
          rev = W64 ((log.length : Int) - 1) ∧ -1 ≤ crev ∧ crev ≤ sint.Z rev⌝ ∗
        ((⌜err = GoInterface.nil ∧ sint.Z revision ≤ sint.Z rev ∧
            n = W64 ((rangeIn (mvcc.stateAt log (sint.nat (mvcc.rangeRev rev revision)))
              (txn.countOp k (txn.rangeEndOf rangeEnd e) revision)).length : Int)⌝) ∨
         (⌜sint.Z rev < sint.Z revision ∧ n = W64 0⌝ ∗ ∃ ef : GoInterfaceOk,
            globalAddr ErrFutureRev ↦□ GoInterface.ok ef ∗ ⌜err = GoInterface.ok ef⌝) ∨
         (⌜sint.Z revision ≤ sint.Z rev ∧ sint.Z (mvcc.rangeRev rev revision) < crev ∧ n = W64 0⌝ ∗
            ∃ ec : GoInterfaceOk,
            globalAddr ErrCompacted ↦□ GoInterface.ok ec ∗ ⌜err = GoInterface.ok ec⌝)) }}

end spec

end EtcdGrove
end Perennial
