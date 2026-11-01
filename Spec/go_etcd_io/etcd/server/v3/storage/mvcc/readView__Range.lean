/-
`readView__Range` (metrics_txn.go / kv_view.go). Lean-first (no Rocq counterpart); see `InvStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.TxnRange
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `rv.Range(ctx, key, end, ro)`: a read transaction opened at the last revision of a
committed log, its range, and closed: at the compaction revision `crev` it observed, at or above
the caller's lower bound `c` (`rangeOutcomeC`; 2026-10-13, unit 6a). The readers' statement
(`storeReader`, `rangeOutcome`) is `specR` (`spec_R`, `ReaderSpecs.lean`). At a context that is
never done (`todo`, `rangeCtx`: `context.TODO()`'s) the result is not `nil`, as
`metricsTxnWrite.Range`'s (2026-10-31, M2 apply side: `applierV3backend.Compaction` reads `rr.Rev`
of `KV.Range(context.TODO(), …)` ignoring the error; at `todo = false` today's statement). -/
abbrev mvcc.readView.Range.spec : Prop :=
  ∀ (rv s : Loc) (γ : mvcc.StoreNames)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (todo : Bool) (key endk : GoSlice) (k e : GoString)
    (ro : RangeOptions) (c : Int),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isReadView rv s γ ∗ mvcc.storeReaderC s γ ∗ mvcc.crevLb γ.idx c ∗
      mvcc.rangeCtx todo ctx cd ∗ key ↦*□ k ∗ endk ↦*□ e }}
    (App (App (App (App (Val (rv @!! go.GoType.PointerType readView.ty @!! go!"Range"))
      (Val #(GoInterface.ok ctx))) (Val #key)) (Val #endk)) (Val #ro))
  {{ (r : Loc) (err : GoInterface), RET (PairV #r #err);
      ⌜todo = true → r ≠ null⌝ ∗ mvcc.storeReaderC s γ ∗
      ∃ (log : mvcc.Log) (rev : w64) (crev : Int), mvcc.idxCert γ.idx log ∗ mvcc.crevLb γ.idx crev ∗
        ⌜log ≠ [] ∧ rev = W64 ((log.length : Int) - 1) ∧ c ≤ crev ∧ -1 ≤ crev⌝ ∗
        mvcc.rangeOutcomeC r err log rev crev (decide (endk = slice.nil)) k e ro }}

/-- **Candidate** (2026-11-01, `notes/mvcc-api-candidate.md`; over `Api.lean`, not proved). `rv.Range(ctx, key, end, ro)` (the store's `Range`): a read transaction (concurrent
mode) opened at the store's state `σ`, the caller's update fired at it, unchanged, its range
(`rangeOutcomeC` at `σ`), and its end. -/
abbrev mvcc.readView.Range.specC : Prop :=
  ∀ (rv : Loc) (γ : mvcc.MvccName) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (todo : Bool) (key endk : GoSlice) (kk e : GoString) (ro : RangeOptions)
    (Q : mvcc.MvccState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isReadViewOf rv γ ∗ threadTok ∗ mvcc.rangeCtx todo ctx cd ∗ key ↦*□ kk ∗ endk ↦*□ e ∗
      AU <{ ∃∃ (σ : mvcc.MvccState), mvcc.mvccState γ σ }> @ ⊤ \ ↑mvcc.mvccN, ∅
        <{ mvcc.mvccState γ σ, COMM Q σ }> }}
    (App (App (App (App (Val (rv @!! go.GoType.PointerType readView.ty @!! go!"Range"))
      (Val #(GoInterface.ok ctx))) (Val #key)) (Val #endk)) (Val #ro))
  {{ (r : Loc) (err : GoInterface), RET (PairV #r #err); threadTok ∗ ⌜todo = true → r ≠ null⌝ ∗
      ∃ σ : mvcc.MvccState, Q σ ∗
        mvcc.rangeOutcomeC r err σ.log (W64 (σ.rev : Int)) σ.crev (decide (endk = slice.nil)) kk e ro }}

end spec

end EtcdGrove
end Perennial
