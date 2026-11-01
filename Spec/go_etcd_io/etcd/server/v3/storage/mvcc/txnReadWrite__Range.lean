/-
`txnReadWrite__Range` (`kv.go`). Lean-first (no Rocq counterpart); see `InvRoTxn.lean`.

-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvRoTxn
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

/-- `trw.Range(ctx, key, end, ro)`: the read transaction's range
(`metricsTxnWrite.Range`; at a context never canceled, `todo`, no context error), at the
compaction revision `crev` it observed (`rangeOutcomeC`; 2026-10-13, unit 6a). The frozen
statement is `specR` (`spec_R`, `ReaderSpecs.lean`). -/
abbrev mvcc.txnReadWrite.Range.spec : Prop :=
  ∀ (trace : Loc) (trw s : Loc) (γ : mvcc.StoreNames) (log : mvcc.Log) (rev : w64)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (todo : Bool) (key endk : GoSlice)
    (k e : GoString) (ro : RangeOptions) (crev : Int) (Z : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ mvcc.isRoTxnWrite trw s γ trace log rev crev Z ∗ mvcc.rangeCtx todo ctx cd ∗ key ↦*□ k ∗
      endk ↦*□ e }}
    (App (App (App (App (Val (trw @!! go.GoType.PointerType txnReadWrite.ty @!! go!"Range"))
      (Val #(GoInterface.ok ctx))) (Val #key)) (Val #endk)) (Val #ro))
  {{ (r : Loc) (err : GoInterface), RET (PairV #r #err);
      ⌜todo = true → r ≠ null⌝ ∗ mvcc.isRoTxnWrite trw s γ trace log rev crev Z ∗
      mvcc.rangeOutcomeC r err log rev crev (decide (endk = slice.nil)) k e ro }}

/-- **Candidate** (2026-11-01, `notes/mvcc-api-candidate.md`; over `Api.lean`, not proved). `t.Range(ctx, key, end, ro)` in the read-only write transaction of a read one at `σ`:
the read transaction's (`metricsTxnWrite.Range.specC`). -/
abbrev mvcc.txnReadWrite.Range.specC : Prop :=
  ∀ (trw : Loc) (γ : mvcc.MvccName) (trace : Loc) (σ : mvcc.MvccState)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (todo : Bool)
    (key endk : GoSlice) (kk e : GoString) (ro : RangeOptions),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.mvccRoTxn trw γ trace σ ∗ mvcc.rangeCtx todo ctx cd ∗ key ↦*□ kk ∗ endk ↦*□ e }}
    (App (App (App (App (Val (trw @!! go.GoType.PointerType txnReadWrite.ty @!! go!"Range"))
      (Val #(GoInterface.ok ctx))) (Val #key)) (Val #endk)) (Val #ro))
  {{ (r : Loc) (err : GoInterface), RET (PairV #r #err);
      ⌜todo = true → r ≠ null⌝ ∗ mvcc.mvccRoTxn trw γ trace σ ∗
      mvcc.rangeOutcomeC r err σ.log (W64 (σ.rev : Int)) σ.crev (decide (endk = slice.nil)) kk e ro }}

end spec

end EtcdGrove
end Perennial
