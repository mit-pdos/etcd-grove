/-
`txnReadWrite__Range` (`kv.go`). Lean-first (no Rocq counterpart); see `InvRoTxn.lean`.

-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvRoTxn
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

/-- `trw.Range(ctx, key, end, ro)`: the read transaction's range
(`metricsTxnWrite.Range`; at a context never canceled, `todo`, no context error), at the
compaction revision `crev` it observed (`rangeOutcomeC`; 2026-10-13, unit 6a). The frozen
statement is `specFrozen` (`spec_frozen`, `FrozenSpecs.lean`). -/
abbrev mvcc.txnReadWrite.Range.spec : Prop :=
  ∀ (trw s : Loc) (γ : mvcc.StoreNames) (log : mvcc.Log) (rev : w64)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (todo : Bool) (key endk : GoSlice)
    (k e : GoString) (ro : RangeOptions) (crev : Int) (Z : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ mvcc.isRoTxnWrite trw s γ log rev crev Z ∗ mvcc.rangeCtx todo ctx cd ∗ key ↦*□ k ∗
      endk ↦*□ e }}
    (App (App (App (App (Val (trw @!! go.GoType.PointerType txnReadWrite.ty @!! go!"Range"))
      (Val #(GoInterface.ok ctx))) (Val #key)) (Val #endk)) (Val #ro))
  {{ (r : Loc) (err : GoInterface), RET (PairV #r #err);
      ⌜todo = true → r ≠ null⌝ ∗ mvcc.isRoTxnWrite trw s γ log rev crev Z ∗
      mvcc.rangeOutcomeC r err log rev crev (decide (endk = slice.nil)) k e ro }}

end spec

end EtcdGrove
end Perennial
