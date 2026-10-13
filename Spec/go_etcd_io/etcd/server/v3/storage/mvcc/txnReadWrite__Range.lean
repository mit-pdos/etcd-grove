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
statement is `specFrozen` (`spec_frozen`). -/
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

/-- The frozen statement (before unit 6a). -/
abbrev mvcc.txnReadWrite.Range.specFrozen : Prop :=
  ∀ (trw s : Loc) (γ : mvcc.StoreNames) (log : mvcc.Log) (rev : w64)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (todo : Bool) (key endk : GoSlice)
    (k e : GoString) (ro : RangeOptions),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ mvcc.isRoTxnWrite trw s γ log rev ∗ mvcc.rangeCtx todo ctx cd ∗ key ↦*□ k ∗
      endk ↦*□ e }}
    (App (App (App (App (Val (trw @!! go.GoType.PointerType txnReadWrite.ty @!! go!"Range"))
      (Val #(GoInterface.ok ctx))) (Val #key)) (Val #endk)) (Val #ro))
  {{ (r : Loc) (err : GoInterface), RET (PairV #r #err);
      ⌜todo = true → r ≠ null⌝ ∗ mvcc.isRoTxnWrite trw s γ log rev ∗
      mvcc.rangeOutcome r err log rev (decide (endk = slice.nil)) k e ro }}

open Iris.ProofMode in
/-- **The frozen statement is a corollary** (`crev = -1`, `rangeOutcomeC_neg`). -/
theorem mvcc.txnReadWrite.Range.spec_frozen
    (h : mvcc.txnReadWrite.Range.spec (GF := GF) (hG := hG)) :
    mvcc.txnReadWrite.Range.specFrozen (GF := GF) (hG := hG) := by
  intro trw s γ log rev ctx cd todo key endk k e ro
  iintro %Φ ⟨#Hpkg, Htx, #Hctx, #Hkey, #Hend⟩ HΦ
  iapply (h trw s γ log rev ctx cd todo key endk k e ro (-1) (mvcc.crevFrozen γ)) $$ %Φ [Htx]
  · iframe Htx; iframe #
  inext
  iintro %r %err ⟨%Ht, Htx, Hout⟩
  ihave %Hrv : ⌜0 ≤ sint.Z rev⌝ $$ [Htx]
  · iunfold mvcc.isRoTxnWrite at Htx
    icases Htx with ⟨%mw, -, Htx⟩
    iunfold mvcc.isTxnRead at Htx
    iNamed Htx
    ihave %Hr := mvcc.storeTxnReadIs_rev tr s rt trace γ log rev (-1) (mvcc.crevFrozen γ) $$ Htr
    ipureintro; exact Hr.1
  iapply HΦ
  iframe Htx
  isplitl []
  · ipureintro; exact Ht
  iapply mvcc.rangeOutcomeC_neg _ _ _ _ _ _ _ _ Hrv $$ Hout

end spec

end EtcdGrove
end Perennial
