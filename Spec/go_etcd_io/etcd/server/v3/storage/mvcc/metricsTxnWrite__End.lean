/-
`metricsTxnWrite.End` (metrics_txn.go). Lean-first (no Rocq counterpart); see `InvStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore

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

/-- `tw.End()` of a transaction (a read or a write one, `TxnKind`; a write one without its
key-values, `isTxnEnd`: `isTxn_toEnd`): the metrics updated, the wrapped transaction ended
(`storeTxnRead.End` or `storeTxnWrite.End`): the tokens are back, and a write transaction's
committed log is certified (`txnEndPost`). A write transaction's `Unlock` takes the batch
lock's invariant back (`txnEndPre`). At any compaction revision `crev`, the tokens back as
`storeReaderC` with the reader's tag `Z` (2026-10-13, unit 6a); the frozen statement
(`storeReader`) is `specFrozen` (`spec_frozen`). -/
abbrev mvcc.metricsTxnWrite.End.spec : Prop :=
  ∀ (mw s : Loc) (γ : mvcc.StoreNames) (kind : mvcc.TxnKind) (crev : Int) (Z : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ mvcc.isTxnEnd mw s γ kind crev Z ∗
      mvcc.txnEndPre γ kind }}
    (App (Val (mw @!! go.GoType.PointerType metricsTxnWrite.ty @!! go!"End")) (Val #()))
  {{ RET #(); mvcc.storeReaderC s γ ∗ □ Z ∗ mvcc.txnEndPost γ kind }}

/-- The frozen statement (before unit 6a). -/
abbrev mvcc.metricsTxnWrite.End.specFrozen : Prop :=
  ∀ (mw s : Loc) (γ : mvcc.StoreNames) (kind : mvcc.TxnKind),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ mvcc.isTxnEnd mw s γ kind ∗
      mvcc.txnEndPre γ kind }}
    (App (Val (mw @!! go.GoType.PointerType metricsTxnWrite.ty @!! go!"End")) (Val #()))
  {{ RET #(); mvcc.storeReader s γ ∗ mvcc.txnEndPost γ kind }}

open Iris.ProofMode in
/-- **The frozen statement is a corollary** (`storeReader_of`). -/
theorem mvcc.metricsTxnWrite.End.spec_frozen
    (h : mvcc.metricsTxnWrite.End.spec (GF := GF) (hG := hG)) :
    mvcc.metricsTxnWrite.End.specFrozen (GF := GF) (hG := hG) := by
  intro mw s γ kind
  iintro %Φ H HΦ
  iapply (h mw s γ kind (-1) (mvcc.crevFrozen γ)) $$ %Φ [H]
  · iexact H
  inext
  iintro ⟨Hr, #Hf, Hpost⟩
  iapply HΦ
  iframe Hpost
  iapply mvcc.storeReader_of $$ [$Hr $Hf]

end spec

end EtcdGrove
end Perennial
