/-
`storeTxnWrite.End` (kvstore_txn.go). Lean-first (no Rocq counterpart); see `InvStore.lean`.
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

/-- `tw.End()` ends the write transaction, its key-values released (`storeTxnWriteCore`: it
reads the `changes` slice's length only), its writer sealed or not: with a change, the pending
revision is committed (`currentRev++` and the batch transaction's write-back, under
`s.revMu`), certified (`idxCert` of `commitLog`); the transaction's tokens are the caller's
again (`storeReaderC`, with the reader's tag `Z`; 2026-10-13, unit 6a), and so is its revision
token if no revision was made (`pend = []`). `Unlock` takes the batch lock's invariant `P` (the
store's, `hookIs`) back. The frozen statement (`storeReader`) is `specFrozen` (`spec_frozen`). -/
abbrev mvcc.storeTxnWrite.End.spec : Prop :=
  ∀ (tw s : Loc) (γ : mvcc.StoreNames) (ilog : mvcc.Log) (pend : List mvcc.Change)
    (chs : GoSlice) (ps : List Loc) (sealed : Bool) (P : IProp GF) (f : val) (crev : Int)
    (Z : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.storeTxnWriteCore tw s γ ilog pend chs ps sealed crev Z ∗ mvcc.hookIs γ P f ∗ P }}
    (App (Val (tw @!! go.GoType.PointerType storeTxnWrite.ty @!! go!"End")) (Val #()))
  {{ RET #(); mvcc.storeReaderC s γ ∗ □ Z ∗ mvcc.idxCert γ.idx (mvcc.commitLog ilog pend) ∗
      (if pend = [] then mvcc.revToken γ else iprop(True)) }}

/-- The frozen statement (before unit 6a). -/
abbrev mvcc.storeTxnWrite.End.specFrozen : Prop :=
  ∀ (tw s : Loc) (γ : mvcc.StoreNames) (ilog : mvcc.Log) (pend : List mvcc.Change)
    (chs : GoSlice) (ps : List Loc) (sealed : Bool) (P : IProp GF) (f : val),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.storeTxnWriteCore tw s γ ilog pend chs ps sealed ∗ mvcc.hookIs γ P f ∗ P }}
    (App (Val (tw @!! go.GoType.PointerType storeTxnWrite.ty @!! go!"End")) (Val #()))
  {{ RET #(); mvcc.storeReader s γ ∗ mvcc.idxCert γ.idx (mvcc.commitLog ilog pend) ∗
      (if pend = [] then mvcc.revToken γ else iprop(True)) }}

open Iris.ProofMode in
/-- **The frozen statement is a corollary** (`storeReader_of`). -/
theorem mvcc.storeTxnWrite.End.spec_frozen (h : mvcc.storeTxnWrite.End.spec (GF := GF) (hG := hG)) :
    mvcc.storeTxnWrite.End.specFrozen (GF := GF) (hG := hG) := by
  intro tw s γ ilog pend chs ps sealed P f
  iintro %Φ H HΦ
  iapply (h tw s γ ilog pend chs ps sealed P f (-1) (mvcc.crevFrozen γ)) $$ %Φ [H]
  · iexact H
  inext
  iintro ⟨Hr, #Hf, Hrest⟩
  iapply HΦ
  iframe Hrest
  iapply mvcc.storeReader_of $$ [$Hr $Hf]

end spec

end EtcdGrove
end Perennial
