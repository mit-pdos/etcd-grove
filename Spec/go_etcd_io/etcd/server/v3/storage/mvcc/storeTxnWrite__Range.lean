/-
`storeTxnWrite.Range` (kvstore_txn.go). Lean-first (no Rocq counterpart); see `InvStore.lean`.
-/
module

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

/-- `tw.Range(ctx, key, end, ro)`: the write transaction's range read sees its own pending
changes. It is `rangeKeys` at the transaction's revision (`writeRev`: the pending one once it
has a change, else the committed log's last) of the committed log with the pending revision
appended (`ilog ++ [pend]`; with no change the empty revision changes nothing), read from the
index by the writer and from the bucket through the batch transaction, which sees its own
puts. At `context.TODO()` (`todo`), no context error. At the compaction revision `crev` the
transaction observed: `ErrCompacted` below it, the uncompacted outcome at or above it
(`rangeOutcomeC`; 2026-10-13, unit 6a). The frozen statement is `specFrozen` (`spec_frozen`). -/
abbrev mvcc.storeTxnWrite.Range.spec : Prop :=
  ∀ (tw s : Loc) (γ : mvcc.StoreNames) (ilog : mvcc.Log) (pend : List mvcc.Change)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (todo : Bool)
    (key endk : GoSlice) (k e : GoString) (ro : RangeOptions) (crev : Int) (Z : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.storeTxnWriteIs tw s γ ilog pend crev Z ∗ mvcc.rangeCtx todo ctx cd ∗ key ↦*□ k ∗
      endk ↦*□ e }}
    (App (App (App (App (Val (tw @!! go.GoType.PointerType storeTxnWrite.ty @!! go!"Range"))
      (Val #(GoInterface.ok ctx))) (Val #key)) (Val #endk)) (Val #ro))
  {{ (r : Loc) (err : GoInterface), RET (PairV #r #err);
      ⌜todo = true → r ≠ null⌝ ∗
      mvcc.storeTxnWriteIs tw s γ ilog pend crev Z ∗
      mvcc.rangeOutcomeC r err (ilog ++ [pend]) (W64 ((mvcc.writeRev ilog pend : Nat) : Int)) crev
        (decide (endk = slice.nil)) k e ro }}

/-- The frozen statement (before unit 6a). -/
abbrev mvcc.storeTxnWrite.Range.specFrozen : Prop :=
  ∀ (tw s : Loc) (γ : mvcc.StoreNames) (ilog : mvcc.Log) (pend : List mvcc.Change)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (todo : Bool)
    (key endk : GoSlice) (k e : GoString) (ro : RangeOptions),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.storeTxnWriteIs tw s γ ilog pend ∗ mvcc.rangeCtx todo ctx cd ∗ key ↦*□ k ∗ endk ↦*□ e }}
    (App (App (App (App (Val (tw @!! go.GoType.PointerType storeTxnWrite.ty @!! go!"Range"))
      (Val #(GoInterface.ok ctx))) (Val #key)) (Val #endk)) (Val #ro))
  {{ (r : Loc) (err : GoInterface), RET (PairV #r #err);
      ⌜todo = true → r ≠ null⌝ ∗
      mvcc.storeTxnWriteIs tw s γ ilog pend ∗
      mvcc.rangeOutcome r err (ilog ++ [pend]) (W64 ((mvcc.writeRev ilog pend : Nat) : Int))
        (decide (endk = slice.nil)) k e ro }}

open Iris.ProofMode in
/-- **The frozen statement is a corollary** (`crev = -1`, `rangeOutcomeC_neg`). -/
theorem mvcc.storeTxnWrite.Range.spec_frozen
    (h : mvcc.storeTxnWrite.Range.spec (GF := GF) (hG := hG)) :
    mvcc.storeTxnWrite.Range.specFrozen (GF := GF) (hG := hG) := by
  intro tw s γ ilog pend ctx cd todo key endk k e ro
  iintro %Φ ⟨#Hpkg, Htw, #Hctx, #Hkey, #Hend⟩ HΦ
  iapply (h tw s γ ilog pend ctx cd todo key endk k e ro (-1) (mvcc.crevFrozen γ)) $$ %Φ [Htw]
  · iframe Htw; iframe #
  inext
  iintro %r %err ⟨%Ht, Htw, Hout⟩
  ihave %Hrv := mvcc.storeTxnWriteIs_writeRev tw s γ ilog pend (-1) (mvcc.crevFrozen γ) $$ Htw
  iapply HΦ
  iframe Htw
  isplitl []
  · ipureintro; exact Ht
  iapply mvcc.rangeOutcomeC_neg _ _ _ _ _ _ _ _ Hrv $$ Hout

end spec

end EtcdGrove
end Perennial
