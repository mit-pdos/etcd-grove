/-
**M2, the storage side: B2 by sealed logs, the mvcc side (Draft, what is left)**
(`notes/m2-storage-plan.md`, "B2 by sealed logs"; the user's decision of 2026-10-30: no `NewServer`
premise, every installed snapshot's log is some member's sealed log). Imported by nothing but the
server's B2 Draft (`etcdserver/M2StorageDraftB2.lean`); no `axiom`, no `sorry`.

**Switched (2026-11-01, branch `m2-b2-mvcc`)**: the mvcc half's ghost state is in place in
`InvIndex.lean`: `idxSealed`/`idxCert` carry the persistent receipt `⧖ (logCh log)` in place of the
pure `logCh log < receiptBound` (`idxSealed_rcpt`, `idxCert_rcpt`; `idxSealed_small` from it), the
writer's handles `idxWriter`/`idxWriterSealed` hold `⧖ (logCh ilog + pend.length)` in place of the
exclusive `⧗` (so this Draft's `idxWriterP` is `idxWriter`, and `idxWriterP_of_image` is
`idxWriter_split`'s right-to-left), and `treeIndex.Put`/`Tombstone` raise it by the change's Go step
(`wp_raise_receipt`, this Draft's `wp_proofP`s, in place). The restore paths turn the rebuild's
exclusive receipts into it (`restore_finish`: `receipt_snapshot`).

**What is left here** (it waits on the restore in compaction mode, `Restore.specM`, itself a Draft,
`M2StorageDraftRestore.lean`): `idxSealedR`/`idxCertR`, now names for `idxSealed`/`idxCert` (kept for
the server Draft's texts), and the restore's premise by the mode, `restoreRcptM` (in place of the pure
`restoreBoundM`), with `Restore.specMR` and `specMR_of_specM`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.M2StorageDraftRestore

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
/-! ## A sealed log's persistent receipt (switched: names for today's) -/

/-- **A sealed log with its persistent receipt**: since the switch, `idxSealed` itself. -/
abbrev mvcc.idxSealedR (γ : mvcc.IdxNames) (log : mvcc.Log) : IProp GF := mvcc.idxSealed γ log

/-- **A certified log with its persistent receipt**: since the switch, `idxCert` itself. What the
sole writer's certificate gives the sender of an image (`txn.soleWriter`'s `idxCert`). -/
abbrev mvcc.idxCertR (γ : mvcc.IdxNames) (log : mvcc.Log) : IProp GF := mvcc.idxCert γ log

theorem mvcc.idxCertR_rcpt (γ : mvcc.IdxNames) (log : mvcc.Log) :
    mvcc.idxCertR (GF := GF) γ log ⊢ ⧖ (mvcc.logCh log) :=
  mvcc.idxCert_rcpt γ log

theorem mvcc.idxSealedR_small (γ : mvcc.IdxNames) (log : mvcc.Log) :
    mvcc.idxSealedR (GF := GF) γ log ⊢ ⌜mvcc.logCh log < receiptBound GF⌝ :=
  mvcc.idxSealed_small γ log

end ghost

section draft
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-! ## The restore takes the image's receipt -/

/- (`restoreRcptM` and `restoreRcptM_on` are switched: `RestoreVocab.lean`, M2's item 15, step A3.) -/

/-- The receipt gives today's pure premise. -/
theorem mvcc.restoreBoundM_of_rcpt (d' : mvcc.KBReal) (L : mvcc.Log) :
    mvcc.restoreRcptM (GF := GF) d' L ⊢ ⌜mvcc.restoreBoundM (GF := GF) d' L⌝ := by
  unfold mvcc.restoreRcptM mvcc.restoreBoundM
  cases hcm : d'.cm
  · simp only [Bool.false_eq_true, ↓reduceIte]
    iintro -; ipureintro; intro h; cases h
  · simp only [↓reduceIte]
    iintro #Hp
    ihave %h := preceipt_lt _ $$ Hp
    ipureintro; intro _; exact h

/- (`store.Restore.specMR` is switched: `store.Restore.spec` with amendment 1's permits, M2's item 15,
step A3.) -/

end draft

end EtcdGrove
end Perennial
