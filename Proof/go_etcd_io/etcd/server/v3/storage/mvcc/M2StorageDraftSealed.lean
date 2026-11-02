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

/-- **The restored log's persistent receipt, by the mode** (drafted, in place of the pure
`restoreBoundM`): on, `⧖ (logCh L)`, the image's (some member's sealed log, `dbImageR`); off,
nothing (the rebuild's receipts are the writer's, as today). -/
def mvcc.restoreRcptM (d' : mvcc.KBReal) (L : mvcc.Log) : IProp GF :=
  if d'.cm then iprop(⧖ (mvcc.logCh L)) else iprop(True)

instance mvcc.restoreRcptM_persistent (d' : mvcc.KBReal) (L : mvcc.Log) :
    Persistent (mvcc.restoreRcptM (GF := GF) d' L) := by
  unfold mvcc.restoreRcptM; split <;> infer_instance

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

/-- On, the receipt is the restored writer's (`idxWriter_split`'s right-to-left). -/
theorem mvcc.restoreRcptM_on (d' : mvcc.KBReal) (L : mvcc.Log) (h : d'.cm = true) :
    mvcc.restoreRcptM (GF := GF) d' L ⊣⊢ ⧖ (mvcc.logCh L) := by
  unfold mvcc.restoreRcptM; simp only [h, ↓reduceIte]; exact .rfl

/-- **Draft of `store.Restore.specM` by sealed logs**: `specM` with the pure premise
`restoreBoundM d' ([[], []] ++ R)` replaced by the persistent receipt `restoreRcptM d' ([[], []] ++
R)` in the pre (first, before `isPkgInit`), which the store's proof keeps in the restored writer's
handle (`idxWriter_split`; item 15's). Everything else is `specM`'s text. -/
abbrev mvcc.store.Restore.specMR : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (b' : GoInterface) (d' : mvcc.KBReal) (γb' : GName)
    (P' : IProp GF) (L R : mvcc.Log) (c : Int) (r : mvcc.CmpRecs),
  L <+: [[], []] ++ R → mvcc.restoreLogOk R → c ≤ r.crev →
  {{ mvcc.restoreRcptM d' ([[], []] ++ R) ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isStore s γ ∗ ⌜∃ d, γ.kb = some d ∧ d'.cm = d.cm⌝ ∗
      mvcc.restoreRightM s γ c ∗ mvcc.fieldShare s γ (1 : Qp).half.half ∗ mvcc.wsDep γ ∗
      mvcc.writerFrag γ ∗ mvcc.writerOwn γ ∗ mvcc.writerPin γ L ∗
      mvcc.idxCert γ.idx L ∗ ownToks γ.revs (2 ^ 63 - 3 - L.length) ∗
      (if γ.watchQ then mvcc.logQ γ L else iprop(True)) ∗
      mvcc.certOk γ ([[], []] ++ R) ∗
      (∀ p : mvcc.PhysNames, ⌜p.bucket = γb' ∧ p.kb = some d'⌝ →
        mvcc.restoreFixM d' (γ.withPhys p) -∗ mvcc.storeBackendTR b' s (γ.withPhys p) P' r) ∗
      (∀ p : mvcc.PhysNames, ⌜p.bucket = γb' ∧ p.kb = some d'⌝ →
        mvcc.keyCleanReadR b' (mvcc.bucketViewC (γ.withPhys p))
          iprop(mvcc.storeRT (γ.withPhys p) ∗ mvcc.restoreRegM d')
          (mvcc.kbRecs (γ.withPhys p).kb (γ.withPhys p).bucket r) r) ∗
      mvcc.restoreImageM d' γb' ([[], []] ++ R) r ∗ mvcc.kbNoDelOff (some d') ∗
      mvcc.kbRegRight (some d') ∗
      mvcc.restoreRegM d' ∗ mvcc.kbSRM (some d') ∗ mvcc.kbWTSupplyM (some d') ∗ mvcc.resumeHookM d' r ∗
      ([∗list] _x ∈ List.replicate mvcc.nReaders (), mvcc.kbRT (some d')) }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"Restore")) (Val #b'))
  {{ RET #GoInterface.nil; ∃ p' : mvcc.PhysNames,
      ⌜p'.bucket = γb' ∧ p'.kb = some d'⌝ ∗
      mvcc.storeCloserM s (γ.withPhys p') r.crev ∗
      mvcc.fieldShare s γ (1 : Qp).half.half ∗ mvcc.wsDep γ ∗
      mvcc.writerFrag (γ.withPhys p') ∗ mvcc.writerOwn (γ.withPhys p') ∗
      mvcc.writerPin (γ.withPhys p') ([[], []] ++ R) ∗
      mvcc.hookP (γ.withPhys p') P' ∗
      mvcc.idxCert γ.idx ([[], []] ++ R) ∗
      ownToks γ.revs (2 ^ 63 - 3 - ([[], []] ++ R).length) ∗
      (if γ.watchQ then mvcc.logQ γ ([[], []] ++ R) else iprop(True)) ∗
      mvcc.resumeHookM d' r ∗
      mvcc.compactJobResM γ.kb ∗
      ([∗list] _x ∈ List.replicate (mvcc.nReaders - 1 - mvcc.nJobRd γ.kb) (), mvcc.storeRT γ) ∗
      mvcc.storeRT (γ.withPhys p') }}

/-- **The drafted `Restore` asks no more of its callers than `specM` did**: `specM` gives
`specMR` (the receipt gives the pure bound, `restoreBoundM_of_rcpt`); the store's proof of `specMR`
has the receipt itself, which the restored writer keeps. -/
theorem mvcc.store.Restore.specMR_of_specM (h : mvcc.store.Restore.specM (GF := GF) (hG := hG)) :
    mvcc.store.Restore.specMR (GF := GF) (hG := hG) := by
  intro s γ b' d' γb' P' L R c r hpre hR hc
  iintro %Φ ⟨#Hr, Hpre⟩ HΦ
  ihave %hb := mvcc.restoreBoundM_of_rcpt d' ([[], []] ++ R) $$ Hr
  iapply (h s γ b' d' γb' P' L R c r hpre hR hc hb) $$ Hpre HΦ

end draft

end EtcdGrove
end Perennial
