/-
**M2, the storage side: B2 by sealed logs, the mvcc side (Draft)** (`notes/m2-storage-plan.md`, "B2 by
sealed logs"; the user's decision of 2026-10-30: no `NewServer` premise, every installed snapshot's
log is some member's sealed log). Imported by nothing but the server's B2 Draft
(`etcdserver/M2StorageDraftB2.lean`); no `axiom`, no `sorry`; nothing switched.

**The problem** (review round 5's B2). The bound every seal certifies (`idxSealed`'s
`logCh log < receiptBound`) comes from the writer's *exclusive* receipts (`idxWriter`'s
`⧗ (logCh ilog + pend.length)`). A member that restores a compacted image (made by another member's
writer) cannot hold `⧗ (logCh L)` for the image's log `L`: those receipts are the other writer's, and
`restore()` takes one step per *surviving* entry (`restoreDone`'s `⧗ ents.length`). The image's
own bound `logCh L < receiptBound` (a pure fact, `restoreBoundM`) does not survive the next change:
counting the restored writer's later receipts from it gives `< 2·receiptBound` at its next seal.

**The fix: persistent receipts.** `⧖ n` (Perennial's `preceipt`: "at least `n` counted steps were
taken", persistent, `⧖ n ⊢ ⌜n < receiptBound⌝`) is a lower bound of the one global step counter,
shared by every member (one Iris instance, one `receiptBound GF`), and a Go step raises it by one
(`wp_go_step_preceipt`, `wp_raise_receipt`: `{⧖ m} step {⧖ (m + 1)}`). So:

- a sealed or committed log carries `⧖ (logCh log)` (in place of the pure `logCh log < receiptBound`:
  `idxSealedR`, `idxCertR`); the writer's seal and commit give it (`idxWriter_sealR`,
  `idxWriter_commitR`: `receipt_snapshot` of the writer's own `⧗`);
- it travels with the snapshot (the image's certificate, `etcdserver/M2StorageDraftB2.lean`'s
  `dbImageR`), and the installer's restore takes it (`restoreRcptM`, in place of the pure
  `restoreBoundM`: `Restore.specMR`, `specMR_of_specM`);
- the restored writer's handle holds the persistent receipt (`idxWriterP`: `idxWriterNR ∗
  ⧖ (logCh ilog + pend.length)`, made from the image's, `idxWriterP_of_image`), each change raises it
  by the Go step that puts it (`treeIndex.Put.specP`, `treeIndex.Tombstone.specP`, proved below: today's
  proofs with `wp_raise_receipt` in place of `wp_take_receipt`), and its seal and commit give
  `idxSealedR`/`idxCertR` again (`idxWriterP_seal`, `idxWriterP_commit`): **the induction closes**,
  the next member restoring this one's later image gets its bound the same way.
- every writer can move to the persistent form (`idxWriterP_of_writer`: `⧗ n ⊢ |==> ⧖ n`), so the
  switch can make `idxWriterP` the one handle (the restore by either mode, the rebuild's receipts
  raising it as the puts do), or keep `idxWriter` off and `idxWriterP` on.

What the switch loses: the writer's receipts are no longer exclusive, so they no longer add up with
another pool's (`receipt_add`); nothing uses that (`idxWriter_split` has no user).
-/
module

public import Proof.ReceiptTactics
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.M2StorageDraftRestore
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.treeIndex__Put
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.treeIndex__Tombstone
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.keyIndex__tombstone

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

/-! ## A sealed log's persistent receipt -/

/-- **A sealed log with its persistent receipt** (drafted: `idxSealed`'s `⌜logCh log < receiptBound
GF⌝` becomes `⧖ (logCh log)`, which implies it, `idxSealedR_small`). -/
def mvcc.idxSealedR (γ : mvcc.IdxNames) (log : mvcc.Log) : IProp GF :=
  iprop(mvcc.idxSealed γ log ∗ ⧖ (mvcc.logCh log))

instance mvcc.idxSealedR_persistent (γ : mvcc.IdxNames) (log : mvcc.Log) :
    Persistent (mvcc.idxSealedR (GF := GF) γ log) := by
  unfold mvcc.idxSealedR; infer_instance

/-- **A certified log with its persistent receipt** (drafted: `idxCert`'s `⌜logCh log <
receiptBound GF⌝` becomes `⧖ (logCh log)`). What the sole writer's certificate gives the sender of
an image (`txn.soleWriter`'s `idxCert`). -/
def mvcc.idxCertR (γ : mvcc.IdxNames) (log : mvcc.Log) : IProp GF :=
  iprop(mvcc.idxCert γ log ∗ ⧖ (mvcc.logCh log))

instance mvcc.idxCertR_persistent (γ : mvcc.IdxNames) (log : mvcc.Log) :
    Persistent (mvcc.idxCertR (GF := GF) γ log) := by
  unfold mvcc.idxCertR; infer_instance

theorem mvcc.idxCertR_sealedR (γ : mvcc.IdxNames) (log : mvcc.Log) :
    mvcc.idxCertR (GF := GF) γ log ⊢ mvcc.idxSealedR γ log := by
  unfold mvcc.idxCertR mvcc.idxSealedR
  iintro ⟨#Hc, #Hp⟩
  ihave #Hs := mvcc.idxCert_sealed γ log $$ Hc
  iframe Hs Hp

theorem mvcc.idxCertR_cert (γ : mvcc.IdxNames) (log : mvcc.Log) :
    mvcc.idxCertR (GF := GF) γ log ⊢ mvcc.idxCert γ log := by
  unfold mvcc.idxCertR
  iintro ⟨#Hc, -⟩; iexact Hc

theorem mvcc.idxSealedR_small (γ : mvcc.IdxNames) (log : mvcc.Log) :
    mvcc.idxSealedR (GF := GF) γ log ⊢ ⌜mvcc.logCh log < receiptBound GF⌝ := by
  unfold mvcc.idxSealedR
  iintro ⟨-, #Hp⟩
  iapply preceipt_lt $$ Hp

/-- The empty log is sealed, with its receipt. -/
theorem mvcc.idxSealedR_nil (γ : mvcc.IdxNames) : ⊢ |==> mvcc.idxSealedR (GF := GF) γ [] := by
  unfold mvcc.idxSealedR
  imod mvcc.idxSealed_nil (GF := GF) γ with #Hs
  imod preceipt_zero (GF := GF) with #H0
  imodintro
  iframe Hs
  have h : mvcc.logCh ([] : mvcc.Log) = 0 := rfl
  rw [h]; iexact H0

/-- **The writer's persistent receipt**: its exclusive receipts give it (`receipt_snapshot`). -/
theorem mvcc.idxWriter_rcpt (γ : mvcc.IdxNames) (ilog : mvcc.Log) (pend : List mvcc.Change) :
    mvcc.idxWriter (GF := GF) γ ilog pend ⊢
      |==> (mvcc.idxWriter γ ilog pend ∗ ⧖ (mvcc.logCh (ilog ++ [pend]))) := by
  unfold mvcc.idxWriter
  iintro ⟨Ha, #Hn, %Hw, Hl, Hr⟩
  imod receipt_snapshot _ $$ Hr with ⟨Hr, #Hp⟩
  imodintro
  iframe Ha Hl Hr Hn
  isplitl []
  · ipureintro; exact Hw
  rw [mvcc.logCh_snoc]; iexact Hp

/-- The sealed writer's persistent receipt. -/
theorem mvcc.idxWriterSealed_rcpt (γ : mvcc.IdxNames) (ilog : mvcc.Log) (pend : List mvcc.Change) :
    mvcc.idxWriterSealed (GF := GF) γ ilog pend ⊢
      |==> (mvcc.idxWriterSealed γ ilog pend ∗ ⧖ (mvcc.logCh (ilog ++ [pend]))) := by
  unfold mvcc.idxWriterSealed
  iintro ⟨Ha, #Hn, %Hw, Hl, Hr⟩
  imod receipt_snapshot _ $$ Hr with ⟨Hr, #Hp⟩
  imodintro
  iframe Ha Hl Hr Hn
  isplitl []
  · ipureintro; exact Hw
  rw [mvcc.logCh_snoc]; iexact Hp

/-- **Seal, with the sealed log's receipt** (`idxWriter_seal`). -/
theorem mvcc.idxWriter_sealR (γ : mvcc.IdxNames) (ilog : mvcc.Log) (pend : List mvcc.Change)
    (hne : pend ≠ []) :
    mvcc.idxWriter (GF := GF) γ ilog pend ==∗
      mvcc.idxWriterSealed γ ilog pend ∗ mvcc.idxSealedR γ (ilog ++ [pend]) := by
  iintro Hw
  imod mvcc.idxWriter_rcpt γ ilog pend $$ Hw with ⟨Hw, #Hp⟩
  imod mvcc.idxWriter_seal γ ilog pend hne $$ Hw with ⟨Hw, #Hs⟩
  imodintro
  iframe Hw
  unfold mvcc.idxSealedR
  iframe Hs Hp

/-- **Commit, with the committed log's receipt** (`idxWriter_commit`). -/
theorem mvcc.idxWriter_commitR (γ : mvcc.IdxNames) (ilog : mvcc.Log) (pend : List mvcc.Change)
    (hlen : ilog.length + 2 < 2 ^ 63) :
    ⊢ mvcc.idxWriter (GF := GF) γ ilog pend -∗ mvcc.idxLogAuth γ (1 : Qp).half ilog ==∗
      mvcc.idxWriter γ (ilog ++ [pend]) [] ∗ mvcc.idxLogAuth γ (1 : Qp).half (ilog ++ [pend]) ∗
        mvcc.idxCertR γ (ilog ++ [pend]) := by
  iintro Hw Hl
  imod mvcc.idxWriter_rcpt γ ilog pend $$ Hw with ⟨Hw, #Hp⟩
  imod mvcc.idxWriter_commit γ ilog pend hlen $$ Hw Hl with ⟨Hw, Hl, #Hc⟩
  imodintro
  iframe Hw Hl
  unfold mvcc.idxCertR
  iframe Hc Hp

/-- **Commit of a sealed writer, with the committed log's receipt** (`idxWriterSealed_commit`). -/
theorem mvcc.idxWriterSealed_commitR (γ : mvcc.IdxNames) (ilog : mvcc.Log) (pend : List mvcc.Change)
    (hlen : ilog.length + 2 < 2 ^ 63) :
    ⊢ mvcc.idxWriterSealed (GF := GF) γ ilog pend -∗ mvcc.idxLogAuth γ (1 : Qp).half ilog ==∗
      mvcc.idxWriter γ (ilog ++ [pend]) [] ∗ mvcc.idxLogAuth γ (1 : Qp).half (ilog ++ [pend]) ∗
        mvcc.idxCertR γ (ilog ++ [pend]) := by
  iintro Hw Hl
  imod mvcc.idxWriterSealed_rcpt γ ilog pend $$ Hw with ⟨Hw, #Hp⟩
  imod mvcc.idxWriterSealed_commit γ ilog pend hlen $$ Hw Hl with ⟨Hw, Hl, #Hc⟩
  imodintro
  iframe Hw Hl
  unfold mvcc.idxCertR
  iframe Hc Hp

/-! ## The writer's handle by persistent receipt -/

/-- **The writer's handle with a persistent receipt** (drafted; the restored writer's in
compaction mode, or every writer's): `idxWriter` with `⧖` in place of `⧗`. -/
def mvcc.idxWriterP (γ : mvcc.IdxNames) (ilog : mvcc.Log) (pend : List mvcc.Change) : IProp GF :=
  iprop(mvcc.idxWriterNR γ ilog pend ∗ ⧖ (mvcc.logCh ilog + pend.length))

/-- Every writer moves to the persistent form. -/
theorem mvcc.idxWriterP_of_writer (γ : mvcc.IdxNames) (ilog : mvcc.Log) (pend : List mvcc.Change) :
    mvcc.idxWriter (GF := GF) γ ilog pend ⊢ |==> mvcc.idxWriterP γ ilog pend := by
  iintro Hw
  icases (mvcc.idxWriter_split γ ilog pend).1 $$ Hw with ⟨Hw, Hr⟩
  imod receipt_snapshot _ $$ Hr with ⟨-, #Hp⟩
  imodintro
  unfold mvcc.idxWriterP
  iframe Hw Hp

/-- **The restored writer's handle, from the image's receipt** (what `store.Restore` in compaction
mode makes, from `restoreRcptM`): no receipt of the rebuild is needed. -/
theorem mvcc.idxWriterP_of_image (γ : mvcc.IdxNames) (L : mvcc.Log) :
    mvcc.idxWriterNR (GF := GF) γ L [] ∗ ⧖ (mvcc.logCh L) ⊢ mvcc.idxWriterP γ L [] := by
  unfold mvcc.idxWriterP
  iintro ⟨Hw, #Hp⟩
  iframe Hw
  simp only [List.length_nil, Nat.add_zero]
  iexact Hp

theorem mvcc.idxWriterP_lt (γ : mvcc.IdxNames) (ilog : mvcc.Log) (pend : List mvcc.Change) :
    mvcc.idxWriterP (GF := GF) γ ilog pend ⊢ ⌜mvcc.logCh ilog + pend.length < receiptBound GF⌝ := by
  unfold mvcc.idxWriterP
  iintro ⟨-, #Hp⟩
  iapply preceipt_lt $$ Hp

/-- The sealed handle without its receipts (`idxWriterSealed`'s other conjuncts; moved from the
server's B2 Draft). -/
def mvcc.idxWriterSealedNR (γ : mvcc.IdxNames) (ilog : mvcc.Log) (pend : List mvcc.Change) :
    IProp GF :=
  iprop(monoListAuthOwn γ.hist 1 (mvcc.histOf (ilog ++ [pend])) ∗
    monoNatLbOwn γ.nev (mvcc.evsOf (ilog ++ [pend])).length ∗ ⌜mvcc.IdxWf ilog pend ∧ pend ≠ []⌝ ∗
    mvcc.idxLogAuth γ (1 : Qp).half ilog)

/-- **The seal with the caller's bound** (moved from the server's B2 Draft): `idxWriter_seal`
without the receipts, the sealed log's `logCh < receiptBound` the caller's. -/
theorem mvcc.idxWriterNR_seal (γ : mvcc.IdxNames) (ilog : mvcc.Log) (pend : List mvcc.Change)
    (hne : pend ≠ []) (hb : mvcc.logCh (ilog ++ [pend]) < receiptBound GF) :
    mvcc.idxWriterNR (GF := GF) γ ilog pend ==∗
      mvcc.idxWriterSealedNR γ ilog pend ∗ mvcc.idxSealed γ (ilog ++ [pend]) := by
  unfold mvcc.idxWriterNR mvcc.idxWriterSealedNR mvcc.idxSealed
  iintro ⟨Hauth, #Hnev, %Hwf, Hlauth⟩
  imod monoListAuthOwn_update_app [mvcc.HistItem.commit] $$ Hauth with ⟨Hauth, #Hlb⟩
  imodintro
  rw [mvcc.histShape_seal]
  iframe Hauth Hlauth Hlb Hnev
  isplitl
  · ipureintro; exact ⟨Hwf, hne⟩
  isplitl
  · ipureintro; exact Hwf.sealed
  ipureintro; exact hb

/-- The sealed handle with a persistent receipt. -/
def mvcc.idxWriterSealedP (γ : mvcc.IdxNames) (ilog : mvcc.Log) (pend : List mvcc.Change) :
    IProp GF :=
  iprop(mvcc.idxWriterSealedNR γ ilog pend ∗ ⧖ (mvcc.logCh ilog + pend.length))

/-- **Seal by persistent receipt**: the sealed log carries the handle's receipt. -/
theorem mvcc.idxWriterP_seal (γ : mvcc.IdxNames) (ilog : mvcc.Log) (pend : List mvcc.Change)
    (hne : pend ≠ []) :
    mvcc.idxWriterP (GF := GF) γ ilog pend ==∗
      mvcc.idxWriterSealedP γ ilog pend ∗ mvcc.idxSealedR γ (ilog ++ [pend]) := by
  unfold mvcc.idxWriterP
  iintro ⟨Hw, #Hp⟩
  ihave %Hlt := preceipt_lt _ $$ Hp
  rw [← mvcc.logCh_snoc] at Hlt
  imod mvcc.idxWriterNR_seal γ ilog pend hne Hlt $$ Hw with ⟨Hw, #Hs⟩
  imodintro
  unfold mvcc.idxWriterSealedP mvcc.idxSealedR
  iframe Hw Hs Hp
  rw [mvcc.logCh_snoc]; iexact Hp

/-- **Commit by persistent receipt** (`idxWriter_commit`'s proof without the exclusive receipts):
the committed log is certified with its receipt, and the handle goes on with it. -/
theorem mvcc.idxWriterP_commit (γ : mvcc.IdxNames) (ilog : mvcc.Log) (pend : List mvcc.Change)
    (hlen : ilog.length + 2 < 2 ^ 63) :
    ⊢ mvcc.idxWriterP (GF := GF) γ ilog pend -∗ mvcc.idxLogAuth γ (1 : Qp).half ilog ==∗
      mvcc.idxWriterP γ (ilog ++ [pend]) [] ∗ mvcc.idxLogAuth γ (1 : Qp).half (ilog ++ [pend]) ∗
        mvcc.idxCertR γ (ilog ++ [pend]) := by
  have hhalves := fun (l : mvcc.Log) =>
    (monoListAuthOwn_fractional (GF := GF) γ.log l).fractional (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at hhalves
  unfold mvcc.idxWriterP mvcc.idxWriterNR mvcc.idxCertR mvcc.idxCert mvcc.idxLogAuth
  iintro ⟨⟨Hauth, #Hnev, %Hwf, Hlauth⟩, #Hp⟩ Hlother
  obtain ⟨hwf, hl, hp, hcs⟩ := Hwf
  ihave %Hsm := preceipt_lt _ $$ Hp
  rw [← mvcc.logCh_snoc] at Hsm
  ihave #Hp' : iprop(⧖ (mvcc.logCh (ilog ++ [pend]))) $$ [Hp]
  · rw [mvcc.logCh_snoc]; iexact Hp
  ihave Hlauth : monoListAuthOwn γ.log 1 ilog $$ [Hlauth Hlother]
  · iapply (hhalves ilog).2; iframe Hlauth Hlother
  imod monoListAuthOwn_update_app [mvcc.HistItem.commit] $$ Hauth with ⟨Hauth, #Hlb⟩
  imod monoListAuthOwn_update_app [pend] $$ Hlauth with ⟨Hlauth, #Hllb⟩
  icases (hhalves (ilog ++ [pend])).1 $$ Hlauth with ⟨Hlauth, Hlother⟩
  imodintro
  have hwf' : mvcc.LogWf' (ilog ++ [pend] ++ [[]]) := hwf.append_nil (by simp)
  have hcs' : ∀ cs ∈ ilog ++ [pend], cs.length < 2 ^ 63 := by
    intro cs hcs'
    rcases List.mem_append.1 hcs' with h | h
    · exact hcs cs h
    · rw [List.mem_singleton] at h; rw [h]; exact hp
  have hhist : mvcc.histShape (ilog ++ [pend]) [] = mvcc.histShape ilog pend ++ [mvcc.HistItem.commit] :=
    (mvcc.histShape_commit ilog pend).symm
  have hhist2 : mvcc.histOf (ilog ++ [pend]) = mvcc.histShape ilog pend ++ [mvcc.HistItem.commit] := by
    rw [mvcc.histShape_commit]; simp [mvcc.histShape, mvcc.evsOfRev]
  have hevs : mvcc.evsOf (ilog ++ [pend] ++ [[]]) = mvcc.evsOf (ilog ++ [pend]) := by
    rw [mvcc.evsOf_append (ilog ++ [pend]) []]; simp [mvcc.evsOfRev]
  rw [hhist, hhist2, hevs]
  isplitl [Hauth Hlauth]
  · isplitl [Hauth Hlauth]
    · iframe Hauth Hlauth
      isplitl []
      · iexact Hnev
      ipureintro
      refine ⟨hwf', by simp; omega, by simp, hcs'⟩
    simp only [List.length_nil, Nat.add_zero]
    iexact Hp'
  iframe Hlother
  isplitl []
  · iframe Hlb Hllb
    isplitl
    · ipureintro
      exact ⟨hwf, by simp; omega, hcs'⟩
    ipureintro; exact Hsm
  iexact Hp'

end ghost

section draft
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-! ## The index's changes raise the receipt (the Go steps that pay them) -/

section put
variable [go_etcd_io.etcd.cache.v3.Assumptions]

/-- **`ti.Put` by persistent receipt** (drafted): `treeIndex.Put.spec` at `idxWriterP`. -/
abbrev mvcc.treeIndex.Put.specP : Prop :=
  ∀ (ti : Loc) (γ : mvcc.IdxNames) (ilog : mvcc.Log) (pend : List mvcc.Change) (key : GoSlice)
    (k : GoString) (rev : Revision) (v : GoString) (l : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isTreeIndex ti γ ∗ mvcc.idxWriterP γ ilog pend ∗ key ↦*□ k ∗
      ⌜mvcc.revOf rev = ⟨W64 ilog.length, W64 pend.length⟩ ∧ 1 ≤ ilog.length ∧
        pend.length + 1 < 2 ^ 63 ∧ mvcc.LogWf' (ilog ++ [pend ++ [.put k v l]])⌝ }}
    (App (App (Val (ti @!! go.GoType.PointerType treeIndex.ty @!! go!"Put")) (Val #key)) (Val #rev))
  {{ RET #(); mvcc.idxWriterP γ ilog (pend ++ [.put k v l]) }}

/-- **`ti.Tombstone` by persistent receipt** (drafted): `treeIndex.Tombstone.spec` at
`idxWriterP`. -/
abbrev mvcc.treeIndex.Tombstone.specP : Prop :=
  ∀ (ti : Loc) (γ : mvcc.IdxNames) (ilog : mvcc.Log) (pend : List mvcc.Change) (key : GoSlice)
    (k : GoString) (rev : Revision),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isTreeIndex ti γ ∗ mvcc.idxWriterP γ ilog pend ∗ key ↦*□ k ∗
      ⌜mvcc.revOf rev = ⟨W64 ilog.length, W64 pend.length⟩ ∧ 1 ≤ ilog.length ∧
        pend.length + 1 < 2 ^ 63 ∧ mvcc.LogWf' (ilog ++ [pend ++ [.del k]])⌝ }}
    (App (App (Val (ti @!! go.GoType.PointerType treeIndex.ty @!! go!"Tombstone")) (Val #key))
      (Val #rev))
  {{ RET #(GoInterface.nil); mvcc.idxWriterP γ ilog (pend ++ [.del k]) }}

/-- `treeIndex.Put.wp_proof` with the receipt raised (three lines differ). -/
theorem mvcc.treeIndex.Put.wp_proofP
    (wp_Get : btree.BTree.Get.spec (GF := GF) (hG := hG))
    (wp_ROI : btree.BTree.ReplaceOrInsert.spec (GF := GF) (hG := hG))
    (hPut : mvcc.keyIndex.put.spec (GF := GF) (hG := hG)) :
    mvcc.treeIndex.Put.specP (GF := GF) (hG := hG) := by
  have wp_Get : btree.BTree.Get.modelSpec (GF := GF) (hG := hG) := btree.BTree.Get.modelSpec_of wp_Get
  have wp_ROI : btree.BTree.ReplaceOrInsert.modelSpec (GF := GF) (hG := hG) :=
    btree.BTree.ReplaceOrInsert.modelSpec_of wp_ROI
  intro ti γ ilog pend key k rev v l
  wp_start as ⟨#Hti, Hw, #Hkey, %Hpre⟩
  obtain ⟨Hrev, Hilog, Hpend, Hwf'⟩ := Hpre
  iunfold mvcc.isTreeIndex at Hti
  iNamed Hti
  iunfold mvcc.idxWriterP at Hw
  iunfold mvcc.idxWriterNR at Hw
  icases Hw with ⟨⟨Hauth, #Hwlb, %Hwwf, Hlauth⟩, #Hrc⟩
  obtain ⟨Hwf, Hlen, Hplen, Hcs⟩ := Hwwf
  wp_apply wp_with_defer
  iintro %defer Hdefer
  (try wp_auto)
  -- `keyi := &keyIndex{key: key}`
  ihave %Hn := typedPointsto_not_null _ _ _ $$ «$r0»
  iStructNamedPrefix «$r0» "K"
  ipersist Kkey
  ihave #Hitem : mvcc.kiItemIs (GF := GF) «$r0_ptr» («$r0_ptr», k) $$ []
  · iunfold mvcc.kiItemIs
    isplitl []
    · ipureintro; rfl
    iunfold mvcc.kiKey
    iexists key
    iframe #
  -- `ti.Lock()`: the promoted method, through the guard
  rw [method_unfold (t := go.GoType.PointerType treeIndex.ty) (m := go!"Lock")]
  wp_call
  (try wp_auto)
  wp_apply +noauto sync.RWMutex.wp_Lock_guard $$ [$Hmu] as ⟨Hlk, HP⟩
  -- the receipt of the change (D19b), from the next resolution step
  -- the change's step raises the handle's persistent receipt (in place of taking `⧗ 1`)
  wp_raise_receipt Hrc
  ihave #Hrc' : iprop(⧖ (mvcc.logCh ilog + (pend ++ [mvcc.Change.put k v l]).length)) $$ [Hrc]
  · rw [List.length_append, List.length_singleton, ← Nat.add_assoc]; iexact Hrc
  wp_auto_lc 1
  imod (lc_fupd_elim_later (E := ⊤) (P := mvcc.idxLockInv t γ 1)) $$ Hlc1 HP with HP
  iunfold mvcc.idxLockInv at HP
  icases HP with ⟨%ilog', %pend', %L, %cmax, HP⟩
  iNamedSuffix HP "L"
  -- every compaction level is below the writer's revision
  icases HclL with ⟨%log₀, #Hl0, %Hc0⟩
  ihave %Hl0pre := mono_list_auth_lb_valid γ.log _ _ _ $$ Hlauth Hl0
  have hcmax : cmax < ilog.length := by
    have := Hl0pre.2.length_le; omega
  -- the lock's events are the writer's
  ihave %Hpre := mono_list_auth_lb_valid γ.hist 1 _ _ $$ Hauth HhistL
  ihave %Hcnt := monoNatLbOwn_valid γ.nev 1 _ _ $$ HnevL Hwlb
  have hevs := writer_events ilog ilog' pend pend' Hpre.2 Hcnt.2
  rw [hevs] at HLL
  iunfold mvcc.ownTree at HtreeL
  icases HtreeL with ⟨%Hsorted, Ht, Hkis⟩
  wp_apply (wp_Get mvcc.kiPtrT t mvcc.kiItemIs mvcc.kiItemLess _ _ «$r0_ptr» («$r0_ptr», k))
    $$ [$Ht $Hitem] as %item %ok ⟨Ht, Hres⟩
  · ipureintro; exact mvcc.kiItemLess_swo
  have Hfind := mvcc.btFind_items L Hsorted «$r0_ptr» k
  have Hidx := mvcc.idxGet_entries L Hsorted k
  have hrevm : rev.Main' = W64 ilog.length := congrArg mvcc.Rev.main Hrev
  have hrevs : rev.Sub' = W64 pend.length := congrArg mvcc.Rev.sub Hrev
  have hev : mvcc.evOfChange ilog.length pend.length (.put k v l) =
      { rev := ⟨W64 ilog.length, W64 pend.length⟩, change := .put k v l } := rfl
  have hwf'' : mvcc.IdxWf ilog (pend ++ [.put k v l]) :=
    ⟨Hwf', Hlen, by simp; omega, Hcs⟩
  have hidxnew : mvcc.IdxCRepN cmax (mvcc.evsOf (ilog ++ [pend ++ [.put k v l]]))
      (mvcc.idxPut (mvcc.idxOfEntries L) k ⟨W64 ilog.length, W64 pend.length⟩) := by
    have := mvcc.IdxCRepN.step ilog pend (.put k v l) hwf''.logB hcmax HLL.1
    rw [hev] at this
    exact this
  have hcount : (mvcc.evsOf (ilog ++ [pend ++ [.put k v l]])).length =
      (mvcc.evsOf (ilog ++ [pend])).length + 1 := by
    rw [mvcc.evsOf_append_change, List.length_append, List.length_singleton]
  -- the ghost steps: the event is put, the count grows
  imod monoListAuthOwn_update_app [mvcc.HistItem.ev (mvcc.evOfChange ilog.length pend.length (.put k v l))]
    $$ Hauth with ⟨Hauth, #Hlb'⟩
  imod mono_nat_own_update ((mvcc.evsOf (ilog ++ [pend])).length + 1) (by rw [hevs]; omega)
    $$ HnevL with ⟨HnevL, #Hnlb'⟩
  generalize btFind mvcc.kiItemLess («$r0_ptr», k) (mvcc.itemsOfEntries L) = f at Hfind ⊢
  cases f with
  | none =>
    icases Hres with % ⟨Hok, Hitem0⟩
    subst Hok Hitem0
    have hf : L.find? (fun z => decide (z.2.1 = k)) = none := by
      cases hf : L.find? (fun z => decide (z.2.1 = k)) with
      | none => rfl
      | some z => rw [hf] at Hfind; simp at Hfind
    rw [hf] at Hidx
    simp only [Option.map_none] at Hidx
    (try wp_auto)
    -- `keyi.put(ti.lg, rev.Main, rev.Sub)` on the fresh key index
    ihave Hki : mvcc.ownKi (GF := GF) «$r0_ptr» slice.nil mvcc.KeyIndex.fresh (DFrac.own 1)
        $$ [Kmodified Kgenerations]
    · iunfold mvcc.ownKi
      iframe Kgenerations
      isplitl [Kmodified]
      · rw [show mvcc.revVal mvcc.KeyIndex.fresh.modified = (zeroValDef : Revision) from rfl]
        iexact Kmodified
      iunfold mvcc.ownGens
      iexists []
      isplitl []
      · iapply ownSlice_nil
      isplitl []
      · iapply ownSliceCap_nil
      simp only [mvcc.KeyIndex.fresh, mvcc.ownGensL]
      itrivial
    have Hlt : mvcc.Rev.lt mvcc.Rev.zero ⟨rev.Main', rev.Sub'⟩ := by
      rw [hrevm, hrevs]; exact mvcc.Rev.lt_zero_of_pos _ _ Hilog (by omega)
    wp_apply (hPut «$r0_ptr» slice.nil mvcc.KeyIndex.fresh lg rev.Main' rev.Sub') $$ [$Hki]
      as %r Hr
    · ipureintro; exact Hlgnn
    simp only [Hlt, ↓reduceIte]
    icases Hr with ⟨%Hr, %gs', Hki⟩
    subst Hr
    (try wp_auto)
    -- `ti.tree.ReplaceOrInsert(keyi)`
    wp_apply (wp_ROI mvcc.kiPtrT t mvcc.kiItemIs mvcc.kiItemLess _ «$r0_ptr» («$r0_ptr», k))
      $$ [$Ht $Hitem] as %old %ok2 ⟨Ht, -⟩
    · ipureintro; exact mvcc.kiItemLess_swo
    (try wp_auto)
    -- the deferred `ti.Unlock()`
    rw [method_unfold (t := go.GoType.PointerType treeIndex.ty) (m := go!"Unlock")]
    wp_call
    (try wp_auto)
    ihave HcmpL := mvcc.idxCmpOwn_mono γ _ L
      (btInsert mvcc.entryLess («$r0_ptr», k, mvcc.kiPut mvcc.KeyIndex.fresh ⟨W64 ilog.length, W64 pend.length⟩) L)
      cmax (mvcc.ptrs_btInsert_new L _ (fun w hw hwk => by
        have := List.find?_eq_none.1 hf w hw; simp only [decide_eq_true_eq] at this; exact this hwk)) $$ HcmpL
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk HnevL Ht Hkis Hki HcmpL]
    · inext
      iunfold mvcc.idxLockInv
      iexists ilog, pend ++ [.put k v l],
        btInsert mvcc.entryLess («$r0_ptr», k, mvcc.kiPut mvcc.KeyIndex.fresh ⟨W64 ilog.length, W64 pend.length⟩) L, cmax
      simp only [named]
      rw [← mvcc.histShape_ev, hcount]
      iframe HnevL HcmpL
      isplitl []
      · iexact Hlb'
      isplitl [Ht Hkis Hki]
      · iunfold mvcc.ownTree
        rw [mvcc.itemsOfEntries_btInsert]
        isplitl []
        · ipureintro; exact btInsert_sorted mvcc.kiItemLess_swo Hsorted
        iframe Ht
        iapply mvcc.bigSepL_ownEntry_insert
        iframe Hkis
        iunfold mvcc.ownEntry
        isplitl []
        · ipureintro; exact Hn
        iexists gs'
        rw [← hrevm, ← hrevs]
        iexact Hki
      isplitl []
      · iexact HcrevL
      isplitl []
      · iexists log₀; iframe Hl0; ipureintro; exact Hc0
      ipureintro
      refine ⟨⟨?_, HLL.2⟩, hwf''⟩
      rw [mvcc.idxOfEntries_btInsert]
      simp only [mvcc.idxPut, Hidx] at hidxnew
      exact hidxnew
    (try wp_auto)
    iapply HΦ
    iunfold mvcc.idxWriterP
    iunfold mvcc.idxWriterNR
    rw [← mvcc.histShape_ev, hcount]
    iframe Hrc'
    iframe Hauth Hlauth
    isplitl []
    · iexact Hnlb'
    ipureintro; exact hwf''
  | some w =>
    icases Hres with ⟨%Hok, #Hitemw⟩
    subst Hok
    iunfold mvcc.kiItemIs at Hitemw
    icases Hitemw with ⟨%Hiw, -⟩
    obtain ⟨z, hf, hwz⟩ : ∃ z, L.find? (fun z => decide (z.2.1 = k)) = some z ∧ w = (z.1, z.2.1) := by
      cases hf : L.find? (fun z => decide (z.2.1 = k)) with
      | none => rw [hf] at Hfind; simp at Hfind
      | some z => rw [hf] at Hfind; simp only [Option.map_some, Option.some.injEq] at Hfind; exact ⟨z, rfl, Hfind⟩
    subst hwz
    rw [hf] at Hidx
    simp only [Option.map_some] at Hidx
    obtain ⟨i, hi, hk⟩ := mvcc.find?_entry_getElem? L k z hf
    have hz := (mvcc.IdxCRepN.get_facts HLL.1 Hidx).2.1
    (try wp_auto)
    -- `okeyi.put(ti.lg, rev.Main, rev.Sub)` on the key's index, borrowed from the tree
    icases BigSepL.bigSepL_lookup_acc (Φ := fun _ z => mvcc.ownEntry (GF := GF) z 1) hi |>.1 $$ Hkis
      with ⟨Hz, Hback⟩
    iunfold mvcc.ownEntry at Hz
    icases Hz with ⟨%Hzn, %gs, Hki⟩
    simp only at Hiw
    rw [Hiw]
    have Hlt : mvcc.Rev.lt z.2.2.modified ⟨rev.Main', rev.Sub'⟩ := by
      rw [hrevm, hrevs, hz, mvcc.kiOfKey_eq_kiFold]
      exact mvcc.kiFold_modified_lt k _ _ _ (mvcc.Rev.lt_zero_of_pos _ _ Hilog (by omega))
        (mvcc.evsOf_rev_lt ilog pend (by omega) Hplen)
    wp_apply (hPut z.1 gs z.2.2 lg rev.Main' rev.Sub') $$ [$Hki] as %r Hr
    · ipureintro; exact Hlgnn
    simp only [Hlt, ↓reduceIte]
    icases Hr with ⟨%Hr, %gs', Hki⟩
    subst Hr
    (try wp_auto)
    -- the deferred `ti.Unlock()`
    rw [method_unfold (t := go.GoType.PointerType treeIndex.ty) (m := go!"Unlock")]
    wp_call
    (try wp_auto)
    have hset : mvcc.itemsOfEntries (L.set i (z.1, z.2.1, mvcc.kiPut z.2.2 ⟨W64 ilog.length, W64 pend.length⟩)) =
        mvcc.itemsOfEntries L := mvcc.itemsOfEntries_set L i z _ hi rfl rfl
    ihave HcmpL := mvcc.idxCmpOwn_mono γ _ L
      (L.set i (z.1, z.2.1, mvcc.kiPut z.2.2 ⟨W64 ilog.length, W64 pend.length⟩)) cmax
      (fun p hp => by rwa [mvcc.ptrs_set L i z (z.1, z.2.1, mvcc.kiPut z.2.2 ⟨W64 ilog.length, W64 pend.length⟩) hi rfl]) $$ HcmpL
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk HnevL Ht Hback Hki HcmpL]
    · inext
      iunfold mvcc.idxLockInv
      iexists ilog, pend ++ [.put k v l],
        L.set i (z.1, z.2.1, mvcc.kiPut z.2.2 ⟨W64 ilog.length, W64 pend.length⟩), cmax
      simp only [named]
      rw [← mvcc.histShape_ev, hcount]
      iframe HnevL HcmpL
      isplitl []
      · iexact Hlb'
      isplitl [Ht Hback Hki]
      · iunfold mvcc.ownTree
        rw [hset]
        isplitl []
        · ipureintro; exact Hsorted
        iframe Ht
        iapply Hback
        iunfold mvcc.ownEntry
        isplitl []
        · ipureintro; exact Hzn
        iexists gs'
        rw [← hrevm, ← hrevs]
        iexact Hki
      isplitl []
      · iexact HcrevL
      isplitl []
      · iexists log₀; iframe Hl0; ipureintro; exact Hc0
      ipureintro
      refine ⟨⟨?_, HLL.2⟩, hwf''⟩
      rw [← mvcc.btInsert_idx_set L Hsorted i z (List.getElem?_eq_some_iff.1 hi), hk]
      simp only [mvcc.idxPut, Hidx] at hidxnew
      exact hidxnew
    (try wp_auto)
    iapply HΦ
    iunfold mvcc.idxWriterP
    iunfold mvcc.idxWriterNR
    rw [← mvcc.histShape_ev, hcount]
    iframe Hrc'
    iframe Hauth Hlauth
    isplitl []
    · iexact Hnlb'
    ipureintro; exact hwf''

/-- `treeIndex.Tombstone.wp_proof` with the receipt raised (three lines differ). -/
theorem mvcc.treeIndex.Tombstone.wp_proofP
    (wp_Get : btree.BTree.Get.spec (GF := GF) (hG := hG))
    (hTomb : mvcc.keyIndex.tombstone.spec (GF := GF) (hG := hG)) :
    mvcc.treeIndex.Tombstone.specP (GF := GF) (hG := hG) := by
  have wp_Get : btree.BTree.Get.modelSpec (GF := GF) (hG := hG) := btree.BTree.Get.modelSpec_of wp_Get
  intro ti γ ilog pend key k rev
  wp_start as ⟨#Hti, Hw, #Hkey, %Hpre⟩
  obtain ⟨Hrev, Hilog, Hpend, Hwf'⟩ := Hpre
  ihave Hinit : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨⟨%e, #Herr⟩, -, -, -, -, -, -, -, -⟩
  iunfold mvcc.isTreeIndex at Hti
  iNamed Hti
  iunfold mvcc.idxWriterP at Hw
  iunfold mvcc.idxWriterNR at Hw
  icases Hw with ⟨⟨Hauth, #Hwlb, %Hwwf, Hlauth⟩, #Hrc⟩
  obtain ⟨Hwf, Hlen, Hplen, Hcs⟩ := Hwwf
  wp_auto
  wp_apply wp_with_defer
  iintro %defer Hdefer
  (try wp_auto)
  -- `keyi := &keyIndex{key: key}`
  iStructNamedPrefix «$r0» "K"
  ipersist Kkey
  ihave #Hitem : mvcc.kiItemIs (GF := GF) «$r0_ptr» («$r0_ptr», k) $$ []
  · iunfold mvcc.kiItemIs
    isplitl []
    · ipureintro; rfl
    iunfold mvcc.kiKey
    iexists key
    iframe #
  -- `ti.Lock()`
  rw [method_unfold (t := go.GoType.PointerType treeIndex.ty) (m := go!"Lock")]
  wp_call
  (try wp_auto)
  wp_apply +noauto sync.RWMutex.wp_Lock_guard $$ [$Hmu] as ⟨Hlk, HP⟩
  -- the receipt of the change (D19b), from the next resolution step
  -- the change's step raises the handle's persistent receipt (in place of taking `⧗ 1`)
  wp_raise_receipt Hrc
  ihave #Hrc' : iprop(⧖ (mvcc.logCh ilog + (pend ++ [mvcc.Change.del k]).length)) $$ [Hrc]
  · rw [List.length_append, List.length_singleton, ← Nat.add_assoc]; iexact Hrc
  wp_auto_lc 1
  imod (lc_fupd_elim_later (E := ⊤) (P := mvcc.idxLockInv t γ 1)) $$ Hlc1 HP with HP
  iunfold mvcc.idxLockInv at HP
  icases HP with ⟨%ilog', %pend', %L, %cmax, HP⟩
  iNamedSuffix HP "L"
  -- every compaction level is below the writer's revision
  icases HclL with ⟨%log₀, #Hl0, %Hc0⟩
  ihave %Hl0pre := mono_list_auth_lb_valid γ.log _ _ _ $$ Hlauth Hl0
  have hcmax : cmax < ilog.length := by
    have := Hl0pre.2.length_le; omega
  ihave %Hpre := mono_list_auth_lb_valid γ.hist 1 _ _ $$ Hauth HhistL
  ihave %Hcnt := monoNatLbOwn_valid γ.nev 1 _ _ $$ HnevL Hwlb
  have hevs : mvcc.evsOf (ilog' ++ [pend']) = mvcc.evsOf (ilog ++ [pend]) := by
    have := mvcc.evsOfHist_prefix_eq _ _ Hpre.2
      (by rw [mvcc.evsOfHist_histShape, mvcc.evsOfHist_histShape]; exact Hcnt.2)
    rw [mvcc.evsOfHist_histShape, mvcc.evsOfHist_histShape] at this
    exact this
  rw [hevs] at HLL
  iunfold mvcc.ownTree at HtreeL
  icases HtreeL with ⟨%Hsorted, Ht, Hkis⟩
  wp_apply (wp_Get mvcc.kiPtrT t mvcc.kiItemIs mvcc.kiItemLess _ _ «$r0_ptr» («$r0_ptr», k))
    $$ [$Ht $Hitem] as %item %ok ⟨Ht, Hres⟩
  · ipureintro; exact mvcc.kiItemLess_swo
  have Hfind := mvcc.btFind_items L Hsorted «$r0_ptr» k
  have Hidx := mvcc.idxGet_entries L Hsorted k
  have hrevm : rev.Main' = W64 ilog.length := congrArg mvcc.Rev.main Hrev
  have hrevs : rev.Sub' = W64 pend.length := congrArg mvcc.Rev.sub Hrev
  have hwf'' : mvcc.IdxWf ilog (pend ++ [.del k]) := ⟨Hwf', Hlen, by simp; omega, Hcs⟩
  have hidxnew : mvcc.IdxCRepN cmax (mvcc.evsOf (ilog ++ [pend ++ [.del k]]))
      (mvcc.idxTombstone (mvcc.idxOfEntries L) k ⟨W64 ilog.length, W64 pend.length⟩) := by
    have := mvcc.IdxCRepN.step ilog pend (.del k) hwf''.logB hcmax HLL.1
    rw [mvcc.evOfChange_del] at this
    exact this
  have hb0 : mvcc.LogB (ilog ++ [pend]) := mvcc.IdxWf.logB ⟨Hwf, Hlen, Hplen, Hcs⟩
  have hcount : (mvcc.evsOf (ilog ++ [pend ++ [.del k]])).length =
      (mvcc.evsOf (ilog ++ [pend])).length + 1 := by
    rw [mvcc.evsOf_append_change, List.length_append, List.length_singleton]
  have hlast : mvcc.kiLastEmpty (mvcc.kiOfKey (mvcc.evsOf (ilog ++ [pend])) k) = false :=
    mvcc.kiLastEmpty_false_of_del ilog pend k Hwf Hwf' Hlen Hilog Hplen Hcs
  -- the key has an index (its last generation is not empty)
  obtain ⟨z, hf, hwz⟩ : ∃ z, L.find? (fun z => decide (z.2.1 = k)) = some z ∧
      btFind mvcc.kiItemLess («$r0_ptr», k) (mvcc.itemsOfEntries L) = some (z.1, z.2.1) := by
    cases hf : L.find? (fun z => decide (z.2.1 = k)) with
    | none =>
      exfalso
      rw [hf] at Hidx
      simp only [Option.map_none] at Hidx
      have := mvcc.IdxCRepN.lastEmpty_none HLL.1 Hidx
      rw [this] at hlast
      exact absurd hlast (by decide)
    | some z => exact ⟨z, rfl, by rw [Hfind, hf]; rfl⟩
  rw [hwz]
  icases Hres with ⟨%Hok, #Hitemw⟩
  subst Hok
  iunfold mvcc.kiItemIs at Hitemw
  icases Hitemw with ⟨%Hiw, #HzKey⟩
  rw [hf] at Hidx
  simp only [Option.map_some] at Hidx
  obtain ⟨i, hi, hk⟩ := mvcc.find?_entry_getElem? L k z hf
  obtain ⟨hne0, hz, hzl, hzg⟩ := mvcc.IdxCRepN.get_facts HLL.1 Hidx
  have hlast : mvcc.kiLastEmpty z.2.2 = false := by
    rw [hzl]; exact hlast
  have hne : mvcc.kiIsEmpty z.2.2 = false ∧ z.2.2.gens ≠ [] := ⟨hne0, hzg.1⟩
  -- the ghost steps
  imod monoListAuthOwn_update_app [mvcc.HistItem.ev (mvcc.evOfChange ilog.length pend.length (.del k))]
    $$ Hauth with ⟨Hauth, #Hlb'⟩
  imod mono_nat_own_update ((mvcc.evsOf (ilog ++ [pend])).length + 1) (by rw [hevs]; omega)
    $$ HnevL with ⟨HnevL, #Hnlb'⟩
  (try wp_auto)
  -- `ki.tombstone(ti.lg, rev.Main, rev.Sub)` on the key's index, borrowed from the tree
  icases BigSepL.bigSepL_lookup_acc (Φ := fun _ z => mvcc.ownEntry (GF := GF) z 1) hi |>.1 $$ Hkis
    with ⟨Hz, Hback⟩
  iunfold mvcc.ownEntry at Hz
  icases Hz with ⟨%Hzn, %gs, Hki⟩
  simp only at Hiw
  rw [Hiw]
  have Hlt : mvcc.Rev.lt z.2.2.modified ⟨rev.Main', rev.Sub'⟩ := by
    rw [hrevm, hrevs, hz, mvcc.kiOfKey_eq_kiFold]
    exact mvcc.kiFold_modified_lt k _ _ _ (mvcc.Rev.lt_zero_of_pos _ _ Hilog (by omega))
      (mvcc.evsOf_rev_lt ilog pend (by omega) Hplen)
  wp_apply (hTomb z.1 gs z.2.2 z.2.1 lg rev.Main' rev.Sub' _) $$ [$HzKey $Hki $Herr] as %err Hpost
  · ipureintro; exact ⟨Hlgnn, hne.2⟩
  rw [hne.1, hlast]
  simp only [Hlt, Bool.false_eq_true, ↓reduceIte]
  icases Hpost with ⟨%Herr', %gs', Hki⟩
  subst Herr'
  (try wp_auto)
  -- the deferred `ti.Unlock()`
  rw [method_unfold (t := go.GoType.PointerType treeIndex.ty) (m := go!"Unlock")]
  wp_call
  (try wp_auto)
  have hset : mvcc.itemsOfEntries (L.set i (z.1, z.2.1, mvcc.kiTombstone z.2.2 ⟨W64 ilog.length, W64 pend.length⟩)) =
      mvcc.itemsOfEntries L := mvcc.itemsOfEntries_set L i z _ hi rfl rfl
  ihave HcmpL := mvcc.idxCmpOwn_mono γ _ L
    (L.set i (z.1, z.2.1, mvcc.kiTombstone z.2.2 ⟨W64 ilog.length, W64 pend.length⟩)) cmax
    (fun p hp => by rwa [mvcc.ptrs_set L i z (z.1, z.2.1, mvcc.kiTombstone z.2.2 ⟨W64 ilog.length, W64 pend.length⟩) hi rfl]) $$ HcmpL
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk HnevL Ht Hback Hki HcmpL]
  · inext
    iunfold mvcc.idxLockInv
    iexists ilog, pend ++ [.del k],
      L.set i (z.1, z.2.1, mvcc.kiTombstone z.2.2 ⟨W64 ilog.length, W64 pend.length⟩), cmax
    simp only [named]
    rw [← mvcc.histShape_ev, hcount]
    iframe HnevL HcmpL
    isplitl []
    · iexact Hlb'
    isplitl [Ht Hback Hki]
    · iunfold mvcc.ownTree
      rw [hset]
      isplitl []
      · ipureintro; exact Hsorted
      iframe Ht
      iapply Hback
      iunfold mvcc.ownEntry
      isplitl []
      · ipureintro; exact Hzn
      iexists gs'
      rw [← hrevm, ← hrevs]
      iexact Hki
    isplitl []
    · iexact HcrevL
    isplitl []
    · iexists log₀; iframe Hl0; ipureintro; exact Hc0
    ipureintro
    refine ⟨⟨?_, HLL.2⟩, hwf''⟩
    rw [← mvcc.btInsert_idx_set L Hsorted i z (List.getElem?_eq_some_iff.1 hi), hk]
    simp only [mvcc.idxTombstone, Hidx, hlast, Bool.false_eq_true, ↓reduceIte] at hidxnew
    exact hidxnew
  (try wp_auto)
  iapply HΦ
  iunfold mvcc.idxWriterP
  iunfold mvcc.idxWriterNR
  rw [← mvcc.histShape_ev, hcount]
  iframe Hrc'
  iframe Hauth Hlauth
  isplitl []
  · iexact Hnlb'
  ipureintro; exact hwf''

end put

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

/-- On, the receipt is the restored writer's (`idxWriterP_of_image`). -/
theorem mvcc.restoreRcptM_on (d' : mvcc.KBReal) (L : mvcc.Log) (h : d'.cm = true) :
    mvcc.restoreRcptM (GF := GF) d' L ⊣⊢ ⧖ (mvcc.logCh L) := by
  unfold mvcc.restoreRcptM; simp only [h, ↓reduceIte]; exact .rfl

/-- **Draft of `store.Restore.specM` by sealed logs**: `specM` with the pure premise
`restoreBoundM d' ([[], []] ++ R)` replaced by the persistent receipt `restoreRcptM d' ([[], []] ++
R)` in the pre (first, before `isPkgInit`), which the store's proof keeps in the restored writer's
handle (`idxWriterP_of_image`; item 15's). Everything else is `specM`'s text. -/
abbrev mvcc.store.Restore.specMR : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (b' : GoInterface) (d' : mvcc.KBReal) (γb' : GName)
    (P' : IProp GF) (L R : mvcc.Log) (c : Int) (r : mvcc.CmpRecs),
  L <+: [[], []] ++ R → mvcc.restoreLogOk R → c ≤ r.crev →
  {{ mvcc.restoreRcptM d' ([[], []] ++ R) ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isStore s γ ∗ ⌜∃ d, γ.kb = some d ∧ d'.cm = d.cm⌝ ∗
      mvcc.restoreRightM s γ c ∗ mvcc.fieldShare s γ (1 : Qp).half.half ∗ mvcc.wsDep γ ∗
      mvcc.writerFrag γ ∗ mvcc.writerOwn γ ∗
      mvcc.idxCert γ.idx L ∗ ownToks γ.revs (2 ^ 63 - 3 - L.length) ∗
      (if γ.watchQ then mvcc.logQ γ L else iprop(True)) ∗
      mvcc.certOk γ ([[], []] ++ R) ∗
      (∀ p : mvcc.PhysNames, ⌜p.bucket = γb' ∧ p.kb = some d'⌝ →
        mvcc.restoreFixM d' (γ.withPhys p) -∗ mvcc.storeBackendTR b' s (γ.withPhys p) P' r) ∗
      (∀ p : mvcc.PhysNames, ⌜p.bucket = γb' ∧ p.kb = some d'⌝ →
        mvcc.keyCleanReadR b' (mvcc.bucketViewC (γ.withPhys p))
          iprop(mvcc.storeRT (γ.withPhys p) ∗ mvcc.restoreRegM d')
          (mvcc.kbRecs (γ.withPhys p).kb (γ.withPhys p).bucket r) r) ∗
      mvcc.restoreImageM d' γb' ([[], []] ++ R) r ∗ mvcc.kbRegRight (some d') ∗
      mvcc.restoreRegM d' ∗ mvcc.kbSRM (some d') ∗ mvcc.kbWTSupplyM (some d') ∗ mvcc.resumeHookM d' r ∗
      ([∗list] _x ∈ List.replicate mvcc.nReaders (), mvcc.kbRT (some d')) }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"Restore")) (Val #b'))
  {{ RET #GoInterface.nil; ∃ p' : mvcc.PhysNames,
      ⌜p'.bucket = γb' ∧ p'.kb = some d'⌝ ∗
      mvcc.storeCloserM s (γ.withPhys p') r.crev ∗
      mvcc.fieldShare s γ (1 : Qp).half.half ∗ mvcc.wsDep γ ∗
      mvcc.writerFrag (γ.withPhys p') ∗ mvcc.writerOwn (γ.withPhys p') ∗
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
