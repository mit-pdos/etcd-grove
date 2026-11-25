/- Lean-first (no Rocq counterpart).

# The WAL's records with their history (etcd-dist D6, task T2, 2026-11-24)

`notes/etcd-dist-d6.md` §3, §10. `walRecs h σ` (`WalRecs.lean`, sealed) says the WAL's records are `σ`
and hides the history they fold from. A crash leaves a prefix of that history (from the synced mark
on: `walImg`; with the fork fix of Q1, a complete prefix: `walSaveAtomic.law`), so the server's
crash-aware durability invariant (`InvWalCrash.lean`) must say what every such prefix reads as. This
module exposes the history, as the server reads it (`walSrvHist`), beside the records:
`walRecsH h σ Hs sized` is `walRecs h σ sized` with the history `Hs`, and `walRecs_iff_H` relates
the two; the history's fold is the records (`walRecsH_fold`).

The two durable facts the invariant also uses are the WAL's own: the synced lower bound
`WalFs.walSyncedLb h.dir h.γ.inc n` (persistent; `storage.Save.spec`'s post when the batch must sync) and the
history's growth at each write, which the server's contract states over `walRecsH`
(`InvWalCrash.lean`'s `walSaveH.law`, `walSaveSnapH.law`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.WalRecs
public import Proof.go_etcd_io.etcd.server.v3.storage.WalRecsCrash
import all Proof.go_etcd_io.etcd.server.v3.storage.WalRecs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The WAL `h`'s records are `σ`, its history (as the server reads it) `Hs`** (sealed; exclusive,
timeless): `walRecs h σ sized` with its history named. -/
@[no_expose] def walRecsH (h : WalH GF) (σ : StorContents) (Hs : WalHist) (sized : Bool := false) :
    IProp GF :=
  letI := h.W
  iprop(∃ d : WalDur, WalFs.walDiskAtI h.dir h.γ.inc d ∗ monoListAuthOwn h.γh 1 d.H ∗ WalFs.walNamed h.dir h.γ.inc ∗
    ⌜walFoldChkFrom walFresh (walSrvHist d.H) = some σ ∧ d.metadata = h.md ∧ d.sized = true ∧
      (sized = true → walEntsSized d.H) ∧ walSrvHist d.H = Hs⌝)

instance walRecsH_timeless (h : WalH GF) (σ : StorContents) (Hs : WalHist) (sized : Bool) :
    Timeless (walRecsH (GF := GF) h σ Hs sized) := by
  unfold walRecsH; infer_instance

/-- **The records are the records at some history.** -/
theorem walRecs_iff_H (h : WalH GF) (σ : StorContents) (sized : Bool) :
    walRecs (GF := GF) h σ sized ⊣⊢ ∃ Hs : WalHist, walRecsH h σ Hs sized := by
  unfold walRecs walRecsH
  constructor
  · iintro ⟨%d, Hd, Ha, Hn, %hf⟩
    iexists walSrvHist d.H
    iexists d
    iframe Hd Ha Hn
    ipureintro; exact ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2, rfl⟩
  · iintro ⟨%Hs, %d, Hd, Ha, Hn, %hf⟩
    iexists d
    iframe Hd Ha Hn
    ipureintro; exact ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1⟩

theorem walRecsH_walRecs (h : WalH GF) (σ : StorContents) (Hs : WalHist) (sized : Bool) :
    walRecsH (GF := GF) h σ Hs sized ⊢ walRecs h σ sized := by
  iintro H
  iapply (walRecs_iff_H h σ sized).2
  iexists Hs
  iexact H

/-- **The history folds to the records.** -/
theorem walRecsH_fold (h : WalH GF) (σ : StorContents) (Hs : WalHist) (sized : Bool) :
    walRecsH (GF := GF) h σ Hs sized ⊢ walRecsH h σ Hs sized ∗ ⌜walFoldChkFrom walFresh Hs = some σ⌝ := by
  unfold walRecsH
  iintro ⟨%d, Hd, Ha, Hn, %hf⟩
  isplitl [Hd Ha Hn]
  · iexists d
    iframe Hd Ha Hn
    ipureintro; exact hf
  · ipureintro; rw [← hf.2.2.2.2]; exact hf.1

/-- **The records across a crash** (P8, 2026-11-25; T5's `walFilesC_crash` on the records with their
history): from the crash view (`walCrashWal`, whole operations since P8), the records `σ` at the
history `Hs` (given back), their synced mark `n`, the new generation's lock token and the WAL
directory's call permission's half, a crash prefix `j` (`n ≤ j ≤ |Hs|`) whose read, if it succeeds, the
new generation's files hold (`walFilesC`, at the area with the new generation's WAL names), with the
member `id` of the cluster `cid` the WAL's metadata names. What T2's crash law's callback runs. -/
theorem walRecsH_crash (h : WalH GF) (W' : WalFs.WalGS GF) (σ : StorContents) (Hs : WalHist) (n : Nat)
    (id cid : w64) (hmd : h.md = walMetaEnc id cid) :
    letI := h.ext; letI := h.semOk; letI := h.has
    WalFs.walCrashWal h.W W' ∗ walRecsH h σ Hs true ∗ WalFs.walSyncedLb (W := h.W) h.dir h.γ.inc n ∗
      WalFs.walUnlockedTok (W := W') ∗ Fs.osCallPerm (Fs.callKey h.R h.dir) (1 : Qp).half ⊢
      walRecsH h σ Hs true ∗ ∃ j : Nat, ⌜n ≤ j ∧ j ≤ Hs.length⌝ ∗
        ∀ σ' : StorContents, ⌜walRead (Hs.take j) = some σ'⌝ -∗
          walFilesC { h.toWalA with W := W' } id cid σ' true := by
  letI := h.ext; letI := h.semOk; letI := h.has
  unfold walRecsH
  iintro ⟨Hcs, ⟨%d, Hd, Ha, #Hn, %hf⟩, #Hs, Hu, Hc⟩
  obtain ⟨hfold, hm, hsz, hes, hH⟩ := hf
  icases walFilesC_crash h.toWalA W' h.γ.inc d n id cid (by rw [hm]; exact hmd) hsz (hes rfl) $$
    [Hcs Hd Hs Hn Hu Hc] with ⟨Hd, %j, %hj, Hf⟩
  · iframe Hcs Hd Hs Hn Hu Hc
  isplitl [Hd Ha]
  · iexists d
    iframe Hd Ha Hn
    ipureintro; exact ⟨hfold, hm, hsz, hes, hH⟩
  iexists j
  isplitr
  · ipureintro; rw [← hH]; simpa [walSrvHist] using hj
  iintro %σ' %hr
  iapply Hf
  ipureintro; rw [← hH] at hr; exact hr

end defs

/-! ## The fork fix: a torn `Save` reads as no `Save` (Q1 (a), `notes/etcd-dist-d6.md` §9) -/

/-- **A crash leaves the reads of a complete prefix** (the WAL fork fix of `notes/etcd-dist-d6.md` §9,
decided after T1: `Save` always ends with a state record, `ReadAll` drops the entry records after the
last state record, etcd bootstraps again when the WAL has no state record): for every image `I` a
crash can leave of a history `H` whose first `n` operations are synced (`walImg`, which still has the
torn case: the first `k` entry records of operation `j` without its state record), there is a
complete prefix `H.take j` at or past the mark that every restart read (`walReadCut`, from any purge
position) reads exactly as it reads `I`.

**Superseded (P8, 2026-11-25)**: the WAL's crash view `walCrashWal` now carries the whole-operation
image (`walStCrashS`, `walImgS`), and `walRecsH_crash` gives the crash prefix directly; nothing uses this law.
**False today** (the model's `walRead` reads a torn `Save`'s entries: `walImg`'s second case;
`issues/raft-commit-lost-with-entries-kept.md`); an obligation on the WAL's re-proof after the fork fix
(another task), which may restate it over the fixed model (e.g. a `walImg` without the torn case, when
the trusted reader drops it: then it is immediate with `I = H.take j`). The server's crash-aware
durability invariant (`InvWalCrash.lean`) relies on nothing else of the fix: it says what every
complete prefix from the synced mark reads as. -/
abbrev walSaveAtomic.law [GooseExts] : Prop :=
  ∀ (H I : List (WalOpG WalEnt)) (n : Nat), walImg H n I →
    ∃ j, n ≤ j ∧ j ≤ H.length ∧
      ∀ k, walReadCut (walSrvHist I) k = walReadCut (walSrvHist (H.take j)) k

end EtcdGrove
end Perennial
