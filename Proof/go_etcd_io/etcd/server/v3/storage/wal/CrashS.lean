/- Lean-first (no Rocq counterpart).

# The WAL's crash with whole operations (etcd-dist D6, task T5; P6's `walImgS`)

`walInv_crash` (`Crash.lean`) hands the crash obligation the crash view `walCrashWal W W'`. Since P8
(2026-11-25) its relation is `walStCrashS s s'` (`CrashPure.lean`): the abstract disk's `walCrash` of each
WAL (`GooseLang/Ext/AbsDisk/Impl.lean`, whose image `walImg` still allows a torn `Save`: the first `k`
entries of operation `j`, its state record lost) **and** the narrower image the WAL's invariant proves
since the torn-`Save` fix: the prefix `H.take j` (`walImgS`, `WalNorm.lean`; `crashTo_start` returns it
beside `walCrash`). A restart reads such an image as the prefix's `walRead` (the trailing entry records
are dropped by `ReadAll`), which is what the server's crash law needs (`notes/etcd-dist-d6.md` §3, T2's
`rnDurK_crash.law`), and which a torn image does not give: `walRead` would apply its entries.

This module has the keep lemma that exposes it (`walDiskAt_crash_keepS`: the WAL's new state an image
`walImgS` of the old history at the synced mark). No trusted text: `walImg`/`walCrash` stay the
vocabulary of the trusted extension; the `_keep` lemmas of `Crash.lean` still give `walImg`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.Crash

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section pure
variable [GooseExts]

/-- A whole-operation image at a mark is one at any lower mark. -/
theorem walImgS_mono {E : Type} {H I : List (WalOpG E)} {n n' : Nat} (hn : n ≤ n')
    (h : walImgS H n' I) : walImgS H n I := by
  obtain ⟨j, h1, h2, h3⟩ := h
  exact ⟨j, Nat.le_trans hn h1, h2, h3⟩

end pure

section crash
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF]

variable (W W' : WalGS GF)

/-- **A named WAL across the crash, with whole operations** (`walDiskAt_crash_keep`, with
the crash's whole-operation image): its new state is the old one with the history a prefix `walImgS` at the synced mark
`n`, its synced mark and name kept in the new generation. -/
theorem walDiskAt_crash_keepS (dir : GoString) (d : WalDur) (n : Nat) :
    ⊢@{IProp GF} walCrashWal W W' -∗
      walDiskAt (W := W) dir d -∗ walSyncedLb (W := W) dir n -∗ walNamed (W := W) dir -∗
      walDiskAt (W := W) dir d ∗ ∃ (I : List (WalOpG WalEnt)) (k : Nat),
        ⌜walImgS d.H n I ∧ k ≤ min d.pur I.length⌝ ∗
        walDiskAt (W := W') dir { d with H := I, cut := k, unl := min d.unl I.length, pur := min d.pur I.length } ∗
        walSyncedLb (W := W') dir n ∗ walNamed (W := W') dir := by
  unfold walCrashWal walDiskAt walDirIs walSyncedLb walNamed
  iintro ⟨%s, %s', %hcS, HG, HM', #Hp'⟩ ⟨%M, HM, %HMd⟩ ⟨%p, %dp, Hp, %Hdp⟩ ⟨%q, %dq, Hq, %Hdq⟩
  icases walOwn_agree (W := W) s M $$ HG HM with %HMs
  obtain ⟨dr, hdr, hle⟩ := walDiskAt_crash_real HMd HMs
  icases walPast_ghost_le (W := W) s p $$ HG Hp with %Hlp
  icases walPast_ghost_le (W := W) s q $$ HG Hq with %Hlq
  obtain ⟨d1, h1, hm1, -, -⟩ := Hlp.2.2 dir dp Hdp.1
  obtain ⟨d2, h2, -, -, hn2⟩ := Hlq.2.2 dir dq Hdq.1
  rw [hdr] at h1 h2; cases h1; cases h2
  have hn : n ≤ dr.m := Nat.le_trans Hdp.2 hm1
  have hnamed : dr.named = true := hn2 Hdq.2
  obtain ⟨⟨-, -, hcw, -⟩, hS⟩ := hcS
  rcases hcw dir dr hdr with ⟨hnf, -⟩ | ⟨I, k, -, hk, hs'⟩
  · rw [hnamed] at hnf; cases hnf
  have hIS : walImgS dr.H n I := walImgS_mono hn (hS dir dr _ hdr hs')
  isplitl [HM]
  · iexists M; iframe HM; ipureintro; exact HMd
  iexists I, k
  isplitr
  · ipureintro
    refine ⟨?_, ?_⟩
    · rw [hle.1]; exact hIS
    · rw [hle.2.2.1]; exact hk
  isplitl [HM']
  · iexists s'.wal; iframe HM'; ipureintro; rw [hs']; exact walDurLe_crash hle
  isplitr
  · iexists s', _; iframe Hp'; ipureintro; exact ⟨hs', hn⟩
  · iexists s', _; iframe Hp'; ipureintro; exact ⟨hs', hnamed⟩

end crash

end WalFs
end EtcdGrove
end Perennial
