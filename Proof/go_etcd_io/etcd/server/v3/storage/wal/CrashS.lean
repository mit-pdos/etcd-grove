/- Lean-first (no Rocq counterpart).

# The WAL's crash view with whole operations (etcd-dist D6, task T5; P6's `walImgS`)

`walInv_crash` (`Crash.lean`) hands the crash obligation the crash view `walCrashWal W W'`, whose
relation `walStCrash s s'` is the abstract disk's `walCrash` of each WAL (`GooseLang/Ext/AbsDisk/
Impl.lean`): an image `walImg` of the history, which still allows a torn `Save` (the first `k`
entries of operation `j`, its state record lost). Since the torn-`Save` fix (P6) the crash the WAL's
invariant proves is narrower: the image is the prefix `H.take j` (`walImgS`, `WalNorm.lean`;
`crashTo_start` has it as `himg` and weakens it by `walImgS_walImg`). A restart reads such an image
as the prefix's `walRead` (the trailing entry records are dropped by `ReadAll`), which is what the
server's crash law needs (`notes/etcd-dist-d6.md` §3, T2's `rnDurK_crash.law`), and which a torn image
does not give: `walRead` would apply its entries.

This module states the narrower view (`walStCrashS`, `walCrashWalS`), its keep lemma
(`walDiskAt_crash_keepS`: the WAL's new state an image `walImgS` of the old history at the synced
mark), and **`walInv_crashS.law`**: `walInv_crash` with `walCrashWalS` in its post. The law is not
proved here: its proof is `walInv_crash`'s, once `crashTo_start`, `CrashGood` and `walCrash_pure`
(`CrashPure.lean`, P6's) return `walImgS` beside `walCrash` (each has it at hand; an added conjunct,
`notes/wal-p8-handoff.md`, "The P6 change P8 needs"). Until then the clients take it as a hypothesis
(the Link pattern). No trusted text: `walImg`/`walCrash` stay the vocabulary of the trusted
extension; `walCrashWalS ⊢ walCrashWal` (`walCrashWalS_weak`) keeps every client of the weak view.
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

/-- **The WAL state's crash relation with whole operations**: `walStCrash`, and every surviving WAL's
new history is a prefix of its old one at or past its synced mark (`walImgS`). -/
def walStCrashS (s s' : AbsDiskState) : Prop :=
  walStCrash s s' ∧
    ∀ dir d d', s.wal !! dir = some d → s'.wal !! dir = some d' → walImgS d.H d.m d'.H

theorem walStCrashS_weak {s s' : AbsDiskState} (h : walStCrashS s s') : walStCrash s s' := h.1

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

/-- **The crash view with whole operations** (`walCrashWal` over `walStCrashS`). -/
def walCrashWalS (W W' : WalGS GF) : IProp GF :=
  iprop(∃ s s' : AbsDiskState, ⌜walStCrashS s s'⌝ ∗ walGhost (W := W) s ∗
    walOwn (W := W') s'.wal ∗ walPast (W := W') s')

/-- The narrower view gives the weak one. -/
theorem walCrashWalS_weak (W W' : WalGS GF) : walCrashWalS W W' ⊢ walCrashWal W W' := by
  unfold walCrashWalS walCrashWal
  iintro ⟨%s, %s', %hc, Hg, HM, Hp⟩
  iexists s, s'
  iframe Hg HM Hp
  ipureintro; exact hc.1

variable (W W' : WalGS GF)

/-- **A named WAL across the crash, with whole operations** (`walDiskAt_crash_keep` over
`walCrashWalS`): its new state is the old one with the history a prefix `walImgS` at the synced mark
`n`, its synced mark and name kept in the new generation. -/
theorem walDiskAt_crash_keepS (dir : GoString) (d : WalDur) (n : Nat) :
    ⊢@{IProp GF} walCrashWalS W W' -∗
      walDiskAt (W := W) dir d -∗ walSyncedLb (W := W) dir n -∗ walNamed (W := W) dir -∗
      walDiskAt (W := W) dir d ∗ ∃ (I : List (WalOpG WalEnt)) (k : Nat),
        ⌜walImgS d.H n I ∧ k ≤ min d.pur I.length⌝ ∗
        walDiskAt (W := W') dir { d with H := I, cut := k, unl := min d.unl I.length, pur := min d.pur I.length } ∗
        walSyncedLb (W := W') dir n ∗ walNamed (W := W') dir := by
  unfold walCrashWalS walDiskAt walDirIs walSyncedLb walNamed
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

/-! ## The law: `walInv_crash` with whole operations -/

section law
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF]

/-- **`walInv_crash` with whole operations** (see the file header): its statement, the crash view
`walCrashWalS`. To be proved by `walInv_crash`'s proof once `walCrash_pure` returns `walStCrashS`
(P6's `CrashPure.lean`, `notes/wal-p8-handoff.md`, "The P6 change P8 needs"). -/
abbrev walInv_crashS.law : Prop :=
  ∀ (C : WalCodec) (_hC : C.Ok) (Mr : WalMarshal) (Q : Fs.OsState → Fs.OsState → Prop)
    (_hQ : ∀ st st', Q st st' → W1 C st st') (_hPre : AbsDiskGpreS GF) (L L' : GooseLocalGS GF)
    (W : WalGS GF) (R : Roots) (jr : Ino) (r : GoString) (V' : Hist) (D : List Ino)
    (_hD : ∀ i ∈ D, ¬ InAreaDir V'.now jr i) (E : CoPset)
    (_hE : ↑walN ⊆ E) (_hE' : ↑osShN ⊆ E),
    ⊢ walInv (L := L) (W := W) C Mr R jr r -∗ crashed (hC := L.goose_crashGS) -∗
      walCrashTok (W := W) -∗ osSharedInv (L := L) R -∗
      crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D false V' ={E}=∗
      ∃ (W' : WalGS GF) (s' : AbsDiskState) (D' : List Ino),
        walCrashWalS W W' ∗
        ⌜W'.roots = R ∧ s'.area = r ∧ DirsAvoid R jr s' ∧ WalsBounded s' ∧ DirsRoots R s' ∧ TreeWf R V'.now ∧
          (∀ nm J, walNameOk nm → V'.now.entry jr nm = some (.dir J) → NoDirX (entsOf V'.now J)) ∧
          (∀ nm J, walNameOk nm → V'.now.entry jr nm = some (.dir J) → ∀ b ∈ walTmps, ∀ J',
            entsOf V'.now J !! b ≠ some (.dir J')) ∧
          ∀ i ∈ D', InAreaDir V'.now jr i⌝ ∗
        walStart L' W' C Mr R jr r s' V'.now ∗
        walPast (W := W') s' ∗ walUnlockedTok (W := W') ∗ walCrashTok (W := W') ∗
        ([∗list] i ∈ bootFiles V'.now jr, trFile (hG := ⟨G, L'⟩) i False) ∗
        crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) (D' ++ D) false V'

end law

end WalFs
end EtcdGrove
end Perennial
