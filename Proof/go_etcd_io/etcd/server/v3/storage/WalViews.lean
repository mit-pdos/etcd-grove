/-
**Views over the WAL's axioms** (WAL W4b, 2026-11-12; `/shared/tmp/wal-spec/w4b/plan.md` §2 B, approved
by etcd-grove-81). Proved; no trusted text. The crash in the tester's terms (B2: the new generation's
WAL is at an image of the history, its purge positions bounded by the old ones), its graceful instance,
and the conversion to `walDisk` (B1's first half; the `walDiskM` half waits for W4a.1).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.WalHistLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

/-! ## B2. The crash, in the tester's terms -/

section crashGen
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt absDiskExt] [GoGlobalContext]
  [go.IntoValInj GoString]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable (L' : GooseLocalGS GF)

/-- What a crash keeps of a WAL's durable state `d` in the new one `d'`, at a mark `n`: `d'`'s history
an image of `d`'s at `n` (raw, and over the model's entries), the read position within the purge
position, the purge and unlock positions `d`'s clamped to the image, the mark, metadata, flags kept. -/
def walCrashKeeps (d d' : WalDur) (n : Nat) : Prop :=
  walImg d.H n d'.H ∧ walImg (d.H.map WalOpG.toM) n (d'.H.map WalOpG.toM) ∧
  d'.cut ≤ d'.pur ∧ d'.pur = min d.pur d'.H.length ∧ d'.unl = min d.unl d'.H.length ∧
  d'.m = d.m ∧ d'.metadata = d.metadata ∧ d'.named = d.named ∧ d'.sized = d.sized

theorem walCrashKeeps_of {d : WalDur} {n : Nat} {I : List (WalOpG WalEnt)} {k : Nat}
    (hI : walImg d.H n I) (hk : k ≤ min d.pur I.length) :
    walCrashKeeps d { d with H := I, cut := k, unl := min d.unl I.length, pur := min d.pur I.length } n :=
  ⟨hI, walImg_map WalOpG.toM WalEnt.toM (fun _ _ => rfl) hI, hk, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The crash of a named WAL, in the tester's terms** (`walDiskAt_crash` with A1): the new
generation's WAL is at some `d'` that `walCrashKeeps` relates to `d` at the synced mark `n`. -/
theorem walDiskAt_crash_img (dir : GoString) (d : WalDur) (n : Nat) :
    ⊢@{IProp GF} absDiskCrashWal (gooseAbsDiskGS (L := L)) (gooseAbsDiskGS (L := L')) -∗
      walDiskAt (L := L) dir d -∗ walSyncedLb (L := L) dir n -∗ walNamed (L := L) dir -∗
      ∃ d' : WalDur, ⌜walCrashKeeps d d' n⌝ ∗ walDiskAt (L := L') dir d' ∗
        walSyncedLb (L := L') dir n ∗ walNamed (L := L') dir := by
  iintro Hcs Hd Hs Hn
  icases walDiskAt_crash (L := L) L' dir d n $$ Hcs Hd Hs Hn with ⟨%I, %k, ⟨%hI, %hk⟩, Hd', Hs', Hn'⟩
  iexists _
  iframe Hd' Hs' Hn'
  ipureintro; exact walCrashKeeps_of hI hk

/-- **The crash of a WAL whose entry may not be durable**, in the same terms. -/
theorem walDiskAt_crash_img_any (dir : GoString) (d : WalDur) (n : Nat) :
    ⊢@{IProp GF} absDiskCrashWal (gooseAbsDiskGS (L := L)) (gooseAbsDiskGS (L := L')) -∗
      walDiskAt (L := L) dir d -∗ walSyncedLb (L := L) dir n -∗
      ((walAbsent (L := L') dir ∗ ⌜d.named = false⌝) ∨
        ∃ d' : WalDur, ⌜walCrashKeeps d d' n⌝ ∗ walDiskAt (L := L') dir d' ∗
          walSyncedLb (L := L') dir n) := by
  iintro Hcs Hd Hs
  icases walDiskAt_crash_any (L := L) L' dir d n $$ Hcs Hd Hs with
    (Ha | ⟨%I, %k, ⟨%hI, %hk⟩, Hd', Hs'⟩)
  · ileft; iexact Ha
  · iright
    iexists _
    iframe Hd' Hs'
    ipureintro; exact walCrashKeeps_of hI hk

/-- **The graceful instance**: with the whole history synced, the crash keeps it, and the restart
reads from some `k ≤ min pur |H|` (restart S3's identity instance, its image half). -/
theorem walDiskAt_crash_graceful (dir : GoString) (d : WalDur) :
    ⊢@{IProp GF} absDiskCrashWal (gooseAbsDiskGS (L := L)) (gooseAbsDiskGS (L := L')) -∗
      walDiskAt (L := L) dir d -∗ walSyncedLb (L := L) dir d.H.length -∗ walNamed (L := L) dir -∗
      ∃ k : Nat, ⌜k ≤ min d.pur d.H.length⌝ ∗
        walDiskAt (L := L') dir { d with cut := k, unl := min d.unl d.H.length, pur := min d.pur d.H.length } ∗
        walSyncedLb (L := L') dir d.H.length ∗ walNamed (L := L') dir := by
  iintro Hcs Hd Hs Hn
  icases walDiskAt_crash (L := L) L' dir d d.H.length $$ Hcs Hd Hs Hn with
    ⟨%I, %k, ⟨%hI, %hk⟩, Hd', Hs', Hn'⟩
  have hIH : I = d.H := walImg_full.1 hI
  subst hIH
  iexists k
  iframe Hd' Hs' Hn'
  ipureintro; exact hk

end crashGen

/-! ## B1. Conversions -/

section views
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt absDiskExt] [go_gctx : GoGlobalContext]
  [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]

/-- **The exact durable state gives the history view.** -/
theorem walDiskAt_walDisk (dir : GoString) (d : WalDur) :
    walDiskAt dir d ⊢@{IProp GF} walDisk dir (d.H.map WalOpG.toM) d.sized := by
  unfold walDisk
  iintro Hd
  iexists d
  iframe Hd
  ipureintro; exact ⟨rfl, rfl⟩

/-- **One history view of a directory** (of any directory: the view owns the whole WAL map). -/
theorem walDisk_excl (dir dir' : GoString) (H H' : WalHist) (s s' : Bool) :
    ⊢@{IProp GF} walDisk dir H s -∗ walDisk dir' H' s' -∗ False := by
  unfold walDisk walDiskAt
  iintro ⟨%d, Hd, -⟩ ⟨%d', Hd', -⟩
  iapply walDirIs_excl $$ Hd Hd'

end views

end EtcdGrove
end Perennial
