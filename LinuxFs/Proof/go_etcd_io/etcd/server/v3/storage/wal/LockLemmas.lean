/-
The WAL's locked files (2026-11-15, the lock semantics, `notes/wal-units/locks.md`): a segment file
`fileutil.LockFile`/`TryLockFile` opened is described by `fileutil.lkFd k i flag` (the open's
description with an exclusive lock of kind `k`) and holds the lock's token `osLock k i fd`; the WAL's
generic file predicates (the tail, `walLockH`, `wal.rcFile`, `walFileS`) hold `osFd fd 1 d ∗ fdLocks fd d`:
`d`'s tokens (`lockToks`, what `Close` takes back) and, persistently, that each lock `d` holds is of
`fileutil`'s kind (`fdKindOk d`; what a purger's lock of the same file is compared with:
`fileutil.lockKind_agree`). These lemmas move between the forms.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.client.pkg.v3.fileutil.LockDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Fs

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- A locked description's fields: the open's, with the lock of kind `k`. -/
theorem lkFd_eta (k : LockKind) (i : Ino) (fl : w64) :
    fileutil.lkFd k i fl = ⟨i, (openFd i (fl ||| W64 0x80000)).readable,
      (openFd i (fl ||| W64 0x80000)).writable, (fileutil.lkFd k i fl).ofd,
      (fileutil.lkFd k i fl).flk⟩ := by
  cases k <;> rfl

theorem lkFd_ino (k : LockKind) (i : Ino) (fl : w64) : (fileutil.lkFd k i fl).ino = i := by
  cases k <;> rfl

theorem lkFd_lk (k : LockKind) (i : Ino) (fl : w64) : (fileutil.lkFd k i fl).lk k = some true := by
  cases k <;> rfl

/-- A locked description's tokens are its lock's token. -/
theorem lkFd_toks (k : LockKind) (i : Ino) (fl : w64) (fd : w64) :
    lockToks (GF := GF) fd (fileutil.lkFd k i fl) ⊣⊢ osLock (GF := GF) k i fd := by
  unfold lockToks
  cases k with
  | ofd =>
    have h1 := lockTok_some (GF := GF) .ofd fd (fileutil.lkFd .ofd i fl) rfl
    rw [lkFd_ino] at h1
    constructor
    · iintro ⟨H1, -⟩; iapply h1.1 $$ H1
    · iintro H; isplitl [H]
      · iapply h1.2 $$ H
      · iapply lockTok_none; simp [fileutil.lkFd, OsFd.setLk, OsFd.lk, openFd]
  | flock =>
    have h1 := lockTok_some (GF := GF) .flock fd (fileutil.lkFd .flock i fl) rfl
    rw [lkFd_ino] at h1
    constructor
    · iintro ⟨-, H1⟩; iapply h1.1 $$ H1
    · iintro H; isplitr [H]
      · iapply lockTok_none; simp [fileutil.lkFd, OsFd.setLk, OsFd.lk, openFd]
      · iapply h1.2 $$ H

/-- Each exclusive lock the description `d` holds is of `fileutil`'s kind (see the file header). -/
def fdKindOk (d : OsFd) : IProp GF :=
  iprop(∀ k : LockKind, ⌜d.lk k = some true⌝ → fileutil.lockKind k)

instance fdKindOk_persistent (d : OsFd) : Persistent (fdKindOk (GF := GF) d) := by
  unfold fdKindOk; infer_instance

/-- The locks of a WAL file's description (see the file header). -/
def fdLocks (fd : w64) (d : OsFd) : IProp GF :=
  iprop(lockToks fd d ∗ fdKindOk d)

theorem fdKindOk_unlocked (d : OsFd) (h1 : d.ofd = none) (h2 : d.flk = none) :
    ⊢ fdKindOk (GF := GF) d := by
  unfold fdKindOk
  iintro %k %hk
  exfalso
  cases k <;> simp [OsFd.lk, h1, h2] at hk

theorem fdLocks_unlocked (fd : w64) (d : OsFd) (h1 : d.ofd = none) (h2 : d.flk = none) :
    ⊢ fdLocks (GF := GF) fd d := by
  unfold fdLocks
  isplitl []
  · iapply lockToks_unlocked <;> assumption
  · iapply fdKindOk_unlocked <;> assumption

theorem fdLocks_openFd (fd : w64) (i : Ino) (fl : w64) :
    ⊢ fdLocks (GF := GF) fd (openFd i fl) :=
  fdLocks_unlocked fd _ rfl rfl

theorem fdLocks_toks (fd : w64) (d : OsFd) : fdLocks (GF := GF) fd d ⊢ lockToks fd d := by
  unfold fdLocks; iintro ⟨H, -⟩; iexact H

theorem lkFd_kindOk (k : LockKind) (i : Ino) (fl : w64) :
    fileutil.lockKind (GF := GF) k ⊢ fdKindOk (GF := GF) (fileutil.lkFd k i fl) := by
  unfold fdKindOk
  iintro #H %k' %hk
  have : k' = k := by
    cases k <;> cases k' <;> first | rfl | simp [fileutil.lkFd, OsFd.setLk, OsFd.lk, openFd] at hk
  subst this
  iexact H

/-- What `LockFile`/`TryLockFile` give, as a WAL file's locks. -/
theorem lkFd_locks (k : LockKind) (i : Ino) (fl : w64) (fd : w64) :
    osLock (GF := GF) k i fd ∗ fileutil.lockKind (GF := GF) k ⊢
      fdLocks (GF := GF) fd (fileutil.lkFd k i fl) := by
  unfold fdLocks
  iintro ⟨H, #Hk⟩
  isplitl [H]
  · iapply (lkFd_toks k i fl fd).2 $$ H
  · iapply lkFd_kindOk $$ Hk

/-- `LockFile`/`TryLockFile`'s success, in the WAL's form: the fd's description as a literal (its access
mode `rd`/`wr`, the open's), with its locks. -/
theorem lkFd_open (k : LockKind) (i : Ino) (fl : w64) (fd : w64) (rd wr : Bool)
    (hrd : (openFd i (fl ||| W64 0x80000)).readable = rd)
    (hwr : (openFd i (fl ||| W64 0x80000)).writable = wr) :
    osFd (GF := GF) fd (DFrac.own 1) (fileutil.lkFd k i fl) ∗ osLock (GF := GF) k i fd ∗
        fileutil.lockKind (GF := GF) k ⊢
      ∃ lo lk : Option Bool, osFd (GF := GF) fd (DFrac.own 1) ⟨i, rd, wr, lo, lk⟩ ∗
        fdLocks (GF := GF) fd ⟨i, rd, wr, lo, lk⟩ := by
  have e := lkFd_eta k i fl
  rw [hrd, hwr] at e
  iintro ⟨Hfd, Hl, #Hk⟩
  ihave Hls := lkFd_locks k i fl fd $$ [$Hl $Hk]
  generalize fileutil.lkFd k i fl = d at e ⊢
  rw [e]
  iexists d.ofd, d.flk
  iframe

end lemmas

end EtcdGrove
end Perennial
