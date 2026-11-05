/-
Behaviours Linux has that the extension's semantics (`Impl.lean`) must contain, as concrete
executions: each test exhibits the model's outcome. Untrusted (a check of the trusted definitions).

* `crash_old_name_new_bytes`: create `t`, write `X`, rename `t` to `a`, write `Y`, crash before the
  rename commits: `t` may hold `Y` (the file's writeback does not wait for the journal).
* `crash_lost_after_sync`: a failed sync, then a successful one, then a crash: the sector may hold
  its version from before the failed sync (Linux marked it clean; the later sync did not write it).
* `restart_keeps_dirty`: a process restart keeps the page cache's contents and their dirty sectors,
  so a later machine crash may still lose them.
-/
module

public import GooseLang.Ext.Fs.Impl

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs
namespace Tests

def rootP : GoString := go!"/r"
def tP : GoString := go!"/r/t"
def aP : GoString := go!"/r/a"

def bx : w8 := 1
def byt : w8 := 2

/-- A one-byte file written `X` then `Y` since its creation, never synced. -/
def fXY : OsFile := ((OsFile.ofBytes []).change [bx] 0 1).change [byt] 0 1

theorem secOf_one (b : w8) : (secOf [b] 0).toList[0]? = some b := by
  simp [secOf]

theorem fXY_vers : (fXY.secs 0).vers = [secOf [] 0, secOf [bx] 0, secOf [byt] 0] := by
  simp [fXY, OsFile.change, OsFile.ofBytes, secHits]

/-- Before the crash: the file of inode 0 created at `t`, renamed to `a`, neither committed. -/
def stOld : OsState :=
  { fs := { roots := [rootP], treeDur := {[rootP := .dir]},
            metaLog := [.create tP 0, .rename tP aP], files := {[0 := fXY]} },
    proc := ProcState.empty }

/-- After: the crash kept the create, not the rename; `t` holds `Y`. -/
def stNew : OsState :=
  { fs := { roots := [rootP], treeDur := replay [.create tP 0] {[rootP := .dir]},
            metaLog := [], files := {[0 := OsFile.ofBytes [byt]]} },
    proc := ProcState.empty }

theorem tree_new : stNew.fs.treeDur = <[tP := .file 0]> {[rootP := .dir]} := rfl

theorem named_new (i : Ino) : (∃ p, stNew.fs.treeDur !! p = some (.file i)) ↔ i = 0 := by
  rw [tree_new]
  constructor
  · rintro ⟨p, hp⟩
    by_cases h : tP = p
    · subst h; rw [GMap.lookup_insert_eq] at hp; cases hp; rfl
    · rw [GMap.lookup_insert_ne _ _ h] at hp
      simp at hp
  · rintro rfl; exact ⟨tP, by rw [GMap.lookup_insert_eq]⟩

/-- **A crash may keep the old name with the new bytes.** -/
theorem crash_old_name_new_bytes : OsCrash stOld stNew := by
  left
  refine ⟨rfl, rfl, rfl, ⟨1, by decide, rfl⟩, fun i => ⟨fun hi => ?_, fun hi => ?_⟩⟩
  · obtain rfl := (named_new i).1 hi
    refine ⟨fXY, [byt], by simp [stOld], ?_,
      by simp [stNew]⟩
    refine ⟨⟨.inl ?_, .inl ?_⟩, fun n hn => ?_⟩
    · simp [fXY, OsFile.change, OsFile.ofBytes]
    · simp [fXY, OsFile.change, OsFile.ofBytes]
    · have hn0 : n = 0 := by simp at hn; omega
      subst hn0
      refine ⟨secOf [byt] 0, .inl (by rw [fXY_vers]; simp), fun j hj hl => ?_⟩
      have hj0 : j = 0 := by simp at hl; omega
      subst hj0
      rw [secOf_one]; rfl
  · have : i ≠ 0 := fun h => hi ((named_new i).2 h)
    simp [stNew, Ne.symm this]

/-! ## A failed sync's sector, after a later successful sync -/

/-- A one-byte file holding `X` on disk, written `Y`, then a failed sync, then a successful one. -/
def f1 : OsFile := (OsFile.ofBytes [bx]).change [byt] 0 1
def fLost : OsFile := (f1.syncFailed (fun _ => False)).synced (fun _ => False)

theorem fLost_vers : (fLost.secs 0).vers = [secOf [bx] 0, secOf [byt] 0] := by
  simp [fLost, f1, OsFile.synced, OsFile.syncFailed, OsFile.change, OsFile.ofBytes, secHits]

/-- One file at `a`, its name durable. -/
def oneFile (f : OsFile) : OsState :=
  { fs := { roots := [rootP], treeDur := <[aP := .file 0]> {[rootP := .dir]},
            metaLog := [], files := {[0 := f]} },
    proc := ProcState.empty }

theorem named_one (f : OsFile) (i : Ino) :
    (∃ p, (oneFile f).fs.treeDur !! p = some (.file i)) ↔ i = 0 := by
  constructor
  · rintro ⟨p, hp⟩
    by_cases h : aP = p
    · subst h; simp [oneFile] at hp; exact hp.symm
    · simp only [oneFile] at hp; rw [GMap.lookup_insert_ne _ _ h] at hp; simp at hp
  · rintro rfl; exact ⟨aP, by simp [oneFile]⟩

/-- A machine crash of `oneFile f` leaving the one-byte image `[b]`, from a version of sector 0. -/
theorem crash_one (f : OsFile) (b : w8) (hlo : f.sizeLo ≤ 1) (hhi : 1 ≤ f.sizeHi)
    (hv : secOf [b] 0 ∈ (f.secs 0).vers) :
    OsCrash (oneFile f) (oneFile (OsFile.ofBytes [b])) := by
  left
  refine ⟨rfl, rfl, rfl, ⟨0, by simp [oneFile], rfl⟩, fun i => ⟨fun hi => ?_, fun hi => ?_⟩⟩
  · obtain rfl := (named_one _ i).1 hi
    refine ⟨f, [b], by simp [oneFile], ⟨⟨.inl hlo, .inl hhi⟩, fun n hn => ?_⟩, by simp [oneFile]⟩
    have hn0 : n = 0 := by simp at hn; omega
    subst hn0
    refine ⟨secOf [b] 0, .inl hv, fun j hj hl => ?_⟩
    have hj0 : j = 0 := by simp at hl; omega
    subst hj0
    rw [secOf_one]; rfl
  · have : i ≠ 0 := fun h => hi ((named_one _ i).2 h)
    simp [oneFile, Ne.symm this]

/-- **A lost sector stays lost across a successful sync**: a crash may leave `X`. -/
theorem crash_lost_after_sync : OsCrash (oneFile fLost) (oneFile (OsFile.ofBytes [bx])) :=
  crash_one fLost bx (by simp [fLost, f1, OsFile.synced, OsFile.syncFailed, OsFile.change,
      OsFile.ofBytes]) (by simp [fLost, f1, OsFile.synced, OsFile.syncFailed, OsFile.change,
      OsFile.ofBytes]) (by rw [fLost_vers]; simp)

/-! ## A process restart keeps the dirty sectors -/

theorem changesOn_empty (i : Ino) : changesOn (oneFile f1) i = [] := by
  simp [changesOn, oneFile, ProcState.empty]

/-- **A process restart, then a machine crash**: the restart keeps `Y` unsynced, and the crash may
leave `X`. -/
theorem restart_keeps_dirty :
    OsCrash (oneFile f1) (oneFile f1) ∧ OsCrash (oneFile f1) (oneFile (OsFile.ofBytes [bx])) := by
  refine ⟨.inr ⟨rfl, rfl, rfl, rfl, fun i => ?_⟩, crash_one f1 bx ?_ ?_ ?_⟩
  · by_cases h : i = 0
    · subst h
      simp only [oneFile, GMap.lookup_singleton_eq]
      exact ⟨[], f1, by simp [changesOn, ProcState.empty], .nil _, rfl⟩
    · simp [oneFile, Ne.symm h]
  · simp [f1, OsFile.change, OsFile.ofBytes]
  · simp [f1, OsFile.change, OsFile.ofBytes]
  · simp [f1, OsFile.change, OsFile.ofBytes, secHits]

end Tests
end Fs
end Perennial

end
