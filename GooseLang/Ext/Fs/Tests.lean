/-
Behaviours Linux has that the extension's semantics (`Impl.lean`) must contain, as concrete
executions: each test exhibits the model's outcome. Untrusted (a check of the trusted definitions).

* `crash_old_name_new_bytes`: create `t`, write `X`, rename `t` to `a`, write `Y`, crash before the
  rename commits: `t` may hold `Y` (the file's writeback does not wait for the journal).
* `crash_lost_after_sync`: a failed sync, then a successful one, then a crash: the sector may hold
  its version from before the failed sync (Linux marked it clean; the later sync did not write it).
* `crash_loses_unsynced`: a machine crash may lose a write that was never synced.
* `crash_overlap`: two overlapping calls in disjoint directories (a rename of the file `a` to `d`,
  and a create in `c/x` begun before the rename took effect): a crash may keep the create without
  the rename.
* `dirsync_new_dir` (a guarantee): after a successful `fsync` of the root, every crash keeps the
  directory made in it during the same run.
* `rmdir_open_fd`: `rmdir` of an empty directory succeeds while an fd is open on it.
-/
module

public import GooseLang.Ext.Fs.Lookup
public import Perennial.Golang.Defn.PostLang

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs
namespace Tests

def rootP : GoString := go!"/r"
def tB : GoString := go!"t"
def aB : GoString := go!"a"

def bx : w8 := 1
def byt : w8 := 2

/-- A one-byte file written `X` then `Y` since its creation, never synced. -/
def fXY : OsFile := ((OsFile.ofBytes []).change [bx] 0 1).change [byt] 0 1

theorem secOf_one (b : w8) : (secOf [b] 0).toList[0]? = some b := by
  simp [secOf]

theorem secOf_far (c : List w8) (hc : c.length ≤ 1) (n : Nat) (h : 1 ≤ n) :
    secOf c n = secOf [] n := by
  unfold secOf; congr 1; funext j
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega),
    List.getElem?_nil]

theorem fXY_vers : (fXY.secs 0).vers = [secOf [] 0, secOf [bx] 0, secOf [byt] 0] := by
  simp [fXY, OsFile.change, OsFile.ofBytes, OsFile.ofDisk, secHits]

/-- Before the crash: the file of inode 0 created as `t` in the root (inode 1), renamed to `a`,
neither committed. -/
def stOld : OsState :=
  { fs := { roots := [(rootP, 1)], treeDur := {[1 := ∅]},
            metaLog := [⟨.create 1 tB 0, 0⟩, ⟨.rename 1 tB 1 aB (.file 0) none, 1⟩],
            committed := fun _ => False, files := {[0 := fXY]}, nextIno := 2 },
    proc := ProcState.empty }

/-- After: the crash kept the create, not the rename; `t` holds `Y`. -/
def stNew : OsState :=
  { fs := { roots := [(rootP, 1)], treeDur := replay [.create 1 tB 0] {[1 := ∅]},
            metaLog := [], committed := fun _ => False, files := {[0 := OsFile.ofBytes [byt]]},
            nextIno := 2 },
    proc := ProcState.empty }

theorem entry_new (j : Ino) (b : GoString) :
    stNew.fs.treeDur.entry j b = if j = 1 ∧ b = tB then some (.file 0) else none := by
  simp only [stNew, replay, List.foldl, MetaOp.apply, Tree.upd, Tree.entry]
  by_cases hj : j = 1
  · subst hj; by_cases hb : b = tB
    · subst hb; simp
    · simp [hb, Ne.symm hb]
  · simp [hj, Ne.symm hj]

theorem named_new (i : Ino) : Named stNew.fs.treeDur i ↔ i = 0 := by
  constructor
  · rintro ⟨j, b, h⟩
    rw [entry_new] at h; split at h
    · cases h; rfl
    · cases h
  · rintro rfl; exact ⟨1, tB, by rw [entry_new]; simp⟩

theorem keptOps_first :
    keptOps stOld.fs.metaLog (fun x => x = 0) = [.create 1 tB 0] := by
  simp [keptOps, stOld, List.range_succ]

theorem closed_first : Closed stOld.fs.metaLog (fun x => x = 0) := by
  intro x y hx hf; subst hx; exact absurd hf.1 (Nat.not_lt_zero _)

/-- **A crash may keep the old name with the new bytes.** -/
theorem crash_old_name_new_bytes : OsCrash stOld stNew := by
  refine ⟨rfl, rfl, rfl, fun _ h => h, rfl,
    ⟨fun x => x = 0, fun x hx => by simp [hx, stOld], fun _ h => h.elim, closed_first,
      by rw [keptOps_first]; rfl⟩, fun i => ⟨fun hi => ?_, fun hi => ?_⟩⟩
  · obtain rfl := (named_new i).1 hi
    refine ⟨fXY, OsFile.ofBytes [byt], by simp [stOld], ?_, by simp [stNew]⟩
    refine ⟨1, secOf [byt], ⟨.inl ?_, .inl ?_⟩, fun n => .inl ?_, rfl⟩
    · simp [fXY, OsFile.change, OsFile.ofBytes, OsFile.ofDisk]
    · simp [fXY, OsFile.change, OsFile.ofBytes, OsFile.ofDisk]
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [fXY_vers]; simp
      · rw [secOf_far _ (by simp) n hn]
        have h0 : 512 * n ≠ 0 := by omega
        simp [fXY, OsFile.change, OsFile.ofBytes, OsFile.ofDisk, secHits, h0]
  · have : i ≠ 0 := fun h => hi ((named_new i).2 h)
    simp [stNew, Ne.symm this]

/-! ## A failed sync's sector, after a later successful sync -/

/-- A one-byte file holding `X` on disk, written `Y`, then a failed sync, then a successful one. -/
def f1 : OsFile := (OsFile.ofBytes [bx]).change [byt] 0 1
def fLost : OsFile := (f1.syncFailed (fun _ => False)).synced (fun _ => False)

theorem fLost_vers : (fLost.secs 0).vers = [secOf [bx] 0, secOf [byt] 0] := by
  simp [fLost, f1, OsFile.synced, OsFile.syncFailed, OsFile.change, OsFile.ofBytes, OsFile.ofDisk,
    secHits]

/-- One file, named `a` in the root, its name durable. -/
def oneFile (f : OsFile) : OsState :=
  { fs := { roots := [(rootP, 1)], treeDur := {[1 := {[aB := .file 0]}]},
            metaLog := [], committed := fun _ => False, files := {[0 := f]}, nextIno := 2 },
    proc := ProcState.empty }

theorem named_one (f : OsFile) (i : Ino) : Named (oneFile f).fs.treeDur i ↔ i = 0 := by
  constructor
  · rintro ⟨j, b, h⟩
    simp only [oneFile, Tree.entry] at h
    by_cases hj : j = 1
    · subst hj; by_cases hb : b = aB
      · subst hb; simp at h; exact h.symm
      · simp [Ne.symm hb] at h
    · simp [Ne.symm hj] at h
  · rintro rfl; exact ⟨1, aB, by simp [oneFile, Tree.entry]⟩

/-- A machine crash of `oneFile f` leaving the one-byte file `[b]`, from versions of its sectors. -/
theorem crash_one (f : OsFile) (b : w8) (hlo : f.sizeLo ≤ 1) (hhi : 1 ≤ f.sizeHi)
    (hv : secOf [b] 0 ∈ (f.secs 0).vers) (hz : ∀ n, 1 ≤ n → secOf [] n ∈ (f.secs n).vers) :
    OsCrash (oneFile f) (oneFile (OsFile.ofBytes [b])) := by
  refine ⟨rfl, rfl, rfl, fun _ h => h, rfl,
    ⟨fun _ => False, fun _ h => h.elim, fun _ h => h, fun _ _ h => h.elim, rfl⟩,
    fun i => ⟨fun hi => ?_, fun hi => ?_⟩⟩
  · obtain rfl := (named_one _ i).1 hi
    refine ⟨f, OsFile.ofBytes [b], by simp [oneFile], ?_, by simp [oneFile]⟩
    refine ⟨1, secOf [b], ⟨.inl hlo, .inl hhi⟩, fun n => .inl ?_, rfl⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact hv
    · rw [secOf_far _ (by simp) n hn]; exact hz n hn
  · have : i ≠ 0 := fun h => hi ((named_one _ i).2 h)
    simp [oneFile, Ne.symm this]

/-- **A lost sector stays lost across a successful sync**: a crash may leave `X`. -/
theorem crash_lost_after_sync : OsCrash (oneFile fLost) (oneFile (OsFile.ofBytes [bx])) :=
  crash_one fLost bx (by simp [fLost, f1, OsFile.synced, OsFile.syncFailed, OsFile.change,
      OsFile.ofBytes, OsFile.ofDisk]) (by simp [fLost, f1, OsFile.synced, OsFile.syncFailed, OsFile.change,
      OsFile.ofBytes, OsFile.ofDisk]) (by rw [fLost_vers]; simp) (fun n hn => by
      simp [fLost, f1, OsFile.synced, OsFile.syncFailed, OsFile.change, OsFile.ofBytes, OsFile.ofDisk,
        OsFile.ofDisk, secHits, Sector.last]
      have h0 : 512 * n ≠ 0 := by omega
      rw [secOf_far _ (by simp) n hn]; simp [h0])

/-! ## Unsynced bytes may be lost -/

/-- **A machine crash may lose a write that was never synced**: `Y` written over `X`, no sync;
the crash may leave `X`. (A process's restart is a machine crash, by the environment's assumption
on restarts.) -/
theorem crash_loses_unsynced : OsCrash (oneFile f1) (oneFile (OsFile.ofBytes [bx])) := by
  refine crash_one f1 bx ?_ ?_ ?_ ?_
  · simp [f1, OsFile.change, OsFile.ofBytes, OsFile.ofDisk]
  · simp [f1, OsFile.change, OsFile.ofBytes, OsFile.ofDisk]
  · simp [f1, OsFile.change, OsFile.ofBytes, OsFile.ofDisk, secHits]
  · intro n hn
    have h0 : 512 * n ≠ 0 := by omega
    simp [f1, OsFile.change, OsFile.ofBytes, OsFile.ofDisk, secHits, h0]
    exact (secOf_far _ (by simp) n hn).symm

/-! ## Overlapping calls in disjoint directories: either may survive alone -/

def cB : GoString := go!"c"
def dB : GoString := go!"d"
def xB : GoString := go!"x"
def yB : GoString := go!"y"

/-- `/r/a`, a file (inode 7); `/r/c/x`, directories 4 and 5. -/
def tree3 : Tree :=
  <[1 := <[aB := .file 7]> {[cB := .dir 4]}]> (<[4 := {[xB := .dir 5]}]> {[5 := ∅]})

/-- Two overlapping calls: the rename of the file `a` to `d` took effect first; the create of `y` in
`/r/c/x` had begun before it did. -/
def stOv : OsState :=
  { fs := { roots := [(rootP, 1)], treeDur := tree3,
            metaLog := [⟨.rename 1 aB 1 dB (.file 7) none, 0⟩, ⟨.create 5 yB 6, 0⟩],
            committed := fun _ => False, files := <[6 := newFile]> {[7 := newFile]}, nextIno := 8 },
    proc := ProcState.empty }

/-- After a crash that kept the create but not the rename. -/
def stOv' : OsState :=
  { fs := { roots := [(rootP, 1)], treeDur := replay [.create 5 yB 6] tree3,
            metaLog := [], committed := fun _ => False,
            files := <[6 := OsFile.ofBytes []]> {[7 := OsFile.ofBytes []]}, nextIno := 8 },
    proc := ProcState.empty }

theorem named_ov (i : Ino) : Named stOv'.fs.treeDur i ↔ i = 6 ∨ i = 7 := by
  constructor
  · rintro ⟨j, b, h⟩
    simp [stOv', tree3, replay, MetaOp.apply, Tree.upd, Tree.entry] at h
    by_cases h5 : 5 = j
    · simp [h5] at h
      by_cases hb : yB = b
      · simp [hb] at h; exact .inl h.symm
      · simp [hb] at h
    · simp [h5] at h
      by_cases h1 : 1 = j
      · simp [h1] at h
        by_cases hb : aB = b
        · simp [hb] at h; exact .inr h.symm
        · simp [hb] at h
      · simp [h1] at h
        by_cases h4 : 4 = j
        · simp [h4] at h
        · simp [h4] at h
  · rintro (rfl | rfl)
    · exact ⟨5, yB, by simp [stOv', tree3, replay, MetaOp.apply, Tree.upd, Tree.entry]⟩
    · exact ⟨1, aB, by simp [stOv', tree3, replay, MetaOp.apply, Tree.upd, Tree.entry]⟩

/-- **Overlapping calls in disjoint directories**: a crash may keep the create in `/r/c/x` without
the rename of `/r/a` that took effect before it (they lock no common directory; the create's call
began before the rename took effect, so the journal may have either first). -/
theorem crash_overlap : OsCrash stOv stOv' := by
  refine ⟨rfl, rfl, rfl, fun _ h => h, rfl,
    ⟨fun x => x = 1, fun x hx => by simp [hx, stOv], fun _ h => h.elim, ?_, ?_⟩,
    fun i => ⟨fun hi => ?_, fun hi => ?_⟩⟩
  · intro x y hx hf; subst hx
    obtain ⟨hy, ex, ey, hex, hey, h⟩ := hf
    have : y = 0 := by omega
    subst this
    simp [stOv] at hex hey; subst hex; subst hey
    simp [MetaOp.locks, MetaOp.crossRename, Node.dirIno] at h
  · simp [keptOps, stOv, List.range_succ]; rfl
  · have hf : ∃ f, stOv.fs.files !! i = some f ∧ f = newFile ∧
        stOv'.fs.files !! i = some (OsFile.ofBytes []) := by
      rcases (named_ov i).1 hi with rfl | rfl <;> exact ⟨newFile, by simp [stOv, stOv']⟩
    obtain ⟨f, hfi, rfl, hfi'⟩ := hf
    refine ⟨newFile, OsFile.ofBytes [], hfi, ⟨0, secOf [], ⟨.inl ?_, .inl ?_⟩,
      fun n => .inl ?_, rfl⟩, hfi'⟩ <;>
      simp [newFile, OsFile.ofBytes, OsFile.ofDisk]
  · have h6 : i ≠ 6 := fun h => hi ((named_ov i).2 (.inl h))
    have h7 : i ≠ 7 := fun h => hi ((named_ov i).2 (.inr h))
    simp [stOv', Ne.symm h6, Ne.symm h7]

/-! ## A directory's `fsync` makes a directory made in the same run durable -/

/-- `m` made in the root (inode 2); a directory fd 3 on the root. -/
def stMk : OsState :=
  { fs := { roots := [(rootP, 1)], treeDur := {[1 := ∅]}, metaLog := [⟨.mkdir 1 go!"m" 2, 0⟩],
            committed := fun _ => False, files := ∅, nextIno := 3 },
    proc := { ProcState.empty with dfds := {[W64 3 := ⟨1, .idle⟩]} } }

/-- **After the root's `fsync` succeeds, every crash keeps `m`.** -/
theorem dirsync_new_dir [GooseExts] [GoGlobalContext] [go.BasicIntoValInj] (st' st'' : OsState) (e' : Expr)
    (hs : IsFsStep "DirSync" (#(W64 3)) stMk e' st') (he : e' = Val (#(0 : w64)))
    (hc : MachineCrash st' st'') : st''.fs.treeDur.entry 1 go!"m" = some (.dir 2) := by
  obtain ⟨fd, df, hv, hdf, hr⟩ := hs
  have hfd : fd = W64 3 := by
    have := go.intoVal_inj hv; exact this.symm
  subst hfd
  simp [stMk] at hdf; subst hdf
  rcases hr with ⟨rfl, -⟩ | ⟨e, he0, rfl, -⟩
  · have hl : lastTouch stMk.fs.metaLog 1 = some 0 := by
      simp [lastTouch, stMk, MetaOp.dirs]
    rw [hl] at hc
    obtain ⟨-, -, -, -, -, ⟨S, hlt, hS, -, htr⟩, -⟩ := hc
    have h0 : S 0 := hS 0 (.inr .self)
    have hk : keptOps stMk.fs.metaLog S = [.mkdir 1 go!"m" 2] := by
      simp [keptOps, stMk, h0]
    simp only [OsState.commitThrough] at htr
    rw [htr, hk]
    simp [replay, MetaOp.apply, Tree.upd, Tree.entry, stMk]
  · exact absurd (go.intoVal_inj (by simpa using he)) he0

/-! ## `rmdir` of a directory with an open fd -/

/-- `m`, an empty directory (inode 2) in the root, with a directory fd 3 on it, and a metadata call
(token 0) begun. -/
def stRm : OsState :=
  { fs := { roots := [(rootP, 1)], treeDur := <[1 := {[go!"m" := .dir 2]}]> {[2 := ∅]},
            metaLog := [], committed := fun _ => False, files := ∅, nextIno := 3 },
    proc := { ProcState.empty with dfds := {[W64 3 := ⟨2, .idle⟩]}, calls := {[0 := 0]} } }

/-- **`rmdir` succeeds although an fd is open on the directory** (the fd keeps it, empty). -/
theorem rmdir_open_fd [GooseExts] [GoGlobalContext] :
    ∃ st' e', IsFsStep "Rmdir" (PairV (osTokV 0) (#(go!"/r/m"))) stRm e' st' := by
  have hp : (go!"/r/m" : GoString) = joinPath rootP [go!"m"] := rfl
  have hr : (go!"/r" : GoString) = joinPath rootP [] := rfl
  have hl : stRm.lookup (go!"/r/m") = some (.dir 2) := by
    rw [hp, lookup_one (r := rootP) (j := 1) rfl (by decide)]
    simp [walk, stRm, OsState.tree, replay, Tree.entry]
  have hl0 : stRm.lookup (go!"/r") = some (.dir 1) := by
    rw [hr, lookup_one (r := rootP) (j := 1) rfl (by decide)]; rfl
  have hpar : stRm.parent (go!"/r/m") = some (1, go!"m") := by
    unfold OsState.parent
    rw [show parentOf (go!"/r/m") = some (go!"/r") by decide]
    dsimp only
    rw [hl0]
    rfl
  refine ⟨_, _, go!"/r/m", 0, 0, rfl, ⟨(rootP, 1), by simp [stRm], [go!"m"], by simp, by decide, hp⟩,
    by simp [stRm], .inl ⟨2, 1, go!"m", ⟨hl, fun b => ?_⟩, hpar, .inl ⟨rfl, rfl⟩⟩⟩
  simp [stRm, OsState.tree, replay, Tree.entry]

end Tests
end Fs
end Perennial

end
