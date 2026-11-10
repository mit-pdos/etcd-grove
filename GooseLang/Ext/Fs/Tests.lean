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
* `crash_append_old_block`: an append into the block holding the old end, then a crash: the new
  size may come back with the block's old bytes (ext4 does not order it; `fs-config/crash.sh
  append-end`).
* `crash_new_block_zeros`: a new file's first write, then a crash: the new size may come back with
  zeros where the write was (ext4 commits the unwritten extent first; `crash.sh empty-write`).
* `crash_past_end_zeros` (a guarantee): a file grown past its durable size's last page, then a
  crash: the grown pages read zeros, whatever the disk held past the old end (durable zeros;
  `crash.sh shrink-grow`, `keep-size`).
* `crash_current`: under `VersOk`, which every file effect keeps (`versOk_*`), a crash may keep a
  file as it is: the crash rule never leaves a file without a crash image.
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

/-- The disk's sector of a file holding `c` (or more): `c`'s, zero past its end. -/
theorem diskSec_secOf_le {c : List w8} {sz : Nat} (h : c.length ≤ sz) (n : Nat) :
    diskSec (secOf c) sz n = secOf c n := by
  unfold diskSec; split
  · rfl
  · rename_i hp
    simp only [pageIn, decide_eq_true_eq, Nat.not_lt] at hp
    unfold secOf zeroSec; congr 1; funext j
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl

/-- A resized file's sector past its old size is zeros (an extension reads zeros). -/
theorem secOf_resized_past (f : OsFile) (sz n : Nat) (h : f.size ≤ 512 * n) :
    secOf (f.resized sz) n = zeroSec := by
  unfold secOf zeroSec; congr 1; funext j
  rw [List.getD_eq_getElem?_getD]
  simp only [OsFile.resized, List.getElem?_map]
  by_cases hb : 512 * n + j.1 < sz
  · rw [List.getElem?_range hb]; simp; omega
  · rw [List.getElem?_eq_none (by simp; omega)]; rfl

theorem fXY_vers : (fXY.secs 0).vers = [secOf [] 0, secOf [bx] 0, secOf [byt] 0] := by
  simp [fXY, OsFile.change, OsFile.ofBytes, OsFile.ofDisk, diskSec_secOf_le, secHits]

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
    refine ⟨1, secOf [byt], ⟨.inl ?_, .inl ?_⟩, fun n => .inl ?_, ?_⟩
    · simp [fXY, OsFile.change, OsFile.ofBytes, OsFile.ofDisk, diskSec_secOf_le]
    · simp [fXY, OsFile.change, OsFile.ofBytes, OsFile.ofDisk, diskSec_secOf_le]
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [fXY_vers]; simp
      · rw [secOf_far _ (by simp) n hn]
        have h0 : 512 * n ≠ 0 := by omega
        simp [fXY, OsFile.change, OsFile.ofBytes, OsFile.ofDisk, diskSec_secOf_le, secHits, h0]
    · simp [fXY, OsFile.change, OsFile.ofBytes, OsFile.ofDisk, diskSec_secOf_le]
  · have : i ≠ 0 := fun h => hi ((named_new i).2 h)
    simp [stNew, Ne.symm this]

/-! ## A failed sync's sector, after a later successful sync -/

/-- A one-byte file holding `X` on disk, written `Y`, then a failed sync, then a successful one. -/
def f1 : OsFile := (OsFile.ofBytes [bx]).change [byt] 0 1
def fLost : OsFile := (f1.syncFailed (fun _ => False)).synced (fun _ => False)

theorem fLost_vers : (fLost.secs 0).vers = [secOf [bx] 0, secOf [byt] 0] := by
  simp [fLost, f1, OsFile.synced, OsFile.syncFailed, OsFile.change, OsFile.ofBytes, OsFile.ofDisk, diskSec_secOf_le,
    secHits, pageIn]

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
      OsFile.ofBytes, OsFile.ofDisk, diskSec_secOf_le]) (by simp [fLost, f1, OsFile.synced, OsFile.syncFailed, OsFile.change,
      OsFile.ofBytes, OsFile.ofDisk, diskSec_secOf_le]) (by rw [fLost_vers]; simp) (fun n hn => by
      simp [fLost, f1, OsFile.synced, OsFile.syncFailed, OsFile.change, OsFile.ofBytes, OsFile.ofDisk, diskSec_secOf_le,
        OsFile.ofDisk, secHits, Sector.last]
      have h0 : 512 * n ≠ 0 := by omega
      rw [secOf_far _ (by simp) n hn]
      by_cases hp : 4096 * (n / 8) < 1
      · simp [hp, pageIn, h0]
      · simp [hp, pageIn, h0]; unfold secOf zeroSec; congr 1)

/-! ## Unsynced bytes may be lost -/

/-- **A machine crash may lose a write that was never synced**: `Y` written over `X`, no sync;
the crash may leave `X`. (A process's restart is a machine crash, by the environment's assumption
on restarts.) -/
theorem crash_loses_unsynced : OsCrash (oneFile f1) (oneFile (OsFile.ofBytes [bx])) := by
  refine crash_one f1 bx ?_ ?_ ?_ ?_
  · simp [f1, OsFile.change, OsFile.ofBytes, OsFile.ofDisk, diskSec_secOf_le]
  · simp [f1, OsFile.change, OsFile.ofBytes, OsFile.ofDisk, diskSec_secOf_le]
  · simp [f1, OsFile.change, OsFile.ofBytes, OsFile.ofDisk, diskSec_secOf_le, secHits]
  · intro n hn
    have h0 : 512 * n ≠ 0 := by omega
    simp [f1, OsFile.change, OsFile.ofBytes, OsFile.ofDisk, diskSec_secOf_le, secHits, h0]
    exact (secOf_far _ (by simp) n hn).symm

/-! ## Durable zeros -/

/-- A machine crash of `oneFile f` leaving the file of size `sz` whose sectors are `vs`: versions of
`f`'s sectors. -/
theorem crash_oneD (f : OsFile) (vs : Nat → SecBytes) (sz : Nat) (hlo : f.sizeLo ≤ sz)
    (hhi : sz ≤ f.sizeHi) (hv : ∀ n, vs n ∈ (f.secs n).vers) :
    OsCrash (oneFile f) (oneFile (OsFile.ofDisk vs sz)) := by
  refine ⟨rfl, rfl, rfl, fun _ h => h, rfl,
    ⟨fun _ => False, fun _ h => h.elim, fun _ h => h, fun _ _ h => h.elim, rfl⟩,
    fun i => ⟨fun hi => ?_, fun hi => ?_⟩⟩
  · obtain rfl := (named_one _ i).1 hi
    exact ⟨f, _, by simp [oneFile], ⟨sz, vs, ⟨.inl hlo, .inl hhi⟩, fun n => .inl (hv n), rfl⟩,
      by simp [oneFile]⟩
  · have : i ≠ 0 := fun h => hi ((named_one _ i).2 h)
    simp [oneFile, Ne.symm this]

/-- A one-byte file holding `X` on disk, `Y` appended (in the block that holds the old end). -/
def fApp : OsFile := (OsFile.ofBytes [bx]).change [bx, byt] 1 2

/-- **An append into the block holding the old end is not ordered**: a crash may keep the new size
with the sector as it was (ext4 commits the size without the data, `crash.sh append-end`): the
file reads `X 0`. -/
theorem crash_append_old_block :
    OsCrash (oneFile fApp) (oneFile (OsFile.ofDisk (secOf [bx]) 2)) := by
  refine crash_oneD fApp (secOf [bx]) 2 (by simp [fApp, OsFile.change, OsFile.ofBytes,
    OsFile.ofDisk]) (by simp [fApp, OsFile.change, OsFile.ofBytes, OsFile.ofDisk, diskSec_secOf_le]) (fun n => ?_)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [fApp, OsFile.change, OsFile.ofBytes, OsFile.ofDisk, diskSec_secOf_le, secHits]
  · have h0 : ¬ 512 * n < 2 := by omega
    simp [fApp, OsFile.change, OsFile.ofBytes, OsFile.ofDisk, diskSec_secOf_le, secHits, h0]

/-- A new file, `Y` written into it, never synced. -/
def fNew : OsFile := (OsFile.ofBytes []).change [byt] 0 1

/-- **A new block may come back as zeros under the size that covers it** (ext4 with
`dioread_nolock` commits the size and the unwritten extent before the data, `crash.sh
empty-write`): the file reads `0`. -/
theorem crash_new_block_zeros :
    OsCrash (oneFile fNew) (oneFile (OsFile.ofDisk (fun _ => zeroSec) 1)) := by
  refine crash_oneD fNew _ 1 (by simp [fNew, OsFile.change, OsFile.ofBytes, OsFile.ofDisk, diskSec_secOf_le])
    (by simp [fNew, OsFile.change, OsFile.ofBytes, OsFile.ofDisk, diskSec_secOf_le]) (fun n => ?_)
  have hz : secOf [] n = zeroSec := by
    unfold secOf zeroSec; congr 1
  simp only [fNew, OsFile.change, OsFile.ofBytes, OsFile.ofDisk,
    diskSec_secOf_le (c := []) (sz := 0) (Nat.le_refl _), hz, List.length_nil]
  split <;> simp

/-- A file of size 1 as a crash may find it on disk, holding the stale bytes `vs` past its end
(any), grown to 8192 bytes. -/
def fGrow (vs : Nat → SecBytes) : OsFile := (OsFile.ofDisk vs 1).truncate 8192

/-- **Durable zeros** (a guarantee): after the file is grown past its durable size's last page, a
crash that keeps the new size leaves the grown pages zeros, whatever the disk held past the old end
(`crash.sh shrink-grow`, `keep-size`): byte 4096 reads 0. -/
theorem crash_past_end_zeros (vs : Nat → SecBytes) (f' : OsFile)
    (h : CrashFile (oneFile (fGrow vs)) 0 (fGrow vs) f') (hs : f'.size = 8192) :
    f'.contents[4096]? = some 0 := by
  obtain ⟨sz, ws, -, hv, rfl⟩ := h
  have hsz : sz = 8192 := by simpa [OsFile.ofDisk] using hs
  subst hsz
  have h8 : ws 8 = zeroSec := by
    rcases hv 8 with h | ⟨ks, f'', hp, hl, hw⟩
    · have hd : diskSec vs 1 8 = zeroSec := by simp [diskSec, pageIn]
      simp only [fGrow, OsFile.truncate, OsFile.change, secHits] at h
      simpa [OsFile.ofDisk, hd, secOf_resized_past] using h
    · have hk : ks = [] := List.perm_nil.mp (by simpa [changesOn, oneFile, ProcState.empty] using hp)
      subst hk; cases hl; rw [hw]
      simp [fGrow, OsFile.truncate, OsFile.change, secHits, Sector.last, secOf_resized_past,
        OsFile.ofDisk]
  simp [OsFile.contents, OsFile.rawAt, OsFile.ofDisk, Sector.last, diskSec, pageIn, h8, zeroSec]

/-! ## A crash may always keep a file as it is -/

/-- Every sector has a version: the invariant of every file the semantics makes (`versOk_*`),
under which the crash rule allows the file as it is (`crash_current`). -/
def VersOk (f : OsFile) : Prop := ∀ n, (f.secs n).vers ≠ []

theorem last_mem {s : Sector} (h : s.vers ≠ []) : s.last ∈ s.vers := by
  unfold Sector.last; rw [List.getLast?_eq_getLast h]; exact List.getLast_mem h

theorem crash_current (st : OsState) (i : Ino) (f : OsFile) (hok : VersOk f)
    (hlo : f.sizeLo ≤ f.size) (hhi : f.size ≤ f.sizeHi) :
    CrashFile st i f (OsFile.ofDisk (fun n => (f.secs n).last) f.size) :=
  ⟨f.size, _, ⟨.inl hlo, .inl hhi⟩, fun n => .inl (last_mem (hok n)), rfl⟩

theorem versOk_ofDisk (vs : Nat → SecBytes) (sz : Nat) : VersOk (OsFile.ofDisk vs sz) := by
  intro n; simp [OsFile.ofDisk]

theorem versOk_change {f : OsFile} (hok : VersOk f) (c : List w8) (lo hi : Nat) :
    VersOk (f.change c lo hi) := by
  intro n; dsimp only [OsFile.change]; split
  · simp
  · exact hok n

theorem versOk_synced {f : OsFile} (hok : VersOk f) (busy : Nat → Prop) [DecidablePred busy] :
    VersOk (f.synced busy) := by
  intro n; dsimp only [OsFile.synced]
  split
  · exact hok n
  · split
    · split
      · simp
      · exact hok n
    · simp

theorem versOk_syncFailed {f : OsFile} (hok : VersOk f) (busy : Nat → Prop)
    [DecidablePred busy] : VersOk (f.syncFailed busy) := by
  intro n; dsimp only [OsFile.syncFailed]; split <;> exact hok n

theorem versOk_landWrite {f : OsFile} (hok : VersOk f) (off : Nat) (data : List w8) (k : Nat) :
    VersOk (f.landWrite off data k) := by
  unfold OsFile.landWrite; split
  · exact hok
  · exact versOk_change hok _ _ _

theorem versOk_truncate {f : OsFile} (hok : VersOk f) (sz : Nat) : VersOk (f.truncate sz) :=
  versOk_change hok _ _ _

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
the rename of `/r/a` that took effect before it (the create's call began before the rename took
effect, so the journal may have either first). -/
theorem crash_overlap : OsCrash stOv stOv' := by
  refine ⟨rfl, rfl, rfl, fun _ h => h, rfl,
    ⟨fun x => x = 1, fun x hx => by simp [hx, stOv], fun _ h => h.elim, ?_, ?_⟩,
    fun i => ⟨fun hi => ?_, fun hi => ?_⟩⟩
  · intro x y hx hf; subst hx
    obtain ⟨hy, ex, hex, h⟩ := hf
    have : y = 0 := by omega
    subst this
    simp [stOv] at hex; subst hex
    simp at h
  · simp [keptOps, stOv, List.range_succ]; rfl
  · have hf : ∃ f, stOv.fs.files !! i = some f ∧ f = newFile ∧
        stOv'.fs.files !! i = some (OsFile.ofBytes []) := by
      rcases (named_ov i).1 hi with rfl | rfl <;> exact ⟨newFile, by simp [stOv, stOv']⟩
    obtain ⟨f, hfi, rfl, hfi'⟩ := hf
    refine ⟨newFile, OsFile.ofBytes [], hfi, ⟨0, secOf [], ⟨.inl ?_, .inl ?_⟩,
      fun n => .inl ?_, rfl⟩, hfi'⟩ <;>
      simp [newFile, OsFile.ofBytes, OsFile.ofDisk, diskSec_secOf_le]
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
  · obtain ⟨-, -, -, -, -, ⟨S, hlt, hS, -, htr⟩, -⟩ := hc
    have h0 : S 0 := hS 0 (.inr (by simp [stMk]))
    have hk : keptOps stMk.fs.metaLog S = [.mkdir 1 go!"m" 2] := by
      simp [keptOps, stMk, h0]
    simp only [OsState.commitAll] at htr
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
