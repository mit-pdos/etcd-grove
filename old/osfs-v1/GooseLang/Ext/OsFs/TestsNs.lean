/-
Tests of the namespace's trusted definitions (`GooseLang/Ext/OsFs/Names.lean`, the namespace's
steps and crash in `Impl.lean`; `notes/walfs-ext-plan.md`): lemmas saying that they do what the
plan says, one per rule a mistake would most likely break.

* Paths: `parentOf`, `baseOf`, `IsUnder` on concrete paths; a root is no `NsName` (so no step
  renames, removes or creates it).
* Commits: an fsync of a directory commits the operations up to the last one that changed it,
  earlier ones in other directories included (N1), and nothing for a directory no operation
  changed.
* Crash: with nothing logged, a crash leaves the durable namespace; a crash never loses a file the
  namespace it leaves names.
* Reads: `Readdirnames` cannot end before returning every name that was there throughout.
* Creation: `NsOpen` with `O_CREAT` of a new name makes a file under a fresh key and logs it.
-/
module

public import GooseLang.Ext.OsFs.Impl
public import Perennial.Golang.Defn

@[expose] public section

namespace Perennial
namespace OsFsNsTests

variable [GooseExts] [GoGlobalContext] [go.BasicIntoValInj]

/-! ## Paths -/

example : parentOf go!"/r/seg" = some go!"/r" := by decide
example : baseOf go!"/r/seg" = go!"seg" := by decide
example : parentOf go!"/r/w/seg" = some go!"/r/w" := by decide
example : parentOf go!"seg" = none := by decide
example : parentOf go!"/r" = some [] := by decide
example : IsUnder go!"/r" go!"/r/x" := by decide
example : IsUnder go!"/r" go!"/r" := by decide
example : ¬ IsUnder go!"/r" go!"/rx" := by decide
example : NameOk go!"seg.tmp" := by decide
example : ¬ NameOk go!".." := by decide
example : ¬ NameOk go!"a/b" := by decide
example : joinPath go!"/r" [go!"w", go!"seg"] = go!"/r/w/seg" := by decide
example : CanonBelow go!"/r" go!"/r/w/seg" :=
  ⟨[go!"w", go!"seg"], by simp, by decide, by decide⟩

/-- A root is not strictly below itself: no `NsName` step (rename, unlink, rmdir, mkdir) takes a
root. -/
theorem not_canonBelow_self (r : GoString) : ¬ CanonBelow r r := by
  rintro ⟨cs, hne, -, h⟩
  have hl := congrArg List.length h
  simp only [joinPath, List.length_append] at hl
  cases cs with
  | nil => exact hne rfl
  | cons c cs => simp at hl <;> omega

/-! ## Commits -/

/-- An fsync of `/r` after creating `/r/seg` commits the create. -/
example : commitLen go!"/r" [.create go!"/r/seg" [0]] = 1 := by decide

/-- An fsync of `/r` commits a create in `/r/w.tmp` made before a rename in `/r` (the WAL's
`Create`: the parent's fsync after the rename makes the segment's entry durable, N1). -/
example : commitLen go!"/r" [.create go!"/r/w.tmp/seg" [0], .rename go!"/r/w.tmp" go!"/r/w"] = 2 := by
  decide

/-- ... and an fsync of a directory no operation changed commits nothing. -/
example : commitLen go!"/r/w" [.create go!"/r/w.tmp/seg" [0], .rename go!"/r/w.tmp" go!"/r/w"] = 0 := by
  decide

/-- The review's case (2026-11-05): a create in `/r/a/b`, then `/r/a` moved away and `/r/z` moved
to `/r/a`: an fsync of the directory now at `/r/a/b` is not known to commit the create, which was
of another directory. -/
example : dirCommitLen go!"/r/a/b" [.create go!"/r/a/b/f" [0], .rename go!"/r/a" go!"/r/q",
    .rename go!"/r/z" go!"/r/a"] = 0 := by decide

/-- ... while the WAL's `Create` (no path above `/r` moved) is: the fsync of `/r` commits both. -/
example : dirCommitLen go!"/r" [.create go!"/r/w.tmp/seg" [0], .rename go!"/r/w.tmp" go!"/r/w"] = 2 := by
  decide

/-- An fsync of `/r` does not commit a later operation in another directory. -/
example : commitLen go!"/r" [.create go!"/r/a" [0], .create go!"/r/w/b" [1]] = 1 := by decide

/-- `commitLen` never exceeds the log. -/
theorem commitLen_le (d : GoString) (ops : List NsOp) : commitLen d ops ≤ ops.length := by
  induction ops with
  | nil => simp [commitLen]
  | cons o os ih =>
    simp only [commitLen, List.length_cons]
    split
    · omega
    · split <;> omega

/-! ## Crash -/

/-- With nothing logged, a crash leaves the durable namespace. -/
theorem crash_empty_log {st st' : OsState} (hl : st.nsLog = []) (h : NsCrash st st') :
    st'.ns = st.nsDur := by
  obtain ⟨-, -, -, -, -, ⟨n, -, hn⟩, -⟩ := h
  rw [hn, hl]; simp [nsReplay]

/-- A successful fsync of a directory leaves nothing of what it committed to a crash: a crash
after it keeps at least the operations up to the last one that changed the directory. -/
theorem crash_after_dirSync {st st' : OsState} {fd : w64} {df : OsDirFd} {e' : Expr}
    (hd : st.dfds !! fd = some df)
    (h : IsOsStep "DirSync" (#fd) st e' st') (he : e' = Val (#(0 : w64))) :
    st'.nsDur = nsReplay (st.nsLog.take (dirCommitLen df.path st.nsLog)) st.nsDur := by
  simp only [IsOsStep] at h
  obtain ⟨fd', df', n, hv, hd', -, rfl, hres⟩ := h
  cases go.intoVal_inj hv
  rw [hd] at hd'; cases hd'
  rcases hres with ⟨rfl, -⟩ | ⟨e, he0, he'⟩
  · rfl
  · rw [he] at he'; injection he' with h1
    exact absurd (go.intoVal_inj h1).symm he0

/-- A crash never loses a file the namespace it leaves names. -/
theorem crash_keeps_named {st st' : OsState} (h : OsCrash st st') {p k : GoString}
    (hp : st'.ns !! p = some (.file k)) : ∃ f, st'.files !! k = some (some f) :=
  h.2.2.2.2.2.2.2 p k hp

/-! ## Reads -/

/-- `Readdirnames` cannot end while a name that was in the directory when the read began, is
still there and was not touched since, has not been returned. -/
theorem readdir_no_early_end {st st' : OsState} {fd : w64} {df : OsDirFd}
    {u s r : GoString → Bool} {b : GoString} (hd : st.dfds !! fd = some df)
    (hcur : df.rd.cur st df.path = some (u, s, r)) (hu : u b = true)
    (hp : nsPresent st df.path b = true) (hr : r b = false) (e : w64) :
    ¬ IsOsStep "DirReadNext" (#fd) st
      (Val (PairV (#([] : GoString)) (PairV (#(1 : w64)) (#e)))) st' ∨ e ≠ 0 := by
  by_cases he : e = 0
  · left
    subst he
    simp only [IsOsStep]
    rintro ⟨fd', df', u', s', r', hv, hd', hcur', hres⟩
    cases go.intoVal_inj hv
    rw [hd] at hd'; cases hd'
    rw [hcur] at hcur'; cases hcur'
    rcases hres with ⟨b', -, -, -, he'⟩ | ⟨hall, -, -⟩ | ⟨e', -, -, he'⟩
    · injection he' with h1
      injection h1 with _ h2
      injection h2 with h3
      exact absurd (go.intoVal_inj h3) (by decide)
    · have := hall b hu hp; rw [hr] at this; cases this
    · injection he' with h1
      injection h1 with _ h2
      injection h2 with h3
      exact absurd (go.intoVal_inj h3) (by decide)
  · right; exact he

/-! ## Creation -/

/-- `NsOpen` of a new name with `O_CREAT` in an existing directory makes an empty file under a
fresh key (a key no path can be), names it, and logs the creation. -/
theorem nsOpen_creates {st st1 : OsState} {p : GoString} {acc : Nat} {trunc : Bool}
    {tgt : Option GoString} (hn : st.ns !! p = none)
    (h : NsOpenEffect st p acc true trunc st1 tgt) :
    ∃ k, tgt = some k ∧ IsInoKey k ∧ k ∉ st.files ∧ st1.ns = <[p := .file k]> st.ns ∧
      st1.nsLog = st.nsLog ++ [.create p k] ∧ st1.file k = some nsNewFile := by
  unfold NsOpenEffect at h
  rw [hn] at h
  obtain ⟨-, -, -, k, hk, hkf, rfl, rfl⟩ := h
  refine ⟨k, rfl, hk, hkf, rfl, rfl, ?_⟩
  show ((<[k := some nsNewFile]> st.files) !! k).bind id = some nsNewFile
  rw [GMap.lookup_insert]; rfl

end OsFsNsTests
end Perennial
