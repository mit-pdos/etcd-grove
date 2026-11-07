/-
**An assumption on the executions, to be reviewed: a `pwrite` that lands only partly stops at a
page boundary.**

`NoTearStep` and `NoTearCrash` restrict the Linux file extension's executions (`fsSemWithS`,
`FilteredSem.lean`): a theorem proved over `fsSemWithS NoTearStep NoTearCrash` holds of the runs
that satisfy them, and states so. They are not part of the semantics (`Impl.lean`), which lets a
`pwrite` land any prefix, return a short count, and a crash keep any prefix of a write in flight.

A *page cut* of a write of `len` bytes at `off` (`PageCut off len k`) is a prefix of `k` bytes
that is none of it, all of it, or ends on a 4096-byte page boundary (`(off + k) % 4096 = 0`).

- `NoTearStep`: the second step of a write (`PWriteFinish`) lands and returns a page cut of it,
  with whatever errno.
- `NoTearCrash`: at a crash, for each write in flight there is a page cut `k` of it such that each
  sector the write touches is, in the crash's image of its file, one of the versions the sector had
  (since its last successful sync, the page cache's included) or the sector with the first `k`
  bytes of the write landed: never a prefix of the write that ends inside a page.

A write within one page (`inPage`) has no page cut but none and all (`pageCut_inPage`): it lands
whole or not at all, at a step and at a crash.

Why Linux behaves so (ext4/xfs, buffered I/O, a regular file):

- `generic_perform_write` copies the user buffer into the page cache a page at a time (the part of
  the write in that page), each copy under that page's lock (`write_begin`/`write_end`); the
  file's size moves at each `write_end`.
- Writeback locks the page and so cannot start in the middle of a page's copy (the no-mixed-writeback
  assumption: the device writes the page's sectors as they are when writeback took the page, each
  sector atomically); a crash finds each sector as one writeback (or none) left it, and the pages
  the copy has reached are the first ones of the write.
- A fatal signal is checked between pages (`fatal_signal_pending` in `generic_perform_write`), never
  inside one page's copy: a signal cuts a write short at a page boundary.
- `ENOSPC`/`EDQUOT` come from the allocation in `write_begin`, before a page's copy: they too cut a
  write short at a page boundary (or fail it with nothing written).
- `EFAULT` (a fault on the user buffer) can stop a copy in the middle of a page
  (`copy_folio_from_iter_atomic` short, the copy retried with a smaller length and, on a second
  fault, given up there); the buffer is Go memory, mapped and resident while the call runs, so it
  does not happen.

A theorem over these premises is only as good as this reading of Linux, to be reviewed against the
kernel (in particular the short copy of `generic_perform_write` on a partial fault, and
filesystems with large folios, whose unit of copy and writeback is more than a page: their
boundaries are page boundaries too, so the premise is weaker than what they do, but this is to
be checked).

`noTearStep_keeps` gives `StepKeeps NoTearStep` (every state `FsStep` has a step from keeps one:
the whole write landing), so the program logic's specs hold over the restricted semantics
(`fsSemWithS_ok`). Untrusted (but the two premises are part of every theorem stated over them).
-/
module

public import GooseLang.Ext.Fs.FilteredSem
public import GooseLang.Ext.Fs.Write

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

/-- `k` bytes of a write of `len` bytes at `off`: none, all, or a prefix ending on a 4096-byte page
boundary. -/
def PageCut (off len k : Nat) : Prop := k ≤ len ∧ (k = 0 ∨ k = len ∨ (off + k) % 4096 = 0)

/-- The step premise: a `PWriteFinish` lands and returns a page cut of its write. -/
def NoTearStep : StepPrem := fun op v st e' _st' =>
  op = "PWriteFinish" → ∀ (t : Nat) (i : Ino) (off : Nat) (data : List w8), v = osTokV t →
    st.proc.inflight !! t = some ⟨i, .write off data⟩ →
    ∃ (k : Nat) (e : w64), PageCut off data.length k ∧ e' = osRes (#(W64 k)) e

/-- The crash premise: for each write in flight, a page cut `k` of it such that each sector the
write touches is, in the crash's image of its file, a version the sector had, or the sector with
the first `k` bytes of the write landed. -/
def NoTearCrash (st st' : OsState) : Prop :=
  ∀ (t : Nat) (i : Ino) (off : Nat) (data : List w8),
    st.proc.inflight !! t = some ⟨i, .write off data⟩ →
    ∀ f f', st.fs.files !! i = some f → st'.fs.files !! i = some f' →
    ∃ k, PageCut off data.length k ∧
      ∀ n, secHits (min off f.size) (off + data.length) n = true →
        (f'.secs n).last ∈ (f.secs n).vers ∨
        (f'.secs n).last = ((f.landWrite off data k).secs n).last

/-- The write of `len` bytes at `off` writes something and lies within one 4096-byte page. -/
def inPage (off len : Nat) : Prop := 0 < len ∧ off / 4096 = (off + len - 1) / 4096

/-- A write within one page has no page cut but none and all. -/
theorem pageCut_inPage {off len k : Nat} (hk : PageCut off len k) (hp : inPage off len) :
    k = 0 ∨ k = len := by
  obtain ⟨hkl, h0 | hl | hm⟩ := hk
  · exact .inl h0
  · exact .inr hl
  · obtain ⟨hpos, hpg⟩ := hp
    by_cases hk0 : k = 0
    · exact .inl hk0
    by_cases hkl' : k = len
    · exact .inr hkl'
    exfalso
    omega

/-- The restricted semantics. -/
@[reducible] def noTearSem : ExtSemantics fsExt := fsSemWithS NoTearStep NoTearCrash

section render
variable [GooseExts] [GoGlobalContext]
attribute [local instance] Classical.propDecidable

/-- `heapRendered_render` from the uniqueness of what a cell maps alone. -/
theorem heapRendered_render_u {st st' : OsState} {h : GMap Loc (NonAtomic val)}
    (hu : ∀ l i b i' b', MapsTo st l i b → MapsTo st l i' b' → i = i' ∧ b = b')
    (hm : st'.proc.maps = st.proc.maps) (Hh : ∀ l, Mapped st l → (h !! l).isSome) :
    HeapRendered st st' h (renderHeap st' h) := by
  have hM : ∀ l p i, MapsTo st' l p i ↔ MapsTo st l p i := by
    intro l p i; simp only [MapsTo, hm]
  have hMd : ∀ l, Mapped st' l ↔ Mapped st l := fun l =>
    ⟨fun ⟨p, i, h⟩ => ⟨p, i, (hM l p i).1 h⟩, fun ⟨p, i, h⟩ => ⟨p, i, (hM l p i).2 h⟩⟩
  have hlk : ∀ l, renderHeap st' h !! l = (if hm : Mapped st' l then
      (h !! l).map (fun x => (x.1, cellVal st' hm.choose hm.choose_spec.choose)) else h !! l) :=
    fun _ => rfl
  refine ⟨fun l p i hpi hmd => ?_, fun l p i hpi hn => absurd ((hMd l).1 ⟨p, i, hpi⟩) hn,
    fun l hn hmd => absurd ((hMd l).2 hmd) hn, fun l hn _ => ?_⟩
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (Hh l hmd)
    refine ⟨x.1, x.2, hx, ?_⟩
    have hm' : Mapped st' l := ⟨p, i, hpi⟩
    rw [hlk, dif_pos hm', hx]
    obtain ⟨rfl, rfl⟩ := hu _ _ _ _ _ ((hM _ _ _).1 hm'.choose_spec.choose_spec) ((hM _ _ _).1 hpi)
    rfl
  · rw [hlk, dif_neg hn]

end render

/-- An in-page write's length fits in a `w64`. -/
theorem inPage_len_lt {off len : Nat} (hp : inPage off len) : len < 2 ^ 64 := by
  obtain ⟨h0, h1⟩ := hp
  have : off + len - 1 < 4096 * (off / 4096) + 4096 := by
    have := Nat.lt_div_mul_add (a := off + len - 1) (b := 4096) (by decide)
    rw [← h1] at this; omega
  have := Nat.div_mul_le_self off 4096
  omega

/-- Every state with a step keeps one under `NoTearStep`: the whole write landing. -/
theorem noTearStep_keeps : StepKeeps NoTearStep := by
  intro _ _ o v h st e' h' st' hu hs
  by_cases ho : o = "PWriteFinish"
  case neg => exact ⟨e', h', st', hs, fun h => absurd h ho⟩
  subst ho
  obtain ⟨hstep, hfr, hr⟩ := hs
  obtain ⟨t, i, off, data, f, k, e, rfl, hin, hf, hk, hok, rfl, rfl⟩ := hstep
  have hsame : ∀ t' i' off' data', osTokV t = osTokV t' →
      st.proc.inflight !! t' = some ⟨i', .write off' data'⟩ → i' = i ∧ off' = off ∧ data' = data := by
    intro t' i' off' data' hv hin'
    have : t = t' := extVal_inj (val.ExtV.inj hv)
    subst this
    rw [hin] at hin'
    cases hin'
    exact ⟨rfl, rfl, rfl⟩
  · let st'' := (st.doneInflight t).setFile i (f.landWrite off data data.length)
    have hm : st''.proc.maps = st.proc.maps := rfl
    have hm' : ((st.doneInflight t).setFile i (f.landWrite off data k)).proc.maps =
        st.proc.maps := rfl
    have Hh : ∀ l, Mapped st l → (h !! l).isSome := by
      intro l ⟨p, b, hpb⟩
      obtain ⟨m, v0, hl, -⟩ := hr.1 l p b (by simpa only [MapsTo, hm'] using hpb) ⟨p, b, hpb⟩
      simp [hl]
    refine ⟨osRes (#(W64 data.length)) 0, renderHeap st'' h, st'',
      ⟨⟨t, i, off, data, f, data.length, 0, rfl, hin, hf, Nat.le_refl _, Or.inl ⟨Or.inl rfl, rfl⟩,
        rfl, rfl⟩, mapsFresh_same hm, heapRendered_render_u hu hm Hh⟩, ?_⟩
    intro _ t' i' off' data' hv hin'
    obtain ⟨rfl, rfl, rfl⟩ := hsame t' i' off' data' hv hin'
    exact ⟨_, 0, ⟨Nat.le_refl _, .inr (.inl rfl)⟩, rfl⟩

/-- The program logic's specs hold over the restricted semantics. -/
theorem noTearSem_ok : letI := noTearSem; FsSemOk :=
  fsSemWithS_ok NoTearStep NoTearCrash noTearStep_keeps

end Fs
end Perennial

end
