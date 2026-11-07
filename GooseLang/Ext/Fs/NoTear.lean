/-
**An assumption on the executions, to be reviewed: a `pwrite` within one page does not tear.**

`NoTearStep` and `NoTearCrash` restrict the Linux file extension's executions (`fsSemWithS`,
`FilteredSem.lean`): a theorem proved over `fsSemWithS NoTearStep NoTearCrash` holds of the runs
that satisfy them, and states so. They are not part of the semantics (`Impl.lean`), which lets a
`pwrite` land any prefix, return a short count, and a crash keep any prefix of a write in flight.

A write is *in one page* (`inPage`) when it writes at least one byte and its bytes `[off, off+len)`
lie within one 4096-byte page.

- `NoTearStep`: the second step of such a write (`PWriteFinish`) returns `len` or `0` written,
  with whatever errno: it lands all of it or none of it.
- `NoTearCrash`: at a crash, each sector such a write in flight touches is, in the crash's image of
  its file, one of the versions the sector had (since its last successful sync, the page cache's
  included) or the sector with the whole write landed: never a prefix of the write that ends inside
  the sector.

Why Linux behaves so (ext4/xfs, buffered I/O, on a regular file whose blocks are allocated):

- `generic_perform_write` copies the user buffer into the page cache a page at a time, each copy
  under that page's lock (`write_begin`/`write_end`); a write within one page is one such copy.
- Writeback locks the page and so cannot start in the middle of the copy (the no-mixed-writeback
  assumption: the device writes the page's sectors as they are when writeback took the page, each
  sector atomically); a crash finds each sector as one writeback (or none) left it.
- A fatal signal is checked between pages (`fatal_signal_pending` in `generic_perform_write`), never
  inside one page's copy, so a signal does not cut a one-page write short.
- A short count on a regular file comes only from `EFAULT` (the buffer is Go memory, mapped) or
  `ENOSPC`/`EDQUOT` (allocation): bbolt's meta pages are allocated when the file is created, so
  rewriting them allocates nothing.

The last point is about the client's file, not every file: a client that relies on `NoTearStep`
for a write that allocates assumes more than Linux promises. The assumption is stated for every
in-page write; a theorem over it is only as good as this reading of Linux, to be reviewed.

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

/-- The write of `len` bytes at `off` writes something and lies within one 4096-byte page. -/
def inPage (off len : Nat) : Prop := 0 < len ∧ off / 4096 = (off + len - 1) / 4096

/-- The step premise: a `PWriteFinish` of an in-page write returns all of it or nothing written. -/
def NoTearStep : StepPrem := fun op v st e' _st' =>
  op = "PWriteFinish" → ∀ (t : Nat) (i : Ino) (off : Nat) (data : List w8), v = osTokV t →
    st.proc.inflight !! t = some ⟨i, .write off data⟩ → inPage off data.length →
    ∃ e : w64, e' = osRes (#(W64 data.length)) e ∨ e' = osRes (#(W64 0)) e

/-- The crash premise: each sector an in-page write in flight touches is, in the crash's image of
its file, a version the sector had, or the sector with the whole write landed. -/
def NoTearCrash (st st' : OsState) : Prop :=
  ∀ (t : Nat) (i : Ino) (off : Nat) (data : List w8),
    st.proc.inflight !! t = some ⟨i, .write off data⟩ → inPage off data.length →
    ∀ f f', st.fs.files !! i = some f → st'.fs.files !! i = some f' →
    ∀ n, secHits (min off f.size) (off + data.length) n = true →
      (f'.secs n).last ∈ (f.secs n).vers ∨
      (f'.secs n).last = ((f.landWrite off data data.length).secs n).last

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

/-- Every state with a step keeps one under `NoTearStep`: the whole in-page write landing. -/
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
  by_cases hp : inPage off data.length
  case neg =>
    refine ⟨_, h', _, ⟨⟨t, i, off, data, f, k, e, rfl, hin, hf, hk, hok, rfl, rfl⟩, hfr, hr⟩, ?_⟩
    intro _ t' i' off' data' hv hin' hp'
    obtain ⟨rfl, rfl, rfl⟩ := hsame t' i' off' data' hv hin'
    exact absurd hp' hp
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
    intro _ t' i' off' data' hv hin' _
    obtain ⟨rfl, rfl, rfl⟩ := hsame t' i' off' data' hv hin'
    exact ⟨0, Or.inl rfl⟩

/-- The program logic's specs hold over the restricted semantics. -/
theorem noTearSem_ok : letI := noTearSem; FsSemOk :=
  fsSemWithS_ok NoTearStep NoTearCrash noTearStep_keeps

end Fs
end Perennial

end
