/-
Tests of the Linux file extension's trusted definitions (`GooseLang/Ext/OsFs/Impl.lean`): lemmas
saying that the step and crash relations do what `notes/osfs-ext-plan.md` says, one per rule a
mistake in the definitions would most likely break. They replace program-level probes: each
asks a question of the trusted file itself.

* Misuse is stuck: a closed fd, a disallowed path, an unsupported flag, a writable or offset
  mapping, a munmap of part of a mapping.
* A mapped cell shows the file, and a hole past EOF and under an in-flight change.
* A read with no change in flight sees exactly the file; a racing read may see any byte the
  change may write.
* After a successful sync (nothing in flight), a crash, which loses the page cache, leaves the
  file with exactly the contents the page cache had at the sync; a crash
  after an unsynced write may keep the old byte or the new one; a byte lost by a failed sync
  stays lost across a later successful sync, until it is written again.
-/
module

public import GooseLang.Ext.OsFs.Impl
public import Perennial.Golang.Defn

@[expose] public section

namespace Perennial
namespace OsFsTests

variable [GooseExts] [GoGlobalContext] [go.BasicIntoValInj]

/-! ## Misuse is stuck -/

/-- A `pread` on an fd that is not open (closed, or never opened) has no step. -/
theorem pread_closed (st st' : OsState) (e' : Expr) (fd off n : w64) (h : st.fds !! fd = none) :
    ¬ IsOsStep "PRead" (PairV (#fd) (PairV (#off) (#n))) st e' st' := by
  simp only [IsOsStep]
  rintro ⟨fd', _, _, d, _, hv, hfd, -⟩
  injection hv with h1
  cases go.intoVal_inj h1
  simp [FdOpen, h] at hfd

/-- A `pwrite` on an fd opened read-only has no step. -/
theorem pwrite_readonly (st st' : OsState) (e' : Expr) (fd off : w64) (data : List w8)
    (d : OsFd) (hd : st.fds !! fd = some d) (hro : d.writable = false) :
    ¬ IsOsStep "PWriteStart" (PairV (#fd) (PairV (#off) (#data))) st e' st' := by
  simp only [IsOsStep]
  rintro ⟨fd', _, _, d', _, hv, hfd, hw, -⟩
  injection hv with h1
  cases go.intoVal_inj h1
  simp [FdOpen, hd] at hfd
  subst hfd
  simp [hro] at hw

/-- Opening a path outside the allowed set has no step. -/
theorem open_outside (st st' : OsState) (e' : Expr) (p : GoString) (fl : w64)
    (h : p ∉ st.files) : ¬ IsOsStep "Open" (PairV (#p) (#fl)) st e' st' := by
  simp only [IsOsStep]
  rintro ⟨p', _, hv, hp, -⟩
  injection hv with h1
  cases go.intoVal_inj h1
  exact h hp

/-- `O_APPEND` (`0x400`) is not an allowed flag; bbolt's three flag sets are. -/
example : ¬ OpenFlagsOk (O_RDWR + 0x400) := by unfold OpenFlagsOk O_RDWR O_CREAT O_TRUNC O_CLOEXEC; decide
example : OpenFlagsOk (O_RDWR + O_CREAT + O_CLOEXEC) := by
  unfold OpenFlagsOk O_RDWR O_CREAT O_TRUNC O_CLOEXEC; decide
example : OpenFlagsOk (O_RDONLY + O_CLOEXEC) := by
  unfold OpenFlagsOk O_RDONLY O_CREAT O_TRUNC O_CLOEXEC; decide
example : OpenFlagsOk (O_RDWR + O_CREAT + O_TRUNC + O_CLOEXEC) := by
  unfold OpenFlagsOk O_RDWR O_CREAT O_TRUNC O_CLOEXEC; decide

/-- A mapping that is not `PROT_READ` (here `PROT_READ|PROT_WRITE`) has no step. -/
theorem mmap_writable (st st' : OsState) (e' : Expr) (fd off len fl : w64) :
    ¬ IsOsStep "Mmap" (PairV (#fd) (PairV (#off) (PairV (#len) (PairV (#(3 : w64)) (#fl))))) st e' st' := by
  simp only [IsOsStep]
  rintro ⟨_, _, _, prot, _, _, hv, -, -, -, -, hprot, -⟩
  injection hv with _ h2
  injection h2 with _ h3
  injection h3 with _ h4
  injection h4 with h5
  cases go.intoVal_inj h5
  simp [PROT_READ] at hprot

/-- A `munmap` whose length is not the whole mapping's has no step. -/
theorem munmap_partial (st st' : OsState) (e' : Expr) (base : Loc) (len cap : w64) (m : OsMap)
    (hm : st.maps !! base = some m) (hlen : len.toNat ≠ m.len) :
    ¬ IsOsStep "Munmap" (PairV (#base) (PairV (#len) (#cap))) st e' st' := by
  simp only [IsOsStep]
  rintro ⟨base', len', _, m', hv, hm', hl, -⟩
  injection hv with h1 h2
  cases go.intoVal_inj h1
  injection h2 with h3
  cases go.intoVal_inj h3
  rw [hm] at hm'
  cases hm'
  exact hlen hl

/-! ## Mapped cells -/

/-- With no change in flight, a mapped cell below EOF holds the file's byte. -/
theorem cellVal_byte (st : OsState) (p : GoString) (f : OsFile) (i : Nat)
    (hf : st.file p = some f) (hi : i < f.cur.length) (hn : ¬ InflightAt st p i) :
    cellVal st p i = LitV (LitByte f.cur[i]) := by
  simp [cellVal, hf, hi, hn]

/-- A mapped cell past EOF is a hole. -/
theorem cellVal_pastEOF (st : OsState) (p : GoString) (f : OsFile) (i : Nat)
    (hf : st.file p = some f) (hi : f.cur.length ≤ i) : cellVal st p i = osHole := by
  simp [cellVal, hf, Nat.not_lt.mpr hi]

/-- A mapped cell an in-flight change may write is a hole. -/
theorem cellVal_inflight (st : OsState) (p : GoString) (i : Nat) (h : InflightAt st p i) :
    cellVal st p i = osHole := by
  unfold cellVal
  split <;> simp [h]

/-- A hole is not a byte, whatever the Go context: a byte load of it is stuck. -/
theorem osHole_not_byte (b : w8) : osHole ≠ LitV (LitByte b) := by
  simp [osHole]

/-! ## Reads -/

/-- With no change in flight on the file, a read sees exactly its bytes from `off`, up to `n`
of them. -/
theorem readSees_exact (st : OsState) (p : GoString) (f : OsFile) (off n : Nat) (r : List w8)
    (hf : st.file p = some f) (hidle : ∀ t c, st.inflight !! t = some c → c.path ≠ p)
    (h : ReadSees st p off n r) : r = (f.cur.drop off).take n := by
  obtain ⟨⟨sz, hsz, hlen⟩, hbytes⟩ := h
  have hsz' : sz = f.cur.length := by
    rcases hsz with hsz | ⟨t, c, ht, hc, -⟩
    · simp [hsz, OsState.size, hf]
    · exact absurd hc (hidle t c ht)
  subst hsz'
  apply List.ext_getElem
  · simp [hlen]
  · intro i h1 h2
    have hi := hbytes i h1 (by rintro ⟨t, c, ht, hc, -⟩; exact hidle t c ht hc)
    simp only [hf, Option.map_some, Option.bind_some] at hi
    rw [List.getElem?_eq_some_iff] at hi
    obtain ⟨_, hi⟩ := hi
    simp [← hi]

/-- A racing read may see any byte where an in-flight change may write. -/
theorem readSees_mix (st : OsState) (p : GoString) (off n : Nat) (r : List w8) (i : Nat) (b : w8)
    (h : ReadSees st p off n r) (hi : InflightAt st p (off + i)) :
    ReadSees st p off n (r.set i b) := by
  obtain ⟨⟨sz, hsz, hlen⟩, hbytes⟩ := h
  refine ⟨⟨sz, hsz, by simp [hlen]⟩, fun j hj hn => ?_⟩
  have hj' : j < r.length := by simpa using hj
  by_cases hij : i = j
  · subst hij; exact absurd hi hn
  · simp [hij]
    exact hbytes j hj' hn

/-- With no change in flight, `fstat` sees exactly the size. -/
theorem statSees_exact (st : OsState) (p : GoString) (sz : Nat)
    (hidle : ∀ t c, st.inflight !! t = some c → c.path ≠ p) (h : StatSees st p sz) :
    sz = st.size p := by
  rcases h with h | ⟨t, c, ht, hc, -⟩
  · exact h
  · exact absurd hc (hidle t c ht)

/-! ## Crashes -/

/-- With no change in flight on the file, a crash right after a successful sync leaves the file
(as the next boot reads it from disk) with exactly the contents the page cache had: the sync
wrote them to disk. This needs what the operations maintain: a clean byte's durable copy is its
page-cache copy, and no byte was lost by a failed sync. -/
theorem crash_after_sync (st : OsState) (p : GoString) (f : OsFile) (img : List w8)
    (hidle : ∀ t c, st.inflight !! t = some c → c.path ≠ p)
    (hcoh : ∀ i, f.dirty i = false → i < f.durable.length → f.durable[i]? = f.cur[i]?)
    (hlost : ∀ i, f.lost i = false)
    (h : CrashImage st p (f.synced (fun _ => False)) img) : img = f.cur := by
  obtain ⟨⟨hlo, hhi⟩, hb⟩ := h
  have hnot : ∀ Q : OsChange → Prop, (∃ t c, st.inflight !! t = some c ∧ c.path = p ∧ Q c) →
      False := by
    rintro Q ⟨t, c, ht, hc, -⟩; exact hidle t c ht hc
  have hlen : img.length = f.cur.length := by
    simp only [OsFile.synced] at hlo hhi
    rcases hlo with hlo | hlo
    · rcases hhi with hhi | hhi
      · omega
      · exact (hnot (fun c => img.length ≤ c.target st) hhi).elim
    · exact (hnot (fun c => c.target st ≤ img.length) hlo).elim
  apply List.ext_getElem hlen
  intro i h1 h2
  have := hb i h1 (by simp [OsFile.synced]) (by simp [OsFile.synced, hlost])
    (by rintro ⟨t, c, ht, hc, -⟩; exact hidle t c ht hc) (by simp [OsFile.synced]; omega)
  rw [this]
  simp only [OsFile.synced, List.getElem_map, List.getElem_range]
  by_cases hd : f.dirty i = true
  · simp [hd, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
  · by_cases hl : f.durable.length ≤ i
    · simp [hl, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
    · have hc := hcoh i (by simpa using hd) (by omega)
      simp [hd, hl, List.getD_eq_getElem?_getD, hc, List.getElem?_eq_getElem h2]

/-- A file as on disk (`ofDisk d`), then one byte below EOF written and not synced: a crash
may keep the old byte, or the new one. -/
theorem crash_unsynced_both (st : OsState) (p : GoString) (d : List w8) (i : Nat) (b : w8)
    (hi : i < d.length) :
    CrashImage st p ((OsFile.ofDisk d).change (writeBytes d i [b]) i (i + 1)) d ∧
    CrashImage st p ((OsFile.ofDisk d).change (writeBytes d i [b]) i (i + 1)) (d.set i b) := by
  have hw : writeBytes d i [b] = d.set i b := by
    simp only [writeBytes, resizeBytes, List.cons_ne_nil, ite_false]
    rw [Nat.max_eq_left (by omega)]
    simp [List.set_eq_take_append_cons_drop, hi]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · simp [OsFile.change, OsFile.ofDisk, hw]
  · intro j hj _ _ _ _; simp [OsFile.change, OsFile.ofDisk]
  · simp [OsFile.change, OsFile.ofDisk, hw]
  · intro j hj hd _ _ _
    have hij : i ≠ j := by
      rintro rfl; simp [OsFile.change, OsFile.ofDisk, inRange] at hd
    simp [OsFile.change, OsFile.ofDisk, hij]

/-- A byte whose writeback a sync failed to do stays lost (arbitrary at a crash) across a later
successful sync, unless it is written again in between. -/
theorem lost_survives_sync (f : OsFile) (i : Nat) (hd : f.dirty i = true) :
    ((f.syncFailed (fun _ => False)).synced (fun _ => False)).lost i = true := by
  simp [OsFile.syncFailed, OsFile.synced, hd]

end OsFsTests
end Perennial
