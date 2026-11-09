/-
What a crash keeps of a file besides its clean bytes (`CrashFiles.lean`'s `FileCrashedR`), from the
facts a take lemma returns (`CrashSeenR`, `CrashTok.lean`). Untrusted. A crash is a machine crash
(`Impl.lean`): a crashed file is on disk, so every byte of it below its size is clean.

* `RunsKept`: every byte of the runs the taker held, below the new size, is clean.
* `TailKept`: every byte past the old size, below the new one, is clean.
* `crashSeen_tokKept`: every byte a taken write takes, below the new size, is clean.
-/
module

public import GooseLang.Ext.Fs.CrashTok

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

open Iris

/-! ## A file across a landing -/

theorem secHits_self {lo hi b : Nat} (h1 : lo ≤ b) (h2 : b < hi) : secHits lo hi (b / 512) = true := by
  have h3 : 512 * (b / 512) ≤ b := Nat.mul_div_le b 512
  have h4 : b < 512 * (b / 512 + 1) := by
    have := Nat.lt_mul_div_succ b (show 0 < 512 by decide); omega
  simp [secHits]; omega

/-- A byte inside a change's bytes is what the new contents have there. -/
theorem rawAt_change_in (f : OsFile) (c : List w8) (lo hi b : Nat) (h1 : lo ≤ b) (h2 : b < hi) :
    (f.change c lo hi).rawAt b = c.getD b 0 := by
  rw [rawAt_def]
  simp only [OsFile.change, secHits_self h1 h2, if_true]
  rw [last_mk_append, secOf_getD]

/-- What a write leaves inside its data. -/
theorem written_in (f : OsFile) (off : Nat) (d : List w8) (b : Nat) (hd : d ≠ [])
    (h1 : off ≤ b) (h2 : b < off + d.length) : (f.written off d).getD b 0 = d.getD (b - off) 0 := by
  unfold OsFile.written
  rw [if_neg hd]
  generalize hn : max f.size (off + d.length) = n
  have hcl : (f.resized n).length = n := resized_length f n
  have hoff : off ≤ n := by omega
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.append_assoc,
    List.getElem?_append_right (by simp; omega), List.getElem?_append_left (by simp; omega)]
  simp only [List.length_take, hcl, Nat.min_eq_left hoff]

/-- The size of a landed write. -/
theorem landWrite_size (f : OsFile) (off : Nat) (data : List w8) (k : Nat) (hk : k ≤ data.length) :
    (f.landWrite off data k).size = if k = 0 then f.size else max f.size (off + k) := by
  unfold OsFile.landWrite
  split
  · rfl
  · rename_i hk0
    have hd : data.take k ≠ [] := by
      intro h; have := congrArg List.length h
      rw [List.length_take, Nat.min_eq_left hk] at this; exact hk0 this
    simp only [OsFile.change]
    rw [written_length f off _ hd, List.length_take, Nat.min_eq_left hk]

/-- Whether a change may grow the file of size `s` (`Reaches`, by kind). -/
def KReach (s : Nat) : OsChangeKind → Prop
  | .write off data => s < off + data.length
  | .truncate _ => True

theorem reaches_kreach (st : OsState) (c : OsChange) :
    Reaches st c ↔ KReach (st.size c.ino) c.kind := by
  unfold Reaches KReach; cases c.kind <;> rfl

/-- **Changes none of which may grow the file keep its size.** -/
theorem size_landed_noreach :
    ∀ {ks : List OsChangeKind} {f g : OsFile}, Landed ks f g → (∀ k ∈ ks, ¬ KReach f.size k) →
      g.size = f.size := by
  intro ks f g hl
  induction hl with
  | nil f => intro _; rfl
  | write off data k ks f g hk _ ih =>
    intro hn
    have h0 := hn _ List.mem_cons_self
    simp only [KReach] at h0
    have hs : (f.landWrite off data k).size = f.size := by
      rw [landWrite_size f off data k hk]; split <;> omega
    rw [ih (fun k' hk' => by rw [hs]; exact hn k' (List.mem_cons_of_mem _ hk')), hs]
  | trunc sz sz' ks f g _ _ _ ih =>
    intro hn
    exact absurd trivial (hn _ List.mem_cons_self)

/-- **Landings of one write, of `data` at `off`, leave its data past the old size.** -/
theorem tail_landed {off : Nat} {data : List w8} {s0 : Nat} (hoff : off ≤ s0) :
    ∀ {ks : List OsChangeKind} {f g : OsFile}, Landed ks f g → (∀ k ∈ ks, k = .write off data) →
      s0 ≤ f.size →
      (∀ b, s0 ≤ b → b < f.size → f.rawAt b = data.getD (b - off) 0 ∧ b < off + data.length) →
      ∀ b, s0 ≤ b → b < g.size → g.rawAt b = data.getD (b - off) 0 ∧ b < off + data.length := by
  intro ks f g hl
  induction hl with
  | nil f => intro _ _ h; exact h
  | write off' data' k ks f g hk _ ih =>
    intro hall hs hinv
    have he := hall _ List.mem_cons_self
    simp only [OsChangeKind.write.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    apply ih (fun k' hk' => hall k' (List.mem_cons_of_mem _ hk'))
    · rw [landWrite_size f off' data' k hk]; split <;> omega
    · intro b hb1 hb2
      rw [landWrite_size f off' data' k hk] at hb2
      unfold OsFile.landWrite
      split
      · rename_i hk0; rw [if_pos hk0] at hb2; exact hinv b hb1 hb2
      rename_i hk0
      rw [if_neg hk0] at hb2
      have hd : data'.take k ≠ [] := by
        intro h; have := congrArg List.length h
        rw [List.length_take, Nat.min_eq_left hk] at this; exact hk0 this
      by_cases hin : min off' f.size ≤ b ∧ b < off' + k
      · rw [rawAt_change_in _ _ _ _ _ hin.1 hin.2, written_in f off' _ b hd (by omega) (by
          rw [List.length_take, Nat.min_eq_left hk]; omega)]
        refine ⟨?_, by omega⟩
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega)]
      · have hbf : b < f.size := by omega
        obtain ⟨h1, h2⟩ := hinv b hb1 hbf
        refine ⟨?_, h2⟩
        rw [rawAt_change _ _ _ _ _ hin (by
          rw [(written_out f off' _ b hd hbf (by
            rw [List.length_take, Nat.min_eq_left hk]; omega)).1]), h1]
  | trunc sz sz' ks f g _ _ _ ih =>
    intro hall
    have := hall _ List.mem_cons_self; cases this

/-! ## From a take lemma's facts -/

/-- Every byte of the runs `rs`, below the new size, is clean. -/
def RunsKept (rs : List (Nat × DFrac × List (w8 × Bool))) (fo : Option OsFile) : Prop :=
  ∀ f', fo = some f' → ∀ r ∈ rs, ∀ k x, r.2.2[k]? = some x → r.1 + k < f'.size →
    CleanPhys f' (r.1 + k)

/-- Every byte past the old size `s`, below the new one, is clean (`ts`, the taken writes, is
unused: a crashed file is on disk). -/
def TailKept (s : Nat) (_ts : List (Nat × TokInfo)) (fo : Option OsFile) : Prop :=
  ∀ f', fo = some f' → ∀ b, s ≤ b → b < f'.size → CleanPhys f' b

/-- An in-flight change on the file: one of the taken tokens, or another token's (not reaching,
and clear of the runs). -/
theorem inflight_tok {st : OsState} {Γb Γm Γf} {Γt : GMap Nat TokInfo} (hcoh : OsCoh st Γb Γm Γf Γt)
    {t : Nat} {c : OsChange} (h : st.proc.inflight !! t = some c) :
    ∃ ti, Γt !! t = some ti ∧ ti.c = c := by
  have := hcoh.toks t
  rw [h] at this
  cases ht : Γt !! t with
  | none => rw [ht] at this; cases this
  | some ti => rw [ht] at this; exact ⟨ti, rfl, Option.some.inj this⟩

/-- A byte below the size that a change affects is in its range. -/
theorem affects_affRange {st : OsState} {c : OsChange} {b : Nat} (ha : Affects st c b)
    (hb : b < st.size c.ino) : b ∈ affRange st c := by
  unfold Affects at ha
  unfold affRange affLo affHi
  rw [List.mem_range'_1]
  cases hk : c.kind with
  | write off data =>
    rw [hk] at ha; simp only [hk]
    simp only [inRange, Bool.and_eq_true, decide_eq_true_eq] at ha; omega
  | truncate sz => rw [hk] at ha; simp only [hk] at ha ⊢; omega

section seen
variable {Q : OsState → OsState → Prop}

/-- **A crashed file is on disk** (`MachineCrash`'s files). -/
theorem crashSeen_ofDisk {i : Ino} {m : OsMeta} {rs : List (Nat × DFrac × List (w8 × Bool))}
    {ts : List (Nat × TokInfo)} {f : OsFile} (h : CrashSeenR Q i m rs ts (some f)) :
    ∃ vs sz kp, f = OsFile.ofDisk vs sz kp := by
  obtain ⟨st, st', Γb, Γm, Γf, Γt, -, hcr, -, hfo, -⟩ := h
  obtain ⟨_hp, _hr, _hl, _hc, _hi, _hS, hfiles⟩ := hcr
  by_cases hn : Named st'.fs.treeDur i
  · obtain ⟨f0, f'', -, ⟨sz, vs, -, -, -, rfl⟩, h''⟩ := (hfiles i).1 hn
    rw [h''] at hfo; cases hfo
    exact ⟨vs, sz, _, rfl⟩
  · rw [(hfiles i).2 hn] at hfo; cases hfo

/-- **A crash leaves the runs' bytes clean** (a crashed file is on disk). -/
theorem crashSeen_runsKept {i : Ino} {m : OsMeta} {rs : List (Nat × DFrac × List (w8 × Bool))}
    {ts : List (Nat × TokInfo)} {fo : Option OsFile} (h : CrashSeenR Q i m rs ts fo)
    (hts : ∀ x ∈ ts, ∃ off data, x.2.c.kind = .write off data ∧
      ∀ r ∈ rs, ∀ k < r.2.2.length, r.1 + k < m.size → r.1 + k < off ∨ off + data.length ≤ r.1 + k) :
    RunsKept rs fo := by
  obtain ⟨st, st', Γb, Γm, Γf, Γt, hcoh, hcr, -, hfo, hm, hxs, hts', hall, -⟩ := h
  obtain ⟨f0, hf0, hok0⟩ := hcoh.meta_some i m hm
  intro f' hf' r hr k x hk hbs
  have hkl : k < r.2.2.length := (List.getElem?_eq_some_iff.1 hk).1
  have hx := hxs r hr k hkl
  rw [(List.getElem?_eq_some_iff.1 hk).2] at hx
  obtain ⟨f, hf, hcur, -⟩ := hcoh.bytes i _ x hx
  simp only [OsState.file] at hf
  have hbf : r.1 + k < f.size := by
    rw [contents_getElem?] at hcur; split at hcur
    · assumption
    · cases hcur
  have hraw : f.rawAt (r.1 + k) = x.1 := by
    rw [contents_getElem?, if_pos hbf] at hcur; exact Option.some.inj hcur
  rw [← hfo] at hf'
  have hc := hcr
  · -- a machine crash: the file is on disk
    obtain ⟨_hp, _hr, _hl, _hc, _hi, _hS, hfiles⟩ := hc
    by_cases hn : Named st'.fs.treeDur i
    · obtain ⟨f0, f'', -, ⟨sz, vs, -, -, -, rfl⟩, h''⟩ := (hfiles i).1 hn
      rw [h''] at hf'; cases hf'
      exact ofDisk_clean vs sz _ hbs
    · rw [(hfiles i).2 hn] at hf'; cases hf'

/-- **A crash leaves the bytes past the old size clean** (a crashed file is on disk). -/
theorem crashSeen_tailKept {i : Ino} {m : OsMeta} {rs : List (Nat × DFrac × List (w8 × Bool))}
    {ts : List (Nat × TokInfo)} {fo : Option OsFile} (h : CrashSeenR Q i m rs ts fo)
    (hts : ∀ x ∈ ts, ∃ off data, x.2.c.kind = .write off data ∧ off ≤ m.size) :
    TailKept m.size ts fo := by
  obtain ⟨st, st', Γb, Γm, Γf, Γt, hcoh, hcr, -, hfo, hm, -, hts', hall, -⟩ := h
  intro f' hf' b hb1 hb2
  rw [← hfo] at hf'
  obtain ⟨f, hf, hok⟩ := hcoh.meta_some i m hm
  have hc := hcr
  · obtain ⟨_hp, _hr, _hl, _hc, _hi, _hS, hfiles⟩ := hc
    by_cases hn : Named st'.fs.treeDur i
    · obtain ⟨f0, f'', -, ⟨sz, vs, -, -, -, rfl⟩, h''⟩ := (hfiles i).1 hn
      rw [h''] at hf'; cases hf'
      exact ofDisk_clean vs sz _ hb2
    · rw [(hfiles i).2 hn] at hf'; cases hf'

end seen

/-! ## The bytes a taken write takes -/

/-- A landed prefix of `k` bytes leaves a clean byte past it clean. -/
theorem clean_landWrite_pre {f : OsFile} {b : Nat} (off : Nat) (data : List w8) (k : Nat)
    (hk : k ≤ data.length) (hbs : b < f.size) (hcp : CleanPhys f b) (hout : b < off ∨ off + k ≤ b) :
    CleanPhys (f.landWrite off data k) b := by
  unfold OsFile.landWrite
  split
  · exact hcp
  rename_i hk0
  have hlen : (data.take k).length = k := by rw [List.length_take]; exact Nat.min_eq_left hk
  have hd : data.take k ≠ [] := by
    intro h; rw [h] at hlen; simp at hlen; omega
  have hout' : b < off ∨ off + (data.take k).length ≤ b := by rw [hlen]; exact hout
  have hc := written_out f off (data.take k) b hd hbs hout'
  have hnr : ¬ (min off f.size ≤ b ∧ b < off + k) := by
    intro ⟨h1, h2⟩
    rcases hout with h3 | h3
    · have : min off f.size = off ∨ min off f.size = f.size := by omega
      omega
    · omega
  exact clean_change hnr hc.1 hc.2 hcp

/-- **Landings around a byte that one write may change**: the byte is what it was (clean if it was,
when `C`), or that write's. -/
theorem landed_tok {s b off : Nat} {data : List w8} (hob : off ≤ b) :
    ∀ {ks : List OsChangeKind} {f g : OsFile}, Landed ks f g →
      (∀ k ∈ ks, k = .write off data ∨ ¬ KAff s k b) → b < s → b < f.size → ∀ (C : Prop) x,
      ((f.rawAt b = x ∧ (C → CleanPhys f b)) ∨ f.rawAt b = data.getD (b - off) 0) →
      b < g.size ∧ ((g.rawAt b = x ∧ (C → CleanPhys g b)) ∨ g.rawAt b = data.getD (b - off) 0) := by
  intro ks f g hl
  induction hl with
  | nil f => intro _ _ hb C x hx; exact ⟨hb, hx⟩
  | write off' data' k ks f g hk _ ih =>
    intro hall hs hb C x hx
    apply ih (fun k' hk' => hall k' (List.mem_cons_of_mem _ hk')) hs
    · rw [landWrite_size f off' data' k hk]; split <;> omega
    rcases hall _ List.mem_cons_self with he | hn
    · -- the write that may change the byte
      simp only [OsChangeKind.write.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      by_cases hk0 : k = 0
      · subst hk0; unfold OsFile.landWrite; rw [if_pos rfl]; exact hx
      have hd : data'.take k ≠ [] := by
        intro h; have := congrArg List.length h
        rw [List.length_take, Nat.min_eq_left hk] at this; exact hk0 this
      by_cases hin : b < off' + k
      · right
        unfold OsFile.landWrite; rw [if_neg hk0]
        rw [rawAt_change_in _ _ _ _ _ (by omega) hin, written_in f off' _ b hd hob (by
          rw [List.length_take, Nat.min_eq_left hk]; omega)]
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega)]
      · have hw := (written_out f off' _ b hd hb (.inr (by
          rw [List.length_take, Nat.min_eq_left hk]; omega))).1
        have hr : (f.landWrite off' data' k).rawAt b = f.rawAt b := by
          unfold OsFile.landWrite; rw [if_neg hk0]
          exact rawAt_change _ _ _ _ _ (by omega) hw
        rw [hr]
        rcases hx with ⟨hx, hc⟩ | hx
        · exact .inl ⟨hx, fun h => clean_landWrite_pre off' data' k hk hb (hc h) (.inr (by omega))⟩
        · exact .inr hx
    · -- another change, which does not reach the byte
      simp only [KAff] at hn
      have hout : b < off' ∨ off' + data'.length ≤ b := by
        by_cases h : b < off'
        · exact .inl h
        · exact .inr (Classical.byContradiction fun h' => hn ⟨by omega, by omega⟩)
      rcases hx with ⟨hx, hc⟩ | hx
      · exact .inl ⟨(holds_landWrite off' data' k hk ⟨hb, hx⟩ (.inr hout)).2,
          fun h => clean_landWrite off' data' k hk hb (hc h) hout⟩
      · exact .inr (holds_landWrite off' data' k hk ⟨hb, hx⟩ (.inr hout)).2
  | trunc sz sz' ks f g h1 h2 _ ih =>
    intro hall hs hb C x hx
    rcases hall _ List.mem_cons_self with he | hn
    · cases he
    simp only [KAff] at hn
    apply ih (fun k' hk' => hall k' (List.mem_cons_of_mem _ hk')) hs
    · simp only [OsFile.truncate, OsFile.change, resized_length]; omega
    rcases hx with ⟨hx, hc⟩ | hx
    · exact .inl ⟨(holds_truncate sz' ⟨hb, hx⟩ (by omega)).2,
        fun h => clean_truncate sz' hb (by omega) (hc h)⟩
    · exact .inr (holds_truncate sz' ⟨hb, hx⟩ (by omega)).2

section seen2
variable {Q : OsState → OsState → Prop}

/-- **A crash leaves a byte a taken write takes** clean (a crashed file is on disk). -/
theorem crashSeen_tokKept {i : Ino} {m : OsMeta} {rs : List (Nat × DFrac × List (w8 × Bool))}
    {ts : List (Nat × TokInfo)} {fo : Option OsFile} (h : CrashSeenR Q i m rs ts fo)
    {t : Nat} {ti : TokInfo} (hx : (t, ti) ∈ ts) (hci : ti.c.ino = i) {off : Nat} {data : List w8}
    (hkind : ti.c.kind = .write off data) (hoff : off ≤ m.size) :
    ∀ f', fo = some f' → ∀ j y, ti.saved[j]? = some y → off + j < f'.size →
      CleanPhys f' (off + j) := by
  obtain ⟨st, st', Γb, Γm, Γf, Γt, hcoh, hcr, -, hfo, hm, -, hts', -, hwfs⟩ := h
  intro f' hf' j y hy hjs
  rw [← hfo] at hf'
  have hti := hts' _ hx
  obtain ⟨f, hf, hok⟩ := hcoh.meta_some i m hm
  have hs : st.size i = f.size := by simp [OsState.size, OsState.file, hf]
  have hms : m.size = f.size := hok.size
  obtain ⟨f0, hf0, hsv⟩ := hcoh.tok_saved t ti hti
  rw [hci] at hf0
  simp only [OsState.file, hf, Option.some.injEq] at hf0; subst hf0
  have hlo : affLo st ti.c = off := by
    unfold affLo; rw [hkind]; dsimp only; rw [hci, hs]; omega
  -- the byte: below the size, its page cache's byte `y`
  rw [hsv] at hy
  simp only [List.getElem?_map] at hy
  unfold affRange at hy
  have hj : j < affHi st ti.c - affLo st ti.c := by
    obtain ⟨a, ha, -⟩ := Option.map_eq_some_iff.1 hy
    simpa using (List.getElem?_eq_some_iff.1 ha).1
  rw [hlo] at hy hj
  rw [List.getElem?_range' hj] at hy
  simp only [Option.map_some, Option.some.injEq, Nat.one_mul] at hy
  have hhi : affHi st ti.c = min (off + data.length) f.size := by
    unfold affHi; rw [hkind]; dsimp only; rw [hci, hs]
  rw [hhi] at hj
  have hbf : off + j < f.size := by omega
  have hjl : j < data.length := by omega
  have hraw : f.rawAt (off + j) = y := by
    rw [← hy, List.getD_eq_getElem?_getD, contents_getElem?, if_pos hbf]; rfl
  have hc := hcr
  · obtain ⟨_hp, _hr, _hl, _hc, _hi, _hS, hfiles⟩ := hc
    by_cases hn : Named st'.fs.treeDur i
    · obtain ⟨f1, f'', -, ⟨sz, vs, -, -, -, rfl⟩, h''⟩ := (hfiles i).1 hn
      rw [h''] at hf'; cases hf'
      exact ofDisk_clean vs sz _ hjs
    · rw [(hfiles i).2 hn] at hf'; cases hf'

end seen2

end Fs
end Perennial

end
