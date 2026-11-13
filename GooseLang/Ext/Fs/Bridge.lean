/-
What a crash leaves of a byte, from its crash candidates (`Impl.lean`, `CrashFile`): one of their
values, or zero at or past the smallest size since the last sync (`crash_byte`); a byte below that
size whose candidates all hold `x` and that the crash's size covers comes back as `x`
(`crash_keeps`). And the arithmetic of the file effects the specs use. Untrusted.
-/
module

public import GooseLang.Ext.Fs.Impl

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

theorem pageIn_of_lt {sz b : Nat} (h : b < sz) : pageIn sz b = true := by
  simp only [pageIn, decide_eq_true_eq]; omega

theorem diskByte_of_lt {img : Nat → w8} {sz b : Nat} (h : b < sz) : diskByte img sz b = img b := by
  simp [diskByte, pageIn_of_lt h]

/-- `x` rounded up to a 4096-byte page. -/
def pageUp (x : Nat) : Nat := 4096 * ((x + 4095) / 4096)

theorem pageIn_pageUp {L b : Nat} (h : pageUp L ≤ b) : pageIn L b = false := by
  simp only [pageIn, pageUp, decide_eq_false_iff_not] at *; omega

theorem pageUp_mono {a b : Nat} (h : a ≤ b) : pageUp a ≤ pageUp b := by
  simp only [pageUp]; omega

theorem le_pageUp (a : Nat) : a ≤ pageUp a := by simp only [pageUp]; omega

theorem diskByte_past {img : Nat → w8} {sz b : Nat} (h : pageUp sz ≤ b) : diskByte img sz b = 0 := by
  simp [diskByte, pageIn_pageUp h]

theorem contents_length (f : OsFile) : f.contents.length = f.size := by simp [OsFile.contents]

theorem contents_getElem? (f : OsFile) (b : Nat) :
    f.contents[b]? = if b < f.size then some (f.cache b) else none := by
  simp only [OsFile.contents, List.getElem?_map]
  split
  · rename_i h; simp [List.getElem?_range h]
  · rename_i h; simp [List.getElem?_range', h]

theorem contents_getElem?_of_lt {f : OsFile} {b : Nat} (h : b < f.size) :
    f.contents[b]? = some (f.cache b) := by rw [contents_getElem?, if_pos h]

/-- **A crash leaves each byte one of its candidates' values, or zero at or past the smallest size
since the last sync** (below the crash's size: past it, the file of a crash holds no byte). -/
theorem crash_byte {st : OsState} {i : Ino} {f f' : OsFile} {b : Nat}
    (hc : CrashFile st i f f') (hb : b < f'.size) :
    (∃ s, (f'.cache b, s) ∈ f.cand b) ∨ (f.sizeLo ≤ b ∧ f'.cache b = 0) := by
  obtain ⟨sz, img, -, hcand, rfl⟩ := hc
  simp only [OsFile.ofDisk] at hb ⊢
  rw [diskByte_of_lt hb]; exact hcand b

/-- **A crash keeps a byte whose candidates all hold `x`**, below the smallest size since the last
sync, if its size covers it. -/
theorem crash_keeps {st : OsState} {i : Ino} {f f' : OsFile} {b : Nat} {x : w8}
    (hc : CrashFile st i f f') (hv : ∀ p ∈ f.cand b, p.1 = x) (hlo : b < f.sizeLo)
    (hsz : b < f'.size) : f'.contents[b]? = some x := by
  rcases crash_byte hc hsz with ⟨s, hs⟩ | ⟨h, -⟩
  · rw [contents_getElem?_of_lt hsz, ← hv _ hs]
  · omega

/-- The size a crash leaves the file with: between the smallest and the largest since the last
sync, or the target of the change in flight. -/
theorem crash_size {st : OsState} {i : Ino} {f f' : OsFile} (hc : CrashFile st i f f') :
    (f.sizeLo ≤ f'.size ∨ ∃ t c, st.proc.inflight !! t = some c ∧ c.ino = i ∧ c.target ≤ f'.size) ∧
    (f'.size ≤ f.sizeHi ∨ ∃ t c, st.proc.inflight !! t = some c ∧ c.ino = i ∧ f'.size ≤ c.target) := by
  obtain ⟨sz, img, hsz, -, rfl⟩ := hc; exact hsz

/-! ## The file effects -/

theorem resized_getD (f : OsFile) (sz b : Nat) (hb : b < sz) (hbs : b < f.size) :
    (f.resized sz).getD b 0 = f.cache b := by
  simp [OsFile.resized, List.getD_eq_getElem?_getD, hb, hbs]

/-- An extension reads zeros past the old size. -/
theorem resized_getD_past (f : OsFile) (sz b : Nat) (hbs : f.size ≤ b) :
    (f.resized sz).getD b 0 = 0 := by
  by_cases hb : b < sz
  · simp [OsFile.resized, List.getD_eq_getElem?_getD, hb, Nat.not_lt.2 hbs]
  · simp [OsFile.resized, List.getD_eq_getElem?_getD, hb]

theorem resized_length (f : OsFile) (sz : Nat) : (f.resized sz).length = sz := by
  simp [OsFile.resized]

theorem written_length (f : OsFile) (off : Nat) (d : List w8) :
    (f.written off d).length = max f.size (off + d.length) := by
  unfold OsFile.written
  simp only [List.length_append, List.length_take, List.length_drop, resized_length]
  omega

/-- The bytes `written` gives: the data inside it, the old bytes before it (below the size), zeros
in the gap past the end. -/
theorem written_getD (f : OsFile) (off : Nat) (d : List w8) (b : Nat) :
    (f.written off d).getD b 0 =
      if off ≤ b ∧ b < off + d.length then d.getD (b - off) 0
      else if b < f.size then f.cache b else 0 := by
  unfold OsFile.written
  generalize hn : max f.size (off + d.length) = n
  have hcl : (f.resized n).length = n := resized_length f n
  have hA : ((f.resized n).take off).length = off := by
    rw [List.length_take, hcl]; exact Nat.min_eq_left (by omega)
  have hAd : ((f.resized n).take off ++ d).length = off + d.length := by
    rw [List.length_append, hA]
  rw [List.getD_eq_getElem?_getD]
  by_cases h1 : b < off
  · rw [List.getElem?_append_left (by rw [hAd]; omega), List.getElem?_append_left (by rw [hA]; exact h1),
      List.getElem?_take_of_lt h1, ← List.getD_eq_getElem?_getD]
    rw [if_neg (by omega)]
    by_cases hbs : b < f.size
    · rw [if_pos hbs, resized_getD _ _ _ (by omega) hbs]
    · rw [if_neg hbs, resized_getD_past _ _ _ (by omega)]
  · by_cases h2 : b < off + d.length
    · rw [List.getElem?_append_left (by rw [hAd]; exact h2), List.getElem?_append_right (by rw [hA]; omega),
        hA, if_pos ⟨by omega, h2⟩, List.getD_eq_getElem?_getD]
    · rw [List.getElem?_append_right (by rw [hAd]; omega), hAd, List.getElem?_drop,
        ← List.getD_eq_getElem?_getD, if_neg (by omega)]
      have : off + d.length + (b - (off + d.length)) = b := by omega
      rw [this]
      by_cases hbs : b < f.size
      · rw [if_pos hbs, resized_getD _ _ _ (by omega) hbs]
      · rw [if_neg hbs, resized_getD_past _ _ _ (by omega)]

end Fs
end Perennial

end
