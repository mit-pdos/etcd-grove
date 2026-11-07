/- Lean-first (no Rocq counterpart). What a retried write leaves of the bytes it covers (each attempt
writes a prefix of the rest of the data, after the bytes a short write left written): the bytes
written form a prefix of the data (`WReach.prefix`), and a byte past that prefix is untouched,
with its clean flag (`pwBytes` keeps it). So a part of the range that the write has not finished
keeps a clean old byte, if all of its old bytes were clean, or is all the new data
(`WReach.torn`).
-/
module

public import Spec.os.CrashSt

@[expose] public section

noncomputable section

namespace Perennial

open Fs

section fin
variable {m : OsMeta} {bs : List (w8 × Bool)} {off : Nat} {data : List w8} {k : Nat}

/-- A byte of the write's range after an attempt that wrote `k` bytes: the data's, not clean, if
the attempt reached it, or untouched (then inside the old file). -/
theorem finBytes_mid (hlen : bs.length = m.size) (hk : k ≤ data.length) (i : Nat)
    (h1 : off ≤ i) (h2 : i < off + data.length) (h3 : i < pwSize m.size off k) :
    (finBytes m bs off data k)[i]? =
      if i < off + k then some (data.getD (i - off) 0, false) else bs[i]? := by
  have hpl := pwBytes_len' (m := m) (bs := bs) (off := off) (data := data) (k := k) hlen
  have hP := pwSize_ge' m.size off k
  have hcl : cfLo m off ≤ off := by unfold cfLo; omega
  have hcb : cfLo m off ≤ bs.length := by unfold cfLo; omega
  unfold finBytes
  rw [List.append_assoc, List.getElem?_append_right (by simp only [List.length_take]; omega),
    List.getElem?_append_left (by simp only [List.length_take, hpl]; omega)]
  simp only [List.length_take]
  rw [show min (cfLo m off) bs.length = cfLo m off by unfold cfLo; omega]
  have hlt : i - cfLo m off < (pwBytes m.size off data k (cfRange m bs off data.length)).length := by
    rw [hpl]; omega
  rw [List.getElem?_eq_getElem hlt]
  simp only [pwBytes, List.getElem_map, List.getElem_range]
  rw [show min off m.size = cfLo m off from rfl, show cfLo m off + (i - cfLo m off) = i by omega]
  unfold pwByte
  rw [if_neg (by omega)]
  by_cases hik : i < off + k
  · rw [if_pos hik, if_pos hik]; simp [show ¬ off + k ≤ i by omega]
  · rw [if_neg hik, if_neg hik]
    have him : i < m.size := by unfold pwSize at h3; split at h3 <;> omega
    have hlo : cfLo m off = off := by unfold cfLo; omega
    have hr : (cfRange m bs off data.length)[i - cfLo m off]? = bs[i]? := by
      unfold cfRange; rw [List.getElem?_take_of_lt (by unfold cfHi; omega),
        List.getElem?_drop, show cfLo m off + (i - cfLo m off) = i by omega]
    rw [List.getD_eq_getElem?_getD, hr, List.getElem?_eq_getElem (by omega)]
    simp [show off + k ≤ i by omega]

end fin

/-- An attempt after `nn ≤ j` of a write's bytes were written, over the size the first `j` left:
the size the first `max j (nn + k)` would leave. -/
theorem pwSize_from' (sz off j nn k : Nat) (hnn : nn ≤ j) :
    pwSize (pwSize sz off j) (off + nn) k = pwSize sz off (max j (nn + k)) := by
  unfold pwSize
  by_cases hj : j = 0
  · have : nn = 0 := by omega
    subst hj this; simp
  · by_cases hk : k = 0
    · subst hk; simp [hj, Nat.max_eq_left hnn]
    · rw [if_neg hk, if_neg hj, if_neg (by omega)]; omega

theorem getD_drop' (data : List w8) (nn j : Nat) :
    (data.drop nn).getD j 0 = data.getD (nn + j) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- The bytes a retried write of `data` at `off` (inside the file) covers: a prefix `K` of the
data, at least the `nn` bytes the loop counts as written, is written (the size is as one attempt
of `K` bytes leaves it), the rest is untouched. -/
theorem WReach.prefix {m : OsMeta} {bs : List (w8 × Bool)} {off : Nat} {data : List w8}
    {C : Nat → Nat → Nat → Prop} {nn : Nat} {m' : OsMeta} {bs' : List (w8 × Bool)}
    (h : WReach C m bs off data nn m' bs')
    (hl : bs.length = m.size) (hoff : off ≤ m.size) :
    ∃ K ≤ data.length, nn ≤ K ∧ m'.size = pwSize m.size off K ∧
      ∀ i, off ≤ i → i < off + data.length → i < pwSize m.size off K →
      bs'[i]? = if i < off + K then some (data.getD (i - off) 0, false) else bs[i]? := by
  induction h with
  | refl =>
    exact ⟨0, Nat.zero_le _, Nat.le_refl _, by simp [pwSize], fun i _ _ _ => by rw [if_neg (by omega)]⟩
  | @step nn m1 bs1 k nn' hR hnn hk _ hnn' ih =>
    obtain ⟨K, hKl, hnK, hsz, hK⟩ := ih
    have hN := hR.narrow hl hoff
    have hdl : (data.drop nn).length = data.length - nn := List.length_drop
    have hS : off + nn ≤ m1.size := by
      rw [hsz]; unfold pwSize; split
      · have : nn = 0 := by omega
        omega
      · omega
    refine ⟨max K (nn + k), by omega, by omega, ?_, fun i h1 h2 h3 => ?_⟩
    · show pwSize m1.size (off + nn) k = _
      rw [hsz, pwSize_from' _ _ _ _ _ hnK]
    rw [← pwSize_from' _ _ _ _ _ hnK, ← hsz] at h3
    by_cases a : i < off + nn
    · rw [finBytes_pre hN.len i (by unfold cfLo; omega)]
      have h3' : i < pwSize m.size off K := by rw [← hsz]; omega
      rw [hK i h1 h2 h3', if_pos (by omega), if_pos (by omega)]
    · rw [finBytes_mid (m := m1) (bs := bs1) (off := off + nn) (data := data.drop nn) hN.len
        (by rw [hdl]; exact hk) i (by omega) (by rw [hdl]; omega) h3]
      by_cases b : i < off + nn + k
      · rw [if_pos b, if_pos (by omega), getD_drop', show nn + (i - (off + nn)) = i - off by omega]
      · rw [if_neg b]
        have h3' : i < pwSize m.size off K := by
          rw [← hsz]; unfold pwSize at h3; split at h3 <;> omega
        rw [hK i h1 h2 h3']
        by_cases c : i < off + K
        · rw [if_pos c, if_pos (by omega)]
        · rw [if_neg c, if_neg (by omega)]

/-- A part `[a, a + w)` of the write's range, held by the reached state: untouched (inside the
old file), or with its first byte the data's and either an old byte left (inside the old file,
with its flag) or all of it the data's. -/
theorem WReach.torn {m : OsMeta} {bs : List (w8 × Bool)} {off : Nat} {data : List w8}
    {C : Nat → Nat → Nat → Prop} {nn : Nat} {m' : OsMeta} {bs' : List (w8 × Bool)}
    (h : WReach C m bs off data nn m' bs')
    (hl : bs.length = m.size) (hoff : off ≤ m.size) {a w : Nat} (hw : 0 < w) (ha : off ≤ a)
    (haw : a + w ≤ off + data.length) (hsz : a + w ≤ bs'.length) :
    (a + w ≤ bs.length ∧ ∀ j < w, bs'[a + j]? = bs[a + j]?) ∨
    (bs'[a]? = some (data.getD (a - off) 0, false) ∧
      ((∃ j < w, a + j < bs.length ∧ bs'[a + j]? = bs[a + j]?) ∨
        ∀ j < w, bs'[a + j]? = some (data.getD (a + j - off) 0, false))) := by
  obtain ⟨K, -, -, hs, hK⟩ := h.prefix hl hoff
  have hN := h.narrow hl hoff
  rw [hN.len, hs] at hsz
  by_cases h0 : a < off + K
  · right
    refine ⟨by rw [hK a ha (by omega) (by omega), if_pos h0], ?_⟩
    by_cases h1 : a + w ≤ off + K
    · exact .inr fun j hj => by rw [hK (a + j) (by omega) (by omega) (by omega), if_pos (by omega)]
    · have hm : a + (w - 1) < m.size := by unfold pwSize at hsz; split at hsz <;> omega
      exact .inl ⟨w - 1, by omega, by omega, by
        rw [hK (a + (w - 1)) (by omega) (by omega) (by omega), if_neg (by omega)]⟩
  · left
    have hm : a + w ≤ m.size := by unfold pwSize at hsz; split at hsz <;> omega
    refine ⟨by omega, fun j hj => ?_⟩
    rw [hK (a + j) (by omega) (by omega) (by omega), if_neg (by omega)]

end Perennial
