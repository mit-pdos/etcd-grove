/- Lean-first (no Rocq counterpart). What a retried write leaves of the bytes it covers: the bytes
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

section fin
variable {m : OsMeta} {bs : List (w8 × Bool)} {off : Nat} {data : List w8} {k : Nat}

/-- A byte of the write's range after an attempt that wrote `k` bytes: the data's, not clean, if
the attempt reached it, or untouched (then inside the old file). -/
theorem finBytes_mid (hlen : bs.length = m.size) (hk : k ≤ data.length) (i : Nat)
    (h1 : off ≤ i) (h2 : i < off + data.length) (h3 : i < pwSize m.size off k) :
    (finBytes m bs off data k)[i]? =
      if i < off + k then some (data.getD (i - off) 0, false) else bs[i]? := by
  have hpl := pwBytes_len' (m := m) (bs := bs) (off := off) (data := data) (k := k) hlen
  have hP := pwSize_ge m.size off k
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

/-- The bytes a retried write of `data` at `off` covers: a prefix `K` of the data is written
(the size is as one attempt of `K` bytes leaves it), the rest is untouched. -/
theorem WReach.prefix {m : OsMeta} {bs : List (w8 × Bool)} {off : Nat} {data : List w8}
    {m' : OsMeta} {bs' : List (w8 × Bool)} (h : WReach m bs off data m' bs')
    (hl : bs.length = m.size) :
    ∃ K ≤ data.length, m'.size = pwSize m.size off K ∧
      ∀ i, off ≤ i → i < off + data.length → i < pwSize m.size off K →
      bs'[i]? = if i < off + K then some (data.getD (i - off) 0, false) else bs[i]? := by
  induction h with
  | refl => exact ⟨0, Nat.zero_le _, by simp [pwSize], fun i _ _ _ => by rw [if_neg (by omega)]⟩
  | @step m1 bs1 k hR hk ih =>
    obtain ⟨K, hKl, hsz, hK⟩ := ih
    have hN := hR.narrow hl
    refine ⟨max K k, by omega, ?_, fun i h1 h2 h3 => ?_⟩
    · show pwSize m1.size off k = _
      rw [hsz, pwSize_pwSize]
    rw [← pwSize_pwSize, ← hsz] at h3
    rw [finBytes_mid hN.len hk i h1 h2 h3]
    by_cases a : i < off + k
    · rw [if_pos a, if_pos (by omega)]
    · rw [if_neg a]
      have h3' : i < pwSize m.size off K := by
        rw [← hsz]; unfold pwSize at h3; split at h3 <;> omega
      rw [hK i h1 h2 h3']
      by_cases b : i < off + K
      · rw [if_pos b, if_pos (by omega)]
      · rw [if_neg b, if_neg (by omega)]

/-- A part `[a, a + w)` of the write's range, held by the reached state: untouched (inside the
old file), or with its first byte the data's and either an old byte left (inside the old file,
with its flag) or all of it the data's. -/
theorem WReach.torn {m : OsMeta} {bs : List (w8 × Bool)} {off : Nat} {data : List w8}
    {m' : OsMeta} {bs' : List (w8 × Bool)} (h : WReach m bs off data m' bs')
    (hl : bs.length = m.size) {a w : Nat} (hw : 0 < w) (ha : off ≤ a)
    (haw : a + w ≤ off + data.length) (hsz : a + w ≤ bs'.length) :
    (a + w ≤ bs.length ∧ ∀ j < w, bs'[a + j]? = bs[a + j]?) ∨
    (bs'[a]? = some (data.getD (a - off) 0, false) ∧
      ((∃ j < w, a + j < bs.length ∧ bs'[a + j]? = bs[a + j]?) ∨
        ∀ j < w, bs'[a + j]? = some (data.getD (a + j - off) 0, false))) := by
  obtain ⟨K, -, hs, hK⟩ := h.prefix hl
  have hN := h.narrow hl
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
