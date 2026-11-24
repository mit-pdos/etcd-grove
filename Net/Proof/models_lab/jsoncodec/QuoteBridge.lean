/-
Bridges between the encoders' functions (`Quote.lean`, #24 J2 batch 2a: `decNat`, `jsonQuote`) and
the scanner's (`Scan/Lits.lean`: `JsonScan.decN`, `JsonScan.plainEnc`), which the decoders' and
the kits' proofs state their bytes in: `decNat_decN` (the same digits) and `jsonQuote_plain` (a
string of plain bytes is written as it is, in quotes). Local to dsv-vr (round 9), until zeldovich's
batch 2b lands its own (`jsonQuote_plain` in `Quote.lean`); then these go. Pure.
-/
module

public import Net.Proof.models_lab.jsoncodec.Quote
public import Net.Proof.models_lab.jsoncodec.Scan.Lits

@[expose] public section

namespace Perennial

namespace models_lab.jsoncodec

theorem w8_natCast (k : Nat) : W8 ((k : Nat) : Int) = BitVec.ofNat 8 k := by
  apply BitVec.eq_of_toNat_eq
  simp [W8]

/-- `AppendUint`'s digits are the scanner's. -/
theorem decNat_decN (n : Nat) : decNat n = JsonScan.decN n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [decNat, JsonScan.decN]
    by_cases h : n < 10
    · simp only [h, ↓reduceIte, w8_natCast]
    · simp only [h, ↓reduceIte, w8_natCast]
      rw [ih (n / 10) (by omega)]

theorem decU64_decN (x : w64) : decU64 x = JsonScan.decN (uint.nat x) := by
  unfold decU64; rw [decNat_decN]

/-- `appendEscapedASCII` writes a plain byte as it is. -/
theorem escASCII_plain (c : w8) (h : JsonScan.plainEnc c) : escASCII c = [c] := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  have ne : ∀ k : Int, 0 ≤ k → k < 256 → c.toNat ≠ k.toNat → c ≠ W8 k := by
    intro k hk0 hk hne heq
    apply hne
    rw [heq]
    simp only [W8, BitVec.toNat_ofInt]
    omega
  unfold escASCII htmlB
  rw [if_neg (by
      rintro (e | e)
      · exact ne 34 (by omega) (by omega) (by simpa using h3) e
      · exact ne 92 (by omega) (by omega) (by simpa using h4) e),
    if_neg (ne 8 (by omega) (by omega) (by simp; omega)),
    if_neg (ne 12 (by omega) (by omega) (by simp; omega)),
    if_neg (ne 10 (by omega) (by omega) (by simp; omega)),
    if_neg (ne 13 (by omega) (by omega) (by simp; omega)),
    if_neg (ne 9 (by omega) (by omega) (by simp; omega)), if_neg]
  rintro (e | e)
  · omega
  · simp only [decide_eq_true_eq] at e
    rcases e with e | e | e
    · exact ne 60 (by omega) (by omega) (by simpa using h5) e
    · exact ne 62 (by omega) (by omega) (by simpa using h6) e
    · exact ne 38 (by omega) (by omega) (by simpa using h7) e

theorem quoteFrom_plain (s : List w8) (h : ∀ c ∈ s, JsonScan.plainEnc c) :
    ∀ i, quoteFrom s i = s.drop i := by
  intro i
  induction h' : s.length - i generalizing i with
  | zero =>
    rw [quoteFrom_end s i (by omega), List.drop_eq_nil_of_le (by omega)]
  | succ n ih =>
    have hi : i < s.length := by omega
    have hc : s.getD i (W8 0) = s[i] := by simp [List.getD_eq_getElem?_getD, hi]
    have hp := h s[i] (List.getElem_mem hi)
    rw [quoteFrom_ascii s i hi (by rw [hc]; obtain ⟨_, h2, _⟩ := hp; omega), hc,
      escASCII_plain _ hp, ih (i + 1) (by omega)]
    rw [List.drop_eq_getElem_cons hi, List.singleton_append]

/-- `AppendString` writes a string of plain bytes as it is, in quotes. -/
theorem jsonQuote_plain (s : List w8) (h : ∀ c ∈ s, JsonScan.plainEnc c) :
    jsonQuote s = 34#8 :: (s ++ [34#8]) := by
  unfold jsonQuote
  rw [quoteFrom_plain s h 0]
  simp

end models_lab.jsoncodec
end Perennial
