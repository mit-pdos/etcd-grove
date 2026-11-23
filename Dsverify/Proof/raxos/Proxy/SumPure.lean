/-
Package `proxy`: pure facts of epoch summaries (`summaryId p` of a permutation `p` of the
replicas): its digits, its length (a command of at least 9 bytes).
-/
module

public import Dsverify.Proof.raxos.Ghost
public import Dsverify.Proof.raxos.Hyp
public import Dsverify.Proof.raxos.Smr.SumId

@[expose] public section

namespace Perennial.raxos

open Perennial.raxos.pure Perennial.raxos.msg

theorem decimal_digit (x : Nat) (h1 : 1 ≤ x) (h5 : x ≤ 5) : decimal x = [W8 (48 + (x : Int))] := by
  simp only [decimal, Nat.toString_eq_ofList_toDigits, String.toUTF8_eq_toByteArray,
    String.toByteArray_ofList]
  rw [Nat.toDigits_of_lt_base (by omega)]
  have : x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl
  · rw [Nat.digitChar_eq_one.2 rfl]; decide +kernel
  · rw [Nat.digitChar_eq_two.2 rfl]; decide +kernel
  · rw [Nat.digitChar_eq_three.2 rfl]; decide +kernel
  · rw [Nat.digitChar_eq_four.2 rfl]; decide +kernel
  · rw [Nat.digitChar_eq_five.2 rfl]; decide +kernel
theorem decimal_small (x : Nat) (h1 : 1 ≤ x) (h5 : x ≤ 5) :
    W8 44 ∉ decimal x ∧ hyp.strconv.smallDigits (decimal x) ∧ hyp.strconv.decVal (decimal x) = x := by
  rw [decimal_digit x h1 h5]
  have : x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 := by omega
  unfold hyp.strconv.smallDigits hyp.strconv.decVal
  rcases this with rfl | rfl | rfl | rfl | rfl <;> simp <;> decide

theorem isPerm_mem (n : Nat) (q : List Nat) (hq : isPerm n q) (x : Nat) :
    x ∈ q ↔ 1 ≤ x ∧ x ≤ n := by
  unfold isPerm at hq
  rw [hq.mem_iff, List.mem_range']; constructor
  · rintro ⟨i, hi, rfl⟩; omega
  · intro h; exact ⟨x - 1, by omega, by omega⟩

theorem isPerm_length (n : Nat) (q : List Nat) (hq : isPerm n q) : q.length = n := by
  unfold isPerm at hq; rw [hq.length_eq]; simp

theorem summaryId_length (p : List Nat) (hp : ∀ x ∈ p, 1 ≤ x ∧ x ≤ 5) :
    (summaryId p).length = 5 + (2 * p.length - 1) := by
  unfold summaryId
  simp only [List.length_append]
  congr 1
  induction p with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil =>
      simp only [List.map_cons, List.map_nil, List.intersperse_singleton, List.flatten_cons,
        List.flatten_nil, List.append_nil, List.length_cons, List.length_nil]
      rw [decimal_digit a (hp a (by simp)).1 (hp a (by simp)).2]; rfl
    | cons b l' =>
      simp only [List.map_cons, List.intersperse_cons_cons, List.flatten_cons, List.length_append]
      have := ih (fun x hx => hp x (List.mem_cons_of_mem _ hx))
      simp only [List.map_cons, List.length_cons] at this
      rw [this, decimal_digit a (hp a (by simp)).1 (hp a (by simp)).2]
      simp; omega

theorem sumPerm_small (p : List Nat) (hp : sumPerm p) : ∀ x ∈ p, 1 ≤ x ∧ x ≤ 5 := by
  intro x hx
  rcases hp with h | h
  · have := (isPerm_mem 3 p h x).1 hx; omega
  · have := (isPerm_mem 5 p h x).1 hx; omega

theorem sumPerm_length (p : List Nat) (hp : sumPerm p) : 3 ≤ p.length ∧ p.length ≤ 5 := by
  rcases hp with h | h <;> rw [isPerm_length _ _ h] <;> omega

/-- A summary is a command of at least 9 bytes. -/
theorem summaryId_cmdOk (p : List Nat) (hp : sumPerm p) : cmdOk (summaryId p) := by
  unfold cmdOk
  rw [summaryId_length p (sumPerm_small p hp)]
  have := sumPerm_length p hp
  simp [keyLen]; omega

set_option linter.deprecated false in
theorem varint_length_le (k : Nat) : ∀ v, v < 128 ^ (k + 1) → (varint v).length ≤ k + 1 := by
  induction k with
  | zero => intro v hv; unfold varint; simp at hv; simp [hv]
  | succ k ih =>
    intro v hv
    unfold varint
    split
    · simp
    · simp only [List.length_cons]
      have := ih (v / 128) (by rw [Nat.pow_succ] at hv; omega)
      omega
theorem ascii_strOk' (s : GoString) (h : asciiOk s) : strOk s := by
  unfold strOk
  induction s with
  | nil => rfl
  | cons c rest ih =>
    have hc : c.toNat < 128 := h c (by simp)
    have hr : asciiOk rest := fun b hb => h b (by simp [hb])
    unfold validUtf8
    simp only [show c.toNat < 0x80 from hc, ↓reduceIte]
    exact ih hr
theorem fBytes_length (n : Nat) (b : List w8) (hn : n < 16) (hb : b.length < 128) :
    (fBytes n b).length ≤ 2 + b.length := by
  unfold fBytes tag
  rw [List.length_append, List.length_append]
  have h1 := varint_length_le 0 (n * 8 + 2) (by omega)
  have h2 := varint_length_le 0 b.length (by omega)
  omega
theorem summary_batchFit (p : List Nat) (hp : sumPerm p) :
    batchFit ⟨summaryId p, -1, [summaryId p]⟩ := by
  have hl := summaryId_length p (sumPerm_small p hp)
  have hpl := sumPerm_length p hp
  have hx : (summaryId p).length < 20 := by omega
  have hne : summaryId p ≠ [] := by intro h; rw [h] at hl; simp at hl; omega
  have hs := ascii_strOk' _ (sumid.summaryId_ascii p)
  refine ⟨⟨⟨by show (-2 ^ 63 : Int) ≤ -1; decide, by show (-1 : Int) < 2 ^ 63; decide⟩, hs,
    by simpa using hs⟩, ?_⟩
  unfold encBatch encSingle fStr fVarint
  simp only [hne, ↓reduceIte, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.length_append]
  have h1 : (tag 1 0).length ≤ 1 := varint_length_le 0 _ (by omega)
  have h2 := varint_length_le 9 (u64 (-1)) (by unfold u64; decide)
  have h3 := fBytes_length 1 (summaryId p) (by omega) (by omega)
  have h4 := fBytes_length 2 (fBytes 1 (summaryId p)) (by omega) (by omega)
  have h5 := fBytes_length 3 (summaryId p) (by omega) (by omega)
  have h6 : (if (-1 : Int) = 0 then [] else tag 1 0 ++ varint (u64 (-1))).length ≤ 11 := by
    rw [if_neg (by decide)]; simp only [List.length_append]; omega
  omega

end Perennial.raxos
