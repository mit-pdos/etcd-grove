/-
**Prefix ranges** (pure): `prefixRangeEnd p`'s decomposition and `inRange p (prefixRangeEnd p)`
as the keys with the prefix `p` (`inRange_prefix`). Moved from `concurrency/InvMutexLemmas.lean`
(K2e-7d: the watch's completeness uses them too). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvOp
public import Proof.go_etcd_io.etcd.cache.v3.InvEtcd

@[expose] public section

set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

/-! ## Prefix ranges -/

theorem goStringLt_cons_iff (x y : w8) (xs ys : GoString) :
    go.GoStringLt (x :: xs) (y :: ys) ↔ uint.Z x < uint.Z y ∨ (x = y ∧ go.GoStringLt xs ys) := by
  constructor
  · intro h; cases h with
    | cons h => exact Or.inr ⟨rfl, h⟩
    | rel h => exact Or.inl h
  · rintro (h | ⟨rfl, h⟩)
    · exact List.Lex.rel h
    · exact List.Lex.cons h

theorem goStringLt_nil_cons (x : w8) (xs : GoString) : go.GoStringLt [] (x :: xs) := List.Lex.nil

theorem goStringLt_not_nil (k : GoString) : ¬ go.GoStringLt k [] := by intro h; cases h

theorem w8_eq_of_Z {x y : w8} (h1 : ¬ uint.Z x < uint.Z y) (h2 : ¬ uint.Z y < uint.Z x) : x = y := by
  apply BitVec.eq_of_toNat_eq
  simp only [uint.Z] at h1 h2
  omega

theorem w8_lt_ff (d : w8) (h : d ≠ W8 255) : uint.Z d < uint.Z (W8 255) := by
  word

theorem w8_succ (b : w8) (h : b ≠ W8 255) : uint.Z (b + W8 1) = uint.Z b + 1 := by
  word

theorem ff_not_lt_iff (fs k : GoString) (hfs : ∀ x ∈ fs, x = W8 255) :
    ¬ go.GoStringLt k fs ↔ fs <+: k := by
  induction fs generalizing k with
  | nil => simp [goStringLt_not_nil]
  | cons f fs ih =>
    have hf : f = W8 255 := hfs f (by simp)
    have hfs' : ∀ x ∈ fs, x = W8 255 := fun x hx => hfs x (List.mem_cons_of_mem _ hx)
    subst hf
    cases k with
    | nil => simp [goStringLt_nil_cons]
    | cons d k' =>
      rw [goStringLt_cons_iff, List.cons_prefix_cons, ← ih k' hfs']
      by_cases hd : d = W8 255
      · subst hd; simp
      · have := w8_lt_ff d hd
        exact ⟨fun h => absurd (Or.inl this) h, fun ⟨h, _⟩ => absurd h.symm hd⟩

/-- The decomposition of a prefix by `prefixRangeEnd`. -/
theorem prefixRangeEnd_cases (p : GoString) :
    (prefixRangeEnd p = [W8 0] ∧ ∀ x ∈ p, x = W8 255) ∨
    ∃ q b fs, p = q ++ b :: fs ∧ b ≠ W8 255 ∧ (∀ x ∈ fs, x = W8 255) ∧
      prefixRangeEnd p = q ++ [b + W8 1] := by
  have hsplit := List.takeWhile_append_dropWhile (p := fun b => b == W8 255) (l := p.reverse)
  unfold prefixRangeEnd
  generalize ht : p.reverse.takeWhile (fun b => b == W8 255) = t at hsplit
  have htff : ∀ x ∈ t, x = W8 255 := by
    intro x hx
    have := List.all_takeWhile (p := fun b => b == W8 255) (l := p.reverse)
    rw [ht, List.all_eq_true] at this
    simpa using this x hx
  generalize hd : p.reverse.dropWhile (fun b => b == W8 255) = d at hsplit
  cases d with
  | nil =>
    left; refine ⟨rfl, fun x hx => ?_⟩
    rw [← List.mem_reverse, ← hsplit] at hx; simpa using htff x (by simpa using hx)
  | cons b r =>
    right
    refine ⟨r.reverse, b, t.reverse, ?_, ?_, fun x hx => htff x (List.mem_reverse.1 hx), rfl⟩
    · rw [← List.reverse_reverse p, ← hsplit]; simp
    · have := List.head_dropWhile_not (fun b => b == W8 255) (l := p.reverse) (by rw [hd]; simp)
      simp only [hd, List.head_cons] at this; simpa using this

theorem prefix_lt_iff_aux (q : GoString) (b : w8) (fs k : GoString) (hb : b ≠ W8 255)
    (hfs : ∀ x ∈ fs, x = W8 255) :
    (¬ go.GoStringLt k (q ++ b :: fs) ∧ go.GoStringLt k (q ++ [b + W8 1])) ↔
      (q ++ b :: fs) <+: k := by
  induction q generalizing k with
  | nil =>
    cases k with
    | nil => simp [goStringLt_nil_cons]
    | cons d k' =>
      simp only [List.nil_append, goStringLt_cons_iff, List.cons_prefix_cons, goStringLt_not_nil,
        and_false, or_false]
      rw [← ff_not_lt_iff fs k' hfs]
      have hs := w8_succ b hb
      constructor
      · rintro ⟨h1, h2⟩
        have hdb : d = b := by
          apply w8_eq_of_Z
          · intro h; exact h1 (Or.inl h)
          · intro h; rw [hs] at h2; omega
        subst hdb
        exact ⟨rfl, fun h => h1 (Or.inr ⟨rfl, h⟩)⟩
      · rintro ⟨rfl, h⟩
        refine ⟨?_, by rw [hs]; omega⟩
        rintro (h' | ⟨-, h'⟩)
        · omega
        · exact h h'
  | cons c q ih =>
    cases k with
    | nil => simp [goStringLt_nil_cons]
    | cons d k' =>
      simp only [List.cons_append, goStringLt_cons_iff, List.cons_prefix_cons]
      rw [← ih k']
      constructor
      · rintro ⟨h1, h2⟩
        have hdc : d = c := by
          apply w8_eq_of_Z
          · intro h; exact h1 (Or.inl h)
          · intro h; rcases h2 with h2 | ⟨rfl, -⟩ <;> omega
        subst hdc
        refine ⟨rfl, fun h => h1 (Or.inr ⟨rfl, h⟩), ?_⟩
        rcases h2 with h2 | ⟨-, h2⟩
        · omega
        · exact h2
      · rintro ⟨rfl, h1, h2⟩
        refine ⟨?_, Or.inr ⟨rfl, h2⟩⟩
        rintro (h | ⟨-, h⟩)
        · omega
        · exact h1 h

/-- A key is in a non-empty prefix's range (`WithPrefix`) exactly when it has the prefix. -/
theorem inRange_prefix (p k : GoString) (hp : p ≠ []) :
    inRange p (prefixRangeEnd p) k = true ↔ p <+: k := by
  rcases prefixRangeEnd_cases p with ⟨he, hall⟩ | ⟨q, b, fs, rfl, hb, hfs, he⟩
  · rw [he]; simp [inRange]
    exact ff_not_lt_iff p k hall
  · rw [he]
    have hne : q ++ [b + W8 1] ≠ [] := by simp
    have hne0 : q ++ [b + W8 1] ≠ [W8 0] := by
      intro h
      cases q with
      | nil =>
        simp at h
        exact hb (by word)
      | cons c q => simp at h
    simp only [inRange, hne, hne0, ite_false, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not, decide_eq_true_eq]
    exact prefix_lt_iff_aux q b fs k hb hfs

theorem keyRangeUnder_prefix (p : GoString) (hp : p ≠ []) :
    KeyRangeUnder p p (prefixRangeEnd p) :=
  fun k hk => (inRange_prefix p k hp).1 hk

theorem keyRangeUnder_key (pfx key : GoString) (h : pfx <+: key) : KeyRangeUnder pfx key [] := by
  intro k hk
  simp [inRange] at hk
  subst hk; exact h

theorem prefixRangeEnd_ne_nil (p : GoString) : prefixRangeEnd p ≠ [] := by
  unfold prefixRangeEnd; split <;> simp

end concurrency
end EtcdGrove
end Perennial
