/-
The pure model of etcd's interval tree (`pkg/v3/adt`), specialized to string-affine intervals
(its only client, the watcher group, uses `StringAffineComparable` intervals). Lean-first (no
Rocq counterpart); see `notes/decisions.md`, "The watchable store: the plan, the interval
tree's contract".

An interval is a pair `(begin, end)` of Go strings, `[begin, end)`, under the affine order
`affCmp` (`StringAffineComparable.Compare`: `""` is +∞). The tree holds a list of entries
(an interval and the `any` value stored with it), sorted by the tree's order `ivlLt` (by begin,
then end), equal intervals allowed, in insertion order among equals (`Insert` descends left when
the new interval is below the node's, right otherwise, so after the equal ones; rotations and the
successor-based delete keep the in-order sequence).
`ivlCmp` is `Interval.Compare` (overlap is `0`), `stab` the entries a query overlaps.
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.adt.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace adt

/-! ## Go's string order -/

theorem strLt_irrefl (a : GoString) : ¬ go.GoStringLt a a := by
  induction a with
  | nil => intro h; cases h
  | cons x xs ih =>
    intro h
    cases h with
    | cons h => exact ih h
    | rel h => exact Int.lt_irrefl _ h

theorem strLt_trans {a b c : GoString} (h1 : go.GoStringLt a b) (h2 : go.GoStringLt b c) :
    go.GoStringLt a c := by
  induction h1 generalizing c with
  | nil => cases h2 <;> exact List.Lex.nil
  | cons h ih =>
    cases h2 with
    | cons h' => exact List.Lex.cons (ih h')
    | rel h' => exact List.Lex.rel h'
  | rel h =>
    cases h2 with
    | cons _ => exact List.Lex.rel h
    | rel h' => exact List.Lex.rel (Int.lt_trans h h')

theorem strLt_asymm {a b : GoString} (h : go.GoStringLt a b) : ¬ go.GoStringLt b a :=
  fun h' => strLt_irrefl a (strLt_trans h h')

/-- Go's `<` on strings is total. -/
theorem strLt_eq_of_not_lt {a b : GoString} (h1 : ¬ go.GoStringLt a b)
    (h2 : ¬ go.GoStringLt b a) : a = b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons y ys => exact absurd List.Lex.nil h1
  | cons x xs ih =>
    cases b with
    | nil => exact absurd List.Lex.nil h2
    | cons y ys =>
      have hxy : x = y := by
        apply BitVec.eq_of_toNat_eq
        have a1 : ¬ (uint.Z x < uint.Z y) := fun h => h1 (List.Lex.rel h)
        have a2 : ¬ (uint.Z y < uint.Z x) := fun h => h2 (List.Lex.rel h)
        simp only [uint.Z] at a1 a2
        omega
      subst hxy
      rw [ih (fun h => h1 (List.Lex.cons h)) (fun h => h2 (List.Lex.cons h))]

/-! ## Intervals -/

/-- A string-affine interval `[begin, end)`: `""` is +∞ (as `End`, unbounded;
`StringAffineComparable.Compare` puts it above every string). -/
abbrev IvlS := GoString × GoString

/-- `StringAffineComparable.Compare` -/
def affCmp (a b : GoString) : Int :=
  if a = go!"" then (if b = go!"" then 0 else 1) else if b = go!"" then -1
  else if go.GoStringLt a b then -1 else if go.GoStringLt b a then 1 else 0

/-- `Interval.Compare` of the query `x` against `y`: `-1` if `x` is left of `y`, `1` if
right, `0` if they overlap. -/
def ivlCmp (x y : IvlS) : Int :=
  if affCmp x.1 y.1 < 0 ∧ affCmp x.2 y.1 ≤ 0 then -1 else if affCmp x.1 y.2 ≥ 0 then 1 else 0

/-- The tree's order on intervals: by begin, then end (`Insert` descends left on it, right
otherwise). -/
def ivlLt (x y : IvlS) : Prop :=
  affCmp x.1 y.1 < 0 ∨ (affCmp x.1 y.1 = 0 ∧ affCmp x.2 y.2 < 0)

instance ivlLt_dec : DecidableRel ivlLt := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

section entries
variable [ext : FfiSyntax]

/-- An entry of the tree: an interval and the value stored with it. -/
abbrev Entry := IvlS × GoInterface

/-- `Insert`: before the first entry it is below (so after the equal ones). -/
def ivtInsert (z : Entry) : List Entry → List Entry
  | [] => [z]
  | w :: ws => if ivlLt z.1 w.1 then z :: w :: ws else w :: ivtInsert z ws

/-- `Stab`/`Visit`: the entries the query overlaps, in the tree's order. -/
def stab (q : IvlS) (L : List Entry) : List Entry :=
  L.filter fun z => decide (ivlCmp q z.1 = 0)

end entries

/-! ## The affine order -/

/-- The strict affine order `affCmp` decides: `""` is the top. -/
def affLt (a b : GoString) : Prop := a ≠ go!"" ∧ (b = go!"" ∨ go.GoStringLt a b)

theorem affCmp_neg_iff (a b : GoString) : affCmp a b < 0 ↔ affLt a b := by
  unfold affCmp affLt
  by_cases ha : a = go!"" <;> by_cases hb : b = go!"" <;> by_cases h1 : go.GoStringLt a b <;>
    by_cases h2 : go.GoStringLt b a <;> simp_all

theorem affCmp_swap (a b : GoString) : affCmp b a = - affCmp a b := by
  unfold affCmp
  by_cases ha : a = go!"" <;> by_cases hb : b = go!"" <;> by_cases h1 : go.GoStringLt a b <;>
    by_cases h2 : go.GoStringLt b a <;> simp_all [strLt_irrefl]
  exact strLt_asymm ‹_› ‹_›

theorem affCmp_eq_zero_iff (a b : GoString) : affCmp a b = 0 ↔ a = b := by
  unfold affCmp
  by_cases ha : a = go!"" <;> by_cases hb : b = go!"" <;> by_cases h1 : go.GoStringLt a b <;>
    by_cases h2 : go.GoStringLt b a <;> simp_all [strLt_irrefl]
  all_goals first | exact strLt_eq_of_not_lt ‹_› ‹_› | (rintro rfl; exact strLt_irrefl _ ‹_›)

theorem affCmp_bounds (a b : GoString) : -1 ≤ affCmp a b ∧ affCmp a b ≤ 1 := by
  unfold affCmp
  by_cases ha : a = go!"" <;> by_cases hb : b = go!"" <;> by_cases h1 : go.GoStringLt a b <;>
    by_cases h2 : go.GoStringLt b a <;> simp_all

@[simp] theorem affCmp_self (a : GoString) : affCmp a a = 0 := (affCmp_eq_zero_iff a a).2 rfl

theorem affLt_irrefl (a : GoString) : ¬ affLt a a := by
  rintro ⟨ha, h | h⟩
  · exact ha h
  · exact strLt_irrefl a h

theorem affLt_trans {a b c : GoString} (h1 : affLt a b) (h2 : affLt b c) : affLt a c := by
  obtain ⟨ha, hab⟩ := h1
  obtain ⟨hb, hbc⟩ := h2
  refine ⟨ha, ?_⟩
  rcases hbc with hc | hbc
  · exact Or.inl hc
  · rcases hab with hb' | hab
    · exact absurd hb' hb
    · exact Or.inr (strLt_trans hab hbc)

/-- The affine order is total. -/
theorem affLt_trichotomy (a b : GoString) : affLt a b ∨ a = b ∨ affLt b a := by
  have := affCmp_swap a b
  by_cases h0 : affCmp a b = 0
  · exact Or.inr (Or.inl ((affCmp_eq_zero_iff a b).1 h0))
  · by_cases hn : affCmp a b < 0
    · exact Or.inl ((affCmp_neg_iff a b).1 hn)
    · exact Or.inr (Or.inr ((affCmp_neg_iff b a).1 (by omega)))

/-- A string is below its proper extensions. -/
theorem strLt_append (a b : GoString) (hb : b ≠ []) : go.GoStringLt a (a ++ b) := by
  induction a with
  | nil =>
    cases b with
    | nil => exact absurd rfl hb
    | cons y ys => exact List.Lex.nil
  | cons x xs ih => exact List.Lex.cons ih

/-- The point query `NewStringAffinePoint key = [key, key ++ "\x00")` is not empty-and-finite:
its begin is `""` (above everything: it overlaps nothing) or below its end. -/
theorem point_ok (key : GoString) : key = go!"" ∨ affLt key (key ++ go!"\x00") := by
  by_cases h : key = go!""
  · exact Or.inl h
  · exact Or.inr ⟨h, Or.inr (strLt_append key _ (by simp))⟩

theorem ivlLt_iff (x y : IvlS) :
    ivlLt x y ↔ affLt x.1 y.1 ∨ (x.1 = y.1 ∧ affLt x.2 y.2) := by
  unfold ivlLt
  rw [affCmp_neg_iff, affCmp_neg_iff, affCmp_eq_zero_iff]

theorem ivlLt_irrefl (x : IvlS) : ¬ ivlLt x x := by
  rw [ivlLt_iff]
  rintro (h | ⟨-, h⟩) <;> exact affLt_irrefl _ h

theorem ivlLt_trans {x y z : IvlS} (h1 : ivlLt x y) (h2 : ivlLt y z) : ivlLt x z := by
  rw [ivlLt_iff] at *
  rcases h1 with h1 | ⟨e1, h1⟩ <;> rcases h2 with h2 | ⟨e2, h2⟩
  · exact Or.inl (affLt_trans h1 h2)
  · exact Or.inl (e2 ▸ h1)
  · exact Or.inl (e1 ▸ h2)
  · exact Or.inr ⟨e1.trans e2, affLt_trans h1 h2⟩

/-- Distinct intervals are ordered one way or the other. -/
theorem ivlLt_trichotomy (x y : IvlS) : ivlLt x y ∨ x = y ∨ ivlLt y x := by
  rw [ivlLt_iff, ivlLt_iff]
  rcases affLt_trichotomy x.1 y.1 with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases affLt_trichotomy x.2 y.2 with h' | h' | h'
    · exact Or.inl (Or.inr ⟨h, h'⟩)
    · exact Or.inr (Or.inl (Prod.ext h h'))
    · exact Or.inr (Or.inr (Or.inr ⟨h.symm, h'⟩))
  · exact Or.inr (Or.inr (Or.inl h))

theorem ivlLt_asymm {x y : IvlS} (h : ivlLt x y) : ¬ ivlLt y x :=
  fun h' => ivlLt_irrefl x (ivlLt_trans h h')

/-- `≤` of the tree's order (as `¬ >`) is transitive. -/
theorem ivlLe_trans {x y z : IvlS} (h1 : ¬ ivlLt y x) (h2 : ¬ ivlLt z y) : ¬ ivlLt z x := by
  intro h
  rcases ivlLt_trichotomy x y with h' | rfl | h'
  · exact h2 (ivlLt_trans h h')
  · exact h2 h
  · exact h1 h'

theorem ivlLt_of_lt_of_le {x y z : IvlS} (h1 : ivlLt x y) (h2 : ¬ ivlLt z y) : ivlLt x z := by
  rcases ivlLt_trichotomy x z with h | rfl | h
  · exact h
  · exact absurd h1 h2
  · exact absurd (ivlLt_trans h h1) h2

theorem ivlLt_of_le_of_lt {x y z : IvlS} (h1 : ¬ ivlLt y x) (h2 : ivlLt y z) : ivlLt x z := by
  rcases ivlLt_trichotomy x z with h | rfl | h
  · exact h
  · exact absurd h2 h1
  · exact absurd (ivlLt_trans h2 h) h1

/-! ## `Insert` -/

section entries
variable [ext : FfiSyntax]

theorem ivtInsert_perm (z : Entry) (L : List Entry) : (ivtInsert z L).Perm (z :: L) := by
  induction L with
  | nil => exact List.Perm.refl _
  | cons w ws ih =>
    unfold ivtInsert
    split
    · exact List.Perm.refl _
    · exact (List.Perm.cons w ih).trans (List.Perm.swap z w ws)

theorem mem_ivtInsert (z x : Entry) (L : List Entry) : x ∈ ivtInsert z L ↔ x = z ∨ x ∈ L := by
  rw [(ivtInsert_perm z L).mem_iff, List.mem_cons]

theorem length_ivtInsert (z : Entry) (L : List Entry) :
    (ivtInsert z L).length = L.length + 1 := by
  rw [(ivtInsert_perm z L).length_eq, List.length_cons]

/-- `Union`'s inserts, one by one: the count grows by the number inserted. -/
theorem length_foldl_ivtInsert (zs L : List Entry) :
    (zs.foldl (fun acc z => ivtInsert z acc) L).length = L.length + zs.length := by
  induction zs generalizing L with
  | nil => rfl
  | cons z zs ih => rw [List.foldl_cons, ih, length_ivtInsert, List.length_cons]; omega

/-- `Insert` keeps the entries sorted (by their intervals, strictly), given that the new
interval is not in the tree. -/
theorem ivtInsert_sorted (z : Entry) (L : List Entry)
    (hs : L.Pairwise fun a b => ivlLt a.1 b.1) (hz : z.1 ∉ L.map Prod.fst) :
    (ivtInsert z L).Pairwise fun a b => ivlLt a.1 b.1 := by
  induction L with
  | nil => exact List.pairwise_singleton _ _
  | cons w ws ih =>
    rw [List.pairwise_cons] at hs
    simp only [List.map_cons, List.mem_cons, not_or] at hz
    unfold ivtInsert
    split
    · rename_i h
      refine List.Pairwise.cons ?_ (List.Pairwise.cons hs.1 hs.2)
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact h
      · exact ivlLt_trans h (hs.1 y hy)
    · rename_i h
      have hwz : ivlLt w.1 z.1 := by
        rcases ivlLt_trichotomy z.1 w.1 with h' | h' | h'
        · exact absurd h' h
        · exact absurd h' hz.1
        · exact h'
      refine List.Pairwise.cons ?_ (ih hs.2 hz.2)
      intro y hy
      rcases (mem_ivtInsert z y ws).1 hy with rfl | hy
      · exact hwz
      · exact hs.1 y hy

end entries

end adt
end EtcdGrove
end Perennial
