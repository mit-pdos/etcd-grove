/-
The pure model of the interval tree's red-black tree (`pkg/v3/adt`): the tree as an inductive
(`RbT`: the sentinel is the leaf), its in-order list, the red-black invariant (`RbOk`), the
subtrees' `max` augmentation (`RbT.maxEnd`, `nodeMax`), the rotations, and the reads' descents
as pure functions mirroring the Go code (`findE`, `intersects`, `visitL`) with their
correctness over the in-order list (`findE_some`/`findE_none`, `intersects_iff`, `visit_stab`). Lean-first; see
`notes/decisions.md`, "The watchable store: the plan, the interval tree's contract".
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.adt.Model

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace adt

/-! ## The tree -/

/-- A node's colour (`rbcolor`: `black` is `0`, `red` is `1`). -/
inductive RbColor where
  | red
  | black
  deriving DecidableEq

/-- The tree: a leaf (the sentinel), or a node with its colour, its children and its entry. -/
inductive RbT (E : Type) where
  | leaf : RbT E
  | node (c : RbColor) (l : RbT E) (e : E) (r : RbT E) : RbT E

namespace RbT
variable {E : Type}

/-- The entries in order (left subtree, the node, right subtree). -/
def inorder : RbT E → List E
  | leaf => []
  | node _ l e r => l.inorder ++ e :: r.inorder

@[simp] theorem inorder_leaf : (leaf : RbT E).inorder = [] := rfl
@[simp] theorem inorder_node (c : RbColor) (l : RbT E) (e : E) (r : RbT E) :
    (node c l e r).inorder = l.inorder ++ e :: r.inorder := rfl

/-- The colour (`color(sentinel)`: the sentinel is black). -/
def color : RbT E → RbColor
  | leaf => .black
  | node c _ _ _ => c

/-- `some h` when every path from the root to a leaf has `h` black nodes. -/
def blackHeight : RbT E → Option Nat
  | leaf => some 0
  | node c l _ r =>
    match l.blackHeight, r.blackHeight with
    | some a, some b => if a = b then some (a + if c = .black then 1 else 0) else none
    | _, _ => none

/-- A red node has black children (the sentinel is black). -/
def redOk : RbT E → Prop
  | leaf => True
  | node c l _ r => (c = .red → l.color = .black ∧ r.color = .black) ∧ l.redOk ∧ r.redOk

/-- `rotateLeft(x)`: `x`'s right child takes its place (no change without one); the colours
stay with their nodes. -/
def rotateLeft : RbT E → RbT E
  | node cx a x (node cy b y d) => node cy (node cx a x b) y d
  | t => t

/-- `rotateRight(x)`: `x`'s left child takes its place (no change without one). -/
def rotateRight : RbT E → RbT E
  | node cy (node cx a x b) y d => node cx a x (node cy b y d)
  | t => t

theorem inorder_rotateLeft (t : RbT E) : t.rotateLeft.inorder = t.inorder := by
  unfold rotateLeft
  split <;> simp

theorem inorder_rotateRight (t : RbT E) : t.rotateRight.inorder = t.inorder := by
  unfold rotateRight
  split <;> simp

/-- The number of nodes. -/
theorem length_inorder_node (c : RbColor) (l : RbT E) (e : E) (r : RbT E) :
    (node c l e r).inorder.length = l.inorder.length + r.inorder.length + 1 := by
  simp; omega

end RbT

/-! ## The affine order, more -/

theorem affCmp_pos_iff (a b : GoString) : affCmp a b > 0 ↔ affLt b a := by
  rw [← affCmp_neg_iff, affCmp_swap a b]; omega

theorem affCmp_nonpos_iff (a b : GoString) : affCmp a b ≤ 0 ↔ ¬ affLt b a := by
  rw [← affCmp_pos_iff]; omega

theorem affCmp_nonneg_iff (a b : GoString) : affCmp a b ≥ 0 ↔ ¬ affLt a b := by
  rw [← affCmp_neg_iff]; omega

theorem affLt_asymm {a b : GoString} (h : affLt a b) : ¬ affLt b a :=
  fun h' => affLt_irrefl a (affLt_trans h h')

/-- `≤` (as `¬ >`) is transitive. -/
theorem affLe_trans {a b c : GoString} (h1 : ¬ affLt b a) (h2 : ¬ affLt c b) : ¬ affLt c a := by
  intro h
  rcases affLt_trichotomy a b with h' | rfl | h'
  · exact h2 (affLt_trans h h')
  · exact h2 h
  · exact h1 h'

theorem affLt_of_lt_of_le {a b c : GoString} (h1 : affLt a b) (h2 : ¬ affLt c b) : affLt a c := by
  rcases affLt_trichotomy a c with h | rfl | h
  · exact h
  · exact absurd h1 h2
  · exact absurd (affLt_trans h h1) h2

theorem affLt_of_le_of_lt {a b c : GoString} (h1 : ¬ affLt b a) (h2 : affLt b c) : affLt a c := by
  rcases affLt_trichotomy a c with h | rfl | h
  · exact h
  · exact absurd h2 h1
  · exact absurd (affLt_trans h2 h) h1

theorem not_affLt_empty (a : GoString) : ¬ affLt go!"" a := fun h => h.1 rfl

/-- The tree's order puts the begins in order. -/
theorem ivlLt_begin_le {x y : IvlS} (h : ivlLt x y) : ¬ affLt y.1 x.1 := by
  rw [ivlLt_iff] at h
  rcases h with h | ⟨h, -⟩
  · exact affLt_asymm h
  · rw [h]; exact affLt_irrefl _

theorem ivlLt_ne {x y : IvlS} (h : ivlLt x y) : x ≠ y := by
  rintro rfl; exact ivlLt_irrefl x h

/-- `≤` of the tree's order (as `¬ >`) puts the begins in order. -/
theorem ivlLe_begin_le {x y : IvlS} (h : ¬ ivlLt y x) : ¬ affLt y.1 x.1 :=
  fun h' => h ((ivlLt_iff y x).2 (Or.inl h'))

/-! ## Overlap -/

/-- `Interval.Compare`'s `0`: the query `x` overlaps `y`. -/
theorem ivlCmp_eq_zero_iff (x y : IvlS) :
    ivlCmp x y = 0 ↔ (affLt x.1 y.1 → affLt y.1 x.2) ∧ affLt x.1 y.2 := by
  simp only [← affCmp_neg_iff]
  have := affCmp_swap y.1 x.2
  unfold ivlCmp
  split <;> (try split) <;> omega

theorem ivlCmp_neg_iff (x y : IvlS) : ivlCmp x y < 0 ↔ affLt x.1 y.1 ∧ ¬ affLt y.1 x.2 := by
  simp only [← affCmp_neg_iff]
  have := affCmp_swap y.1 x.2
  unfold ivlCmp
  split <;> (try split) <;> omega

theorem ivlCmp_pos_iff (x y : IvlS) :
    ivlCmp x y > 0 ↔ ¬ (affLt x.1 y.1 ∧ ¬ affLt y.1 x.2) ∧ ¬ affLt x.1 y.2 := by
  simp only [← affCmp_neg_iff]
  have := affCmp_swap y.1 x.2
  unfold ivlCmp
  split <;> (try split) <;> omega

/-- An interval ending at or before the query's begin does not overlap it. -/
theorem no_ovl_of_end_le {q z : IvlS} (h : ¬ affLt q.1 z.2) : ivlCmp q z ≠ 0 :=
  fun h0 => h ((ivlCmp_eq_zero_iff q z).1 h0).2

/-- An interval beginning after the query's begin, at or after its end, does not overlap it. -/
theorem no_ovl_of_left {q z : IvlS} (h1 : affLt q.1 z.1) (h2 : ¬ affLt z.1 q.2) :
    ivlCmp q z ≠ 0 :=
  fun h0 => h2 (((ivlCmp_eq_zero_iff q z).1 h0).1 h1)

section entries
variable [ext : FfiSyntax]
set_option linter.unusedSectionVars false

theorem stab_append (q : IvlS) (A B : List Entry) : stab q (A ++ B) = stab q A ++ stab q B := by
  simp [stab, List.filter_append]

theorem stab_cons (q : IvlS) (z : Entry) (B : List Entry) :
    stab q (z :: B) = if ivlCmp q z.1 = 0 then z :: stab q B else stab q B := by
  unfold stab; rw [List.filter_cons]; by_cases h : ivlCmp q z.1 = 0 <;> simp [h]

theorem stab_eq_nil_iff (q : IvlS) (A : List Entry) :
    stab q A = [] ↔ ∀ z ∈ A, ivlCmp q z.1 ≠ 0 := by
  unfold stab; rw [List.filter_eq_nil_iff]; simp

/-! ## Sorted trees -/

/-- Entries sorted by the tree's order, non-strictly: equal intervals are allowed (`Insert`
puts a new one after the equal ones), none is above a later one. -/
def IvSorted (L : List Entry) : Prop := L.Pairwise fun a b => ¬ ivlLt b.1 a.1

theorem ivSorted_node {c : RbColor} {l : RbT Entry} {e : Entry} {r : RbT Entry}
    (h : IvSorted (RbT.node c l e r).inorder) :
    IvSorted l.inorder ∧ IvSorted r.inorder ∧ (∀ z ∈ l.inorder, ¬ ivlLt e.1 z.1) ∧
      (∀ z ∈ r.inorder, ¬ ivlLt z.1 e.1) := by
  unfold IvSorted at *
  rw [RbT.inorder_node, List.pairwise_append, List.pairwise_cons] at h
  obtain ⟨hl, ⟨he, hr⟩, hlr⟩ := h
  exact ⟨hl, hr, fun z hz => hlr z hz e List.mem_cons_self, he⟩

/-- `Insert` keeps the entries sorted (equal intervals allowed: no premise). -/
theorem ivtInsert_ivSorted (z : Entry) (L : List Entry) (hs : IvSorted L) :
    IvSorted (ivtInsert z L) := by
  unfold IvSorted at *
  induction L with
  | nil => exact List.pairwise_singleton _ _
  | cons w ws ih =>
    rw [List.pairwise_cons] at hs
    unfold ivtInsert
    split
    · rename_i h
      refine List.Pairwise.cons ?_ (List.Pairwise.cons hs.1 hs.2)
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact ivlLt_asymm h
      · exact ivlLt_asymm (ivlLt_of_lt_of_le h (hs.1 y hy))
    · rename_i h
      refine List.Pairwise.cons ?_ (ih hs.2)
      intro y hy
      rcases (mem_ivtInsert z y ws).1 hy with rfl | hy
      · exact h
      · exact hs.1 y hy

/-- Strictly sorted entries are sorted. -/
theorem ivSorted_of_strict (L : List Entry) (h : L.Pairwise fun a b => ivlLt a.1 b.1) :
    IvSorted L :=
  h.imp ivlLt_asymm

/-! ## The `max` augmentation -/

/-- `updateMax`'s step: the larger of `m` and the child's max (if any), under `affCmp`. -/
def affMaxO (m : GoString) : Option GoString → GoString
  | none => m
  | some x => if affCmp x m > 0 then x else m

/-- The largest end of a subtree's entries; `none` for the leaf. -/
def RbT.maxEnd : RbT Entry → Option GoString
  | .leaf => none
  | .node _ l e r => some (affMaxO (affMaxO e.1.2 l.maxEnd) r.maxEnd)

/-- A node's `max` field: its end, then its children's max (as `updateMax` computes it). -/
def nodeMax (l : RbT Entry) (e : Entry) (r : RbT Entry) : GoString :=
  affMaxO (affMaxO e.1.2 l.maxEnd) r.maxEnd

@[simp] theorem maxEnd_leaf : (RbT.leaf : RbT Entry).maxEnd = none := rfl
@[simp] theorem maxEnd_node (c : RbColor) (l : RbT Entry) (e : Entry) (r : RbT Entry) :
    (RbT.node c l e r).maxEnd = some (nodeMax l e r) := rfl

theorem affMaxO_ge (m : GoString) (o : Option GoString) : ¬ affLt (affMaxO m o) m := by
  cases o with
  | none => exact affLt_irrefl m
  | some x =>
    simp only [affMaxO]
    split
    · rename_i h; exact affLt_asymm ((affCmp_pos_iff x m).1 h)
    · exact affLt_irrefl m

theorem affMaxO_ge_some (m x : GoString) : ¬ affLt (affMaxO m (some x)) x := by
  simp only [affMaxO]
  split
  · exact affLt_irrefl x
  · rename_i h; rw [affCmp_pos_iff] at h; exact h

theorem affMaxO_cases (m : GoString) (o : Option GoString) :
    affMaxO m o = m ∨ some (affMaxO m o) = o := by
  cases o with
  | none => exact Or.inl rfl
  | some x => simp only [affMaxO]; split <;> simp

/-- A subtree's max is at least every end in it. -/
theorem maxEnd_ge : ∀ (t : RbT Entry) (m : GoString), t.maxEnd = some m →
    ∀ z ∈ t.inorder, ¬ affLt m z.1.2
  | .leaf, _, h, _, _ => by cases h
  | .node c l e r, m, h, z, hz => by
    simp only [maxEnd_node, Option.some.injEq] at h
    subst h
    have h1 : ¬ affLt (nodeMax l e r) (affMaxO e.1.2 l.maxEnd) := affMaxO_ge _ _
    have h2 : ¬ affLt (affMaxO e.1.2 l.maxEnd) e.1.2 := affMaxO_ge _ _
    simp only [RbT.inorder_node, List.mem_append, List.mem_cons] at hz
    rcases hz with hz | rfl | hz
    · cases hl : l.maxEnd with
      | none => cases l with
        | leaf => simp at hz
        | node _ _ _ _ => simp at hl
      | some ml =>
        have h3 : ¬ affLt (affMaxO e.1.2 l.maxEnd) ml := by rw [hl]; exact affMaxO_ge_some _ _
        exact affLe_trans (affLe_trans (maxEnd_ge l ml hl z hz) h3) h1
    · exact affLe_trans h2 h1
    · cases hr : r.maxEnd with
      | none => cases r with
        | leaf => simp at hz
        | node _ _ _ _ => simp at hr
      | some mr =>
        have h3 : ¬ affLt (nodeMax l e r) mr := by
          unfold nodeMax; rw [hr]; exact affMaxO_ge_some _ _
        exact affLe_trans (maxEnd_ge r mr hr z hz) h3

/-- A subtree's max is an end in it. -/
theorem maxEnd_mem : ∀ (t : RbT Entry) (m : GoString), t.maxEnd = some m →
    ∃ z ∈ t.inorder, z.1.2 = m
  | .leaf, _, h => by cases h
  | .node c l e r, m, h => by
    simp only [maxEnd_node, Option.some.injEq] at h
    subst h
    unfold nodeMax
    rcases affMaxO_cases (affMaxO e.1.2 l.maxEnd) r.maxEnd with h | h
    · rw [h]
      rcases affMaxO_cases e.1.2 l.maxEnd with h' | h'
      · rw [h']; exact ⟨e, by simp, rfl⟩
      · obtain ⟨z, hz, hz'⟩ := maxEnd_mem l _ h'.symm
        exact ⟨z, by simp [hz], hz'⟩
    · obtain ⟨z, hz, hz'⟩ := maxEnd_mem r _ h.symm
      exact ⟨z, by simp [hz], hz'⟩

/-! ## `find` -/

/-- `find`'s descent: by begin, then end; the entry with exactly the interval `k`. -/
def RbT.findE (k : IvlS) : RbT Entry → Option Entry
  | .leaf => none
  | .node _ l e r =>
    if affCmp k.1 e.1.1 = 0 ∧ affCmp k.2 e.1.2 = 0 then some e
    else if affCmp k.1 e.1.1 < 0 then l.findE k
    else if affCmp k.1 e.1.1 = 0 then (if affCmp k.2 e.1.2 < 0 then l.findE k else r.findE k)
    else r.findE k

/-- `find`'s step at a node: the node's interval, or below it and on to the left, or above it
and on to the right. -/
theorem findE_node (k : IvlS) (c : RbColor) (l : RbT Entry) (e : Entry) (r : RbT Entry) :
    (k = e.1 ∧ (RbT.node c l e r).findE k = some e) ∨
    (ivlLt k e.1 ∧ (RbT.node c l e r).findE k = l.findE k) ∨
    (ivlLt e.1 k ∧ (RbT.node c l e r).findE k = r.findE k) := by
  have hsw1 := affCmp_swap k.1 e.1.1
  have hsw2 := affCmp_swap k.2 e.1.2
  simp only [RbT.findE]
  unfold ivlLt
  by_cases h1 : affCmp k.1 e.1.1 = 0 ∧ affCmp k.2 e.1.2 = 0
  · exact Or.inl ⟨Prod.ext ((affCmp_eq_zero_iff _ _).1 h1.1) ((affCmp_eq_zero_iff _ _).1 h1.2),
      ite_eq_left_of_eq_true _ _ (eq_true h1)⟩
  rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
  by_cases h2 : affCmp k.1 e.1.1 < 0
  · exact Or.inr (Or.inl ⟨Or.inl h2, ite_eq_left_of_eq_true _ _ (eq_true h2)⟩)
  rw [ite_eq_right_of_eq_false _ _ (eq_false h2)]
  by_cases h3 : affCmp k.1 e.1.1 = 0
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h3)]
    by_cases h4 : affCmp k.2 e.1.2 < 0
    · exact Or.inr (Or.inl ⟨Or.inr ⟨h3, h4⟩, ite_eq_left_of_eq_true _ _ (eq_true h4)⟩)
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h4)]
      have : affCmp k.2 e.1.2 ≠ 0 := fun h => h1 ⟨h3, h⟩
      exact Or.inr (Or.inr ⟨Or.inr ⟨by omega, by omega⟩, rfl⟩)
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h3)]
    exact Or.inr (Or.inr ⟨Or.inl (by omega), rfl⟩)

/-- **What `find` finds is an entry with the interval** (with equal intervals, the topmost on
the descent's path, not necessarily the first in order). -/
theorem findE_some (k : IvlS) : ∀ (t : RbT Entry) (z : Entry), t.findE k = some z →
    z ∈ t.inorder ∧ z.1 = k
  | .leaf, _, h => by cases h
  | .node c l e r, z, h => by
    rcases findE_node k c l e r with ⟨hk, he⟩ | ⟨-, he⟩ | ⟨-, he⟩ <;> rw [he] at h
    · obtain rfl := Option.some.inj h
      exact ⟨by simp, hk.symm⟩
    · obtain ⟨h1, h2⟩ := findE_some k l z h
      exact ⟨by simp [h1], h2⟩
    · obtain ⟨h1, h2⟩ := findE_some k r z h
      exact ⟨by simp [h1], h2⟩

/-- **`find` finds an entry whenever there is one with the interval**, in a sorted tree. -/
theorem findE_none (k : IvlS) : ∀ (t : RbT Entry), IvSorted t.inorder → t.findE k = none →
    k ∉ t.inorder.map Prod.fst
  | .leaf, _, _ => by simp
  | .node c l e r, hs, h => by
    obtain ⟨hl, hr, hle, her⟩ := ivSorted_node hs
    intro hk
    rw [RbT.inorder_node, List.map_append, List.mem_append, List.map_cons, List.mem_cons] at hk
    rcases findE_node k c l e r with ⟨-, he⟩ | ⟨hlt, he⟩ | ⟨hgt, he⟩ <;> rw [he] at h
    · cases h
    · rcases hk with hk | hk | hk
      · exact findE_none k l hl h hk
      · exact ivlLt_ne hlt hk
      · obtain ⟨z, hz, hzk⟩ := List.mem_map.1 hk
        rw [← hzk] at hlt
        exact her z hz hlt
    · rcases hk with hk | hk | hk
      · obtain ⟨z, hz, hzk⟩ := List.mem_map.1 hk
        rw [← hzk] at hgt
        exact hle z hz hgt
      · exact ivlLt_ne hgt hk.symm
      · exact findE_none k r hr h hk

/-! ## `Intersects` -/

/-- `Intersects`'s descent: stop at an overlapping node; else left when the left subtree's max
is above the query's begin, right otherwise. -/
def RbT.intersects (q : IvlS) : RbT Entry → Bool
  | .leaf => false
  | .node _ l e r =>
    if ivlCmp q e.1 = 0 then true
    else match l.maxEnd with
      | some m => if affCmp m q.1 > 0 then l.intersects q else r.intersects q
      | none => r.intersects q

/-- **`Intersects` decides whether an entry overlaps the query**, in a sorted tree with exact
`max`es (by construction: `nodeMax`). -/
theorem intersects_iff (q : IvlS) : ∀ (t : RbT Entry), IvSorted t.inorder →
    (t.intersects q = true ↔ stab q t.inorder ≠ [])
  | .leaf, _ => by simp [RbT.intersects, stab]
  | .node c l e r, hs => by
    obtain ⟨hl, hr, hle, her⟩ := ivSorted_node hs
    have ihl := intersects_iff q l hl
    have ihr := intersects_iff q r hr
    unfold RbT.intersects
    rw [RbT.inorder_node, stab_append, stab_cons]
    by_cases h0 : ivlCmp q e.1 = 0
    · simp [h0]
    simp only [h0, ↓reduceIte, ne_eq, List.append_eq_nil_iff, not_and]
    -- the left subtree has no overlap when its max is at or below the query's begin
    have hlnone : ∀ m, l.maxEnd = some m → ¬ affCmp m q.1 > 0 → stab q l.inorder = [] := by
      intro m hm hle'
      rw [affCmp_pos_iff] at hle'
      rw [stab_eq_nil_iff]
      intro z hz
      exact no_ovl_of_end_le (affLe_trans (maxEnd_ge l m hm z hz) hle')
    cases hm : l.maxEnd with
    | none =>
      have : l = .leaf := by cases l with
        | leaf => rfl
        | node _ _ _ _ => simp at hm
      subst this
      simp only [RbT.inorder_leaf, stab, List.filter_nil, ne_eq] at ihr ⊢
      rw [ihr]; simp
    | some m =>
      simp only
      by_cases hgt : affCmp m q.1 > 0
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hgt), ihl]
        constructor
        · intro h1 h2; exact absurd h2 h1
        · intro h hnil
          apply h hnil
          -- the entry with the max end does not overlap: it is left of the query's end, and
          -- so is everything from it on
          obtain ⟨z0, hz0, hz0e⟩ := maxEnd_mem l m hm
          have hq0 : affLt q.1 z0.1.2 := by rw [hz0e]; exact (affCmp_pos_iff m q.1).1 hgt
          have hn0 : ivlCmp q z0.1 ≠ 0 := (stab_eq_nil_iff q _).1 hnil z0 hz0
          have hleft : affLt q.1 z0.1.1 ∧ ¬ affLt z0.1.1 q.2 := by
            rw [ne_eq, ivlCmp_eq_zero_iff] at hn0
            by_cases ha : affLt q.1 z0.1.1
            · exact ⟨ha, fun hb => hn0 ⟨fun _ => hb, hq0⟩⟩
            · exact absurd ⟨fun h => absurd h ha, hq0⟩ hn0
          rw [stab_eq_nil_iff]
          intro z hz
          have hb : ¬ affLt z.1.1 z0.1.1 := ivlLe_begin_le (ivlLe_trans (hle z0 hz0) (her z hz))
          exact no_ovl_of_left (affLt_of_lt_of_le hleft.1 hb) (affLe_trans hleft.2 hb)
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hgt), ihr, hlnone m hm hgt]
        simp

/-! ## `visit` (`Stab`, `Visit`) -/

/-- The entries `visit` calls the visitor on, in order (for a visitor that never stops it):
left only when the query is left of the node; when right of it, both subtrees if the query
overlaps `[begin, max)`, nothing otherwise; when overlapping, left, the node, right. -/
def RbT.visitL (q : IvlS) : RbT Entry → List Entry
  | .leaf => []
  | .node _ l e r =>
    if ivlCmp q e.1 < 0 then l.visitL q
    else if ivlCmp q e.1 > 0 then
      (if ivlCmp (e.1.1, nodeMax l e r) q = 0 then l.visitL q ++ r.visitL q else [])
    else l.visitL q ++ e :: r.visitL q

/-- **`visit` visits exactly the overlapping entries, in order**, in a sorted tree, for a query
that is not empty-and-finite (`b = ""`, which overlaps nothing, or `b < e`). -/
theorem visit_stab (q : IvlS) (hq : q.1 = go!"" ∨ affLt q.1 q.2) : ∀ (t : RbT Entry),
    IvSorted t.inorder → t.visitL q = stab q t.inorder
  | .leaf, _ => rfl
  | .node c l e r, hs => by
    obtain ⟨hl, hr, hle, her⟩ := ivSorted_node hs
    have ihl := visit_stab q hq l hl
    have ihr := visit_stab q hq r hr
    unfold RbT.visitL
    rw [RbT.inorder_node, stab_append, stab_cons]
    by_cases hneg : ivlCmp q e.1 < 0
    · -- the query is left of the node: so it is of the node's right subtree
      have h0 : ¬ ivlCmp q e.1 = 0 := by omega
      simp only [hneg, h0, ↓reduceIte]
      rw [ihl]
      have hn := (ivlCmp_neg_iff q e.1).1 hneg
      have : stab q r.inorder = [] := by
        rw [stab_eq_nil_iff]
        intro z hz
        have hb : ¬ affLt z.1.1 e.1.1 := ivlLe_begin_le (her z hz)
        exact no_ovl_of_left (affLt_of_lt_of_le hn.1 hb) (affLe_trans hn.2 hb)
      rw [this]; simp
    by_cases hpos : ivlCmp q e.1 > 0
    · have h0 : ¬ ivlCmp q e.1 = 0 := by omega
      -- nothing in the node's subtree overlaps the query unless it overlaps `[begin, max)`
      have hall : ¬ ivlCmp (e.1.1, nodeMax l e r) q = 0 →
          ∀ z ∈ (RbT.node c l e r).inorder, ivlCmp q z.1 ≠ 0 := by
        intro hm z hz
        rcases hq with hq | hq
        · exact no_ovl_of_end_le (by rw [hq]; exact not_affLt_empty _)
        have hmax : ¬ affLt (nodeMax l e r) z.1.2 :=
          maxEnd_ge (.node c l e r) _ (maxEnd_node c l e r) z hz
        have hp := (ivlCmp_pos_iff q e.1).1 hpos
        by_cases hneg' : ivlCmp (e.1.1, nodeMax l e r) q < 0
        · -- the subtree's ends are at or below the query's begin
          have hn := (ivlCmp_neg_iff _ _).1 hneg'
          exact no_ovl_of_end_le (affLe_trans hmax hn.2)
        · -- the node's begin is at or above the query's end: then the query is left of it
          have hp' : ivlCmp (e.1.1, nodeMax l e r) q > 0 := by omega
          have hn := ((ivlCmp_pos_iff _ _).1 hp').2
          exact absurd ⟨affLt_of_lt_of_le hq hn, hn⟩ hp.1
      simp only [hneg, hpos, h0, ↓reduceIte]
      by_cases hm : ivlCmp (e.1.1, nodeMax l e r) q = 0
      · simp only [hm, ↓reduceIte]; rw [ihl, ihr]
      · simp only [hm, ↓reduceIte]
        have hst := (stab_eq_nil_iff q _).2 (hall hm)
        rw [RbT.inorder_node, stab_append, stab_cons] at hst
        simp only [h0, ↓reduceIte] at hst
        rw [hst]
    · have h0 : ivlCmp q e.1 = 0 := by omega
      simp only [h0, ↓reduceIte, Int.lt_irrefl, gt_iff_lt]
      rw [ihl, ihr]

end entries

/-! ## The red-black invariant -/

section rb
variable [ext : FfiSyntax]

/-- The root is black (after `insertFixup`'s and `deleteFixup`'s last line). -/
def rootBlack (t : RbT Entry) : Prop := t.color = .black

/-- The red-black invariant: a red node's children are black, the black height is the same on
every path, the root is black. -/
def RbOk (t : RbT Entry) : Prop := t.redOk ∧ t.blackHeight.isSome ∧ rootBlack t

theorem rbOk_leaf : RbOk (.leaf : RbT Entry) := ⟨trivial, rfl, rfl⟩

end rb

end adt
end EtcdGrove
end Perennial
