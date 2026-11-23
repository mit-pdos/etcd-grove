/-
The pure model of gods' red-black tree (`trees/redblacktree`, v1.18.1 through its model
`models/gods`, notes/gods-verified.md): a binary tree whose nodes carry the node's address, its key
(an `int64` the comparator compares, behind the encoding of the map's keys), its value and its
color (Go's `color`: `true` black, `false` red), and contexts (the path from the root to a subtree,
innermost frame first), in which the code's walks (down from the root, up through the parent
pointers) and rotations are stated.

Only what the treemap specs need is modelled: the entries in order and the shape. The red-black
balance is not (no proof needs it); the one color fact the code's safety needs is that the root is
black (`Defs.lean`).
-/
module

public import Dsverify.Proof.github_com.emirpasic.gods.maps.treemap.Defs

@[expose] public section

noncomputable section

namespace Perennial.github_com.emirpasic.gods.trees.redblacktree

open github_com.emirpasic.gods.maps.treemap (sortedE lookupE putE idxOf)

universe u

/-- A tree: a leaf, or a node with its address, key, value, color and subtrees. -/
inductive RB (α : Type u) where
  | leaf
  | node (n : Loc) (k : w64) (v : α) (c : Bool) (l r : RB α)

namespace RB
variable {α : Type u}

/-- The address of the root (`nil` for a leaf). -/
def loc : RB α → Loc
  | leaf => null
  | node n _ _ _ _ _ => n

/-- The root's color (a leaf is black, as gods' `nodeColor(nil)`). -/
def color : RB α → Bool
  | leaf => true
  | node _ _ _ c _ _ => c

/-- The entries in order. -/
def entries : RB α → List (w64 × α)
  | leaf => []
  | node _ k v _ l r => l.entries ++ (k, v) :: r.entries

/-- The nodes' addresses. -/
def locs : RB α → List Loc
  | leaf => []
  | node n _ _ _ l r => n :: (l.locs ++ r.locs)

@[simp] theorem loc_leaf : (leaf : RB α).loc = null := rfl
@[simp] theorem loc_node (n k v c) (l r : RB α) : (node n k v c l r).loc = n := rfl
@[simp] theorem color_leaf : (leaf : RB α).color = true := rfl
@[simp] theorem color_node (n k v c) (l r : RB α) : (node n k v c l r).color = c := rfl
@[simp] theorem entries_leaf : (leaf : RB α).entries = [] := rfl
@[simp] theorem entries_node (n k v c) (l r : RB α) :
    (node n k v c l r).entries = l.entries ++ (k, v) :: r.entries := rfl
@[simp] theorem locs_leaf : (leaf : RB α).locs = [] := rfl
@[simp] theorem locs_node (n k v c) (l r : RB α) :
    (node n k v c l r).locs = n :: (l.locs ++ r.locs) := rfl

/-- The root's address is one of the nodes' (for a node). -/
theorem loc_mem_locs (t : RB α) (h : t ≠ leaf) : t.loc ∈ t.locs := by
  cases t with
  | leaf => exact absurd rfl h
  | node => simp

/-- The leftmost entry of a nonempty tree is its first. -/
theorem entries_ne_nil (n k v c) (l r : RB α) : (node n k v c l r).entries ≠ [] := by simp

end RB

open RB

/-- A frame of a context: the hole is the left (`L`) or right (`R`) child of the node. -/
inductive Frame (α : Type u) where
  | L (n : Loc) (k : w64) (v : α) (c : Bool) (r : RB α)
  | R (n : Loc) (k : w64) (v : α) (c : Bool) (l : RB α)

namespace Frame
variable {α : Type u}

def loc : Frame α → Loc
  | L n _ _ _ _ => n
  | R n _ _ _ _ => n

/-- The frame with `t` in its hole. -/
def fill : Frame α → RB α → RB α
  | L n k v c r, t => .node n k v c t r
  | R n k v c l, t => .node n k v c l t

/-- The entries of the frame before (`pre`) and after (`post`) its hole. -/
def pre : Frame α → List (w64 × α)
  | L .. => []
  | R _ k v _ l => l.entries ++ [(k, v)]

def post : Frame α → List (w64 × α)
  | L _ k v _ r => (k, v) :: r.entries
  | R .. => []

/-- The frame's nodes' addresses. -/
def locs : Frame α → List Loc
  | L n _ _ _ r => n :: r.locs
  | R n _ _ _ l => n :: l.locs

@[simp] theorem fill_loc (f : Frame α) (t : RB α) : (f.fill t).loc = f.loc := by
  cases f <;> rfl

theorem fill_entries (f : Frame α) (t : RB α) :
    (f.fill t).entries = f.pre ++ t.entries ++ f.post := by
  cases f <;> simp [fill, pre, post]

theorem fill_locs_perm (f : Frame α) (t : RB α) : (f.fill t).locs.Perm (t.locs ++ f.locs) := by
  cases f with
  | L n k v c r =>
    simp only [fill, locs, RB.locs_node]
    exact (List.perm_middle).symm
  | R n k v c l =>
    simp only [fill, locs, RB.locs_node]
    refine List.Perm.trans ?_ (List.perm_middle).symm
    exact List.Perm.cons _ List.perm_append_comm

end Frame

/-- A context: the frames from the hole up to the root, innermost first. -/
abbrev Ctx (α : Type u) := List (Frame α)

namespace Ctx
variable {α : Type u}

/-- The tree with `t` in the context's hole. -/
def plug : Ctx α → RB α → RB α
  | [], t => t
  | f :: C, t => plug C (f.fill t)

def pre : Ctx α → List (w64 × α)
  | [] => []
  | f :: C => pre C ++ f.pre

def post : Ctx α → List (w64 × α)
  | [] => []
  | f :: C => f.post ++ post C

def locs : Ctx α → List Loc
  | [] => []
  | f :: C => f.locs ++ locs C

/-- The hole's parent: the innermost frame's node, or `p` (the root's parent) at the top. -/
def parent : Ctx α → Loc → Loc
  | [], p => p
  | f :: _, _ => f.loc

@[simp] theorem plug_nil (t : RB α) : plug [] t = t := rfl
@[simp] theorem plug_cons (f : Frame α) (C : Ctx α) (t : RB α) :
    plug (f :: C) t = plug C (f.fill t) := rfl
@[simp] theorem post_nil : post ([] : Ctx α) = [] := rfl
@[simp] theorem pre_nil : pre ([] : Ctx α) = [] := rfl
@[simp] theorem locs_nil : locs ([] : Ctx α) = [] := rfl
@[simp] theorem parent_nil (p : Loc) : parent ([] : Ctx α) p = p := rfl
@[simp] theorem parent_cons (f : Frame α) (C : Ctx α) (p : Loc) : parent (f :: C) p = f.loc := rfl

theorem plug_entries (C : Ctx α) (t : RB α) :
    (plug C t).entries = pre C ++ t.entries ++ post C := by
  induction C generalizing t with
  | nil => simp [plug, pre, post]
  | cons f C ih =>
    simp only [plug, ih, Frame.fill_entries, pre, post, List.append_assoc]

theorem plug_locs_perm (C : Ctx α) (t : RB α) : (plug C t).locs.Perm (t.locs ++ locs C) := by
  induction C generalizing t with
  | nil => simp [plug, locs]
  | cons f C ih =>
    simp only [plug, locs]
    refine (ih (f.fill t)).trans ?_
    have := Frame.fill_locs_perm f t
    rw [← List.append_assoc]
    exact this.append_right _

theorem plug_append (C D : Ctx α) (t : RB α) : plug (C ++ D) t = plug D (plug C t) := by
  induction C generalizing t with
  | nil => rfl
  | cons f C ih => simp [plug, ih]

end Ctx

/-! ## Search: the keys around a subtree -/

section search
variable {α : Type u}

/-- `k` is above every key before the context's hole and below every key after it. -/
def Bounds (k : w64) (C : Ctx α) : Prop :=
  (∀ e ∈ Ctx.pre C, sint.Z e.1 < sint.Z k) ∧ (∀ e ∈ Ctx.post C, sint.Z k < sint.Z e.1)

theorem Bounds_nil (k : w64) : Bounds k ([] : Ctx α) := by simp [Bounds, Ctx.pre, Ctx.post]

theorem lookupE_append_left (A B : List (w64 × α)) (k : w64) (h : ∀ e ∈ A, e.1 ≠ k) :
    lookupE (A ++ B) k = lookupE B k := by
  induction A with
  | nil => rfl
  | cons a A ih =>
    have ha : a.1 ≠ k := h a (by simp)
    simp only [lookupE, List.cons_append, List.find?_cons, ha, decide_false] at ih ⊢
    exact ih (fun e he => h e (by simp [he]))

theorem lookupE_append_right (A B : List (w64 × α)) (k : w64) (h : ∀ e ∈ B, e.1 ≠ k) :
    lookupE (A ++ B) k = lookupE A k := by
  induction A with
  | nil =>
    simp only [List.nil_append, lookupE]
    rw [List.find?_eq_none.mpr (by intro e he; simpa using h e he)]
    rfl
  | cons a A ih =>
    simp only [lookupE, List.cons_append, List.find?_cons] at ih ⊢
    split <;> simp_all

theorem sortedE_split {A B : List (w64 × α)} (hs : sortedE (A ++ B)) :
    ∀ a ∈ A, ∀ b ∈ B, sint.Z a.1 < sint.Z b.1 := by
  unfold sortedE at hs
  rw [List.pairwise_append] at hs
  exact hs.2.2

theorem sortedE_left {A B : List (w64 × α)} (hs : sortedE (A ++ B)) : sortedE A := by
  unfold sortedE at hs ⊢; exact (List.pairwise_append.mp hs).1

theorem sortedE_right {A B : List (w64 × α)} (hs : sortedE (A ++ B)) : sortedE B := by
  unfold sortedE at hs ⊢; exact (List.pairwise_append.mp hs).2.1

/-- In a context with bounds, `k`'s value is the subtree's. -/
theorem lookupE_plug (C : Ctx α) (t : RB α) (k : w64) (hb : Bounds k C) :
    lookupE (Ctx.plug C t).entries k = lookupE t.entries k := by
  rw [Ctx.plug_entries]
  rw [List.append_assoc, lookupE_append_left _ _ k
    (fun e he heq => by have := hb.1 e he; rw [heq] at this; omega)]
  rw [lookupE_append_right _ _ k
    (fun e he heq => by have := hb.2 e he; rw [heq] at this; omega)]

/-- The keys of a node's subtrees, in a sorted tree. -/
theorem sortedE_plug_node {C : Ctx α} {n : Loc} {k : w64} {v : α} {c : Bool} {L R : RB α}
    (hs : sortedE (Ctx.plug C (.node n k v c L R)).entries) :
    (∀ e ∈ L.entries, sint.Z e.1 < sint.Z k) ∧ (∀ e ∈ R.entries, sint.Z k < sint.Z e.1) ∧
    (∀ e ∈ Ctx.pre C, sint.Z e.1 < sint.Z k) ∧ (∀ e ∈ Ctx.post C, sint.Z k < sint.Z e.1) ∧
    (∀ e ∈ R.entries, ∀ e' ∈ Ctx.post C, sint.Z e.1 < sint.Z e'.1) ∧
    (∀ e ∈ Ctx.pre C, ∀ e' ∈ L.entries, sint.Z e.1 < sint.Z e'.1) := by
  rw [Ctx.plug_entries, RB.entries_node] at hs
  have h1 := sortedE_split (A := Ctx.pre C ++ (L.entries ++ (k, v) :: R.entries)) (B := Ctx.post C)
    (by simpa [List.append_assoc] using hs)
  have hmid := sortedE_left (A := Ctx.pre C ++ (L.entries ++ (k, v) :: R.entries))
    (B := Ctx.post C) (by simpa [List.append_assoc] using hs)
  have h2 := sortedE_split hmid
  have hnode := sortedE_right hmid
  have h3 := sortedE_split hnode
  have hkR := sortedE_right hnode
  unfold sortedE at hkR
  rw [List.pairwise_cons] at hkR
  refine ⟨fun e he => h3 e he (k, v) (by simp), fun e he => hkR.1 e he,
    fun e he => h2 e he (k, v) (by simp), fun e he => h1 (k, v) (by simp) e he,
    fun e he e' he' => h1 e (by simp [he]) e' he', fun e he e' he' => h2 e he e' (by simp [he'])⟩

theorem Bounds_left {C : Ctx α} {n : Loc} {k' : w64} {v : α} {c : Bool} {L R : RB α} {k : w64}
    (hs : sortedE (Ctx.plug C (.node n k' v c L R)).entries) (hb : Bounds k C)
    (hlt : sint.Z k < sint.Z k') : Bounds k (.L n k' v c R :: C) := by
  obtain ⟨-, hR, -, -, -, -⟩ := sortedE_plug_node hs
  refine ⟨by simpa [Ctx.pre, Frame.pre] using hb.1, ?_⟩
  simp only [Ctx.post, Frame.post, List.cons_append, List.mem_cons, List.mem_append]
  rintro e (rfl | he | he)
  · exact hlt
  · have := hR e he; omega
  · exact hb.2 e he

theorem Bounds_right {C : Ctx α} {n : Loc} {k' : w64} {v : α} {c : Bool} {L R : RB α} {k : w64}
    (hs : sortedE (Ctx.plug C (.node n k' v c L R)).entries) (hb : Bounds k C)
    (hlt : sint.Z k' < sint.Z k) : Bounds k (.R n k' v c L :: C) := by
  obtain ⟨hL, -, -, -, -, -⟩ := sortedE_plug_node hs
  refine ⟨?_, by simpa [Ctx.post, Frame.post] using hb.2⟩
  intro e he
  simp only [Ctx.pre, Frame.pre, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he | he
  · exact hb.1 e he
  · have := hL e he; omega
  · subst he; exact hlt

theorem lookupE_node_self {n : Loc} {k : w64} {v : α} {c : Bool} {L R : RB α}
    (hL : ∀ e ∈ L.entries, sint.Z e.1 < sint.Z k) :
    lookupE (RB.node n k v c L R).entries k = some v := by
  rw [RB.entries_node, lookupE_append_left _ _ k
    (fun e he heq => by have := hL e he; rw [heq] at this; omega)]
  simp [lookupE]

end search

end Perennial.github_com.emirpasic.gods.trees.redblacktree
