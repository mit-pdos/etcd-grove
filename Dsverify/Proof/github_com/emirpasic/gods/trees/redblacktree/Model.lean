/-
The pure model of gods' red-black tree (`trees/redblacktree`, v1.18.1 through its model
`models/gods`, notes/gods-verified.md): a binary tree whose nodes carry the node's address, its key
(an `int64` the comparator compares, behind the encoding of the map's keys) and its value, and
contexts (the path from the root to a subtree,
innermost frame first), in which the code's walks (down from the root, up through the parent
pointers) and rotations are stated.

Only what the treemap specs need is modelled: the entries in order and the shape. The colors are
not (they are the heap's, `Defs.lean`): no proof needs the red-black balance; the one color fact
the code's safety needs is that the root is black (`rootBlack`).
-/
module

public import Dsverify.Proof.github_com.emirpasic.gods.maps.treemap.Defs

@[expose] public section

noncomputable section

namespace Perennial.github_com.emirpasic.gods.trees.redblacktree

open github_com.emirpasic.gods.maps.treemap (sortedE lookupE putE idxOf)

universe u

/-- A tree: a leaf, or a node with its address, key, value and subtrees. -/
inductive RB (α : Type u) where
  | leaf
  | node (n : Loc) (k : w64) (v : α) (l r : RB α)

namespace RB
variable {α : Type u}

/-- The address of the root (`nil` for a leaf). -/
def loc : RB α → Loc
  | leaf => null
  | node n _ _ _ _ => n

/-- The entries in order. -/
def entries : RB α → List (w64 × α)
  | leaf => []
  | node _ k v l r => l.entries ++ (k, v) :: r.entries

/-- The nodes' addresses. -/
def locs : RB α → List Loc
  | leaf => []
  | node n _ _ l r => n :: (l.locs ++ r.locs)

@[simp] theorem loc_leaf : (leaf : RB α).loc = null := rfl
@[simp] theorem loc_node (n k v) (l r : RB α) : (node n k v l r).loc = n := rfl
@[simp] theorem entries_leaf : (leaf : RB α).entries = [] := rfl
@[simp] theorem entries_node (n k v) (l r : RB α) :
    (node n k v l r).entries = l.entries ++ (k, v) :: r.entries := rfl
@[simp] theorem locs_leaf : (leaf : RB α).locs = [] := rfl
@[simp] theorem locs_node (n k v) (l r : RB α) :
    (node n k v l r).locs = n :: (l.locs ++ r.locs) := rfl

/-- The root's address is one of the nodes' (for a node). -/
theorem loc_mem_locs (t : RB α) (h : t ≠ leaf) : t.loc ∈ t.locs := by
  cases t with
  | leaf => exact absurd rfl h
  | node => simp

/-- The leftmost entry of a nonempty tree is its first. -/
theorem entries_ne_nil (n k v) (l r : RB α) : (node n k v l r).entries ≠ [] := by simp

end RB

open RB

/-- A frame of a context: the hole is the left (`L`) or right (`R`) child of the node. -/
inductive Frame (α : Type u) where
  | L (n : Loc) (k : w64) (v : α) (r : RB α)
  | R (n : Loc) (k : w64) (v : α) (l : RB α)

namespace Frame
variable {α : Type u}

def loc : Frame α → Loc
  | L n _ _ _ => n
  | R n _ _ _ => n

/-- The frame with `t` in its hole. -/
def fill : Frame α → RB α → RB α
  | L n k v r, t => .node n k v t r
  | R n k v l, t => .node n k v l t

/-- The entries of the frame before (`pre`) and after (`post`) its hole. -/
def pre : Frame α → List (w64 × α)
  | L .. => []
  | R _ k v l => l.entries ++ [(k, v)]

def post : Frame α → List (w64 × α)
  | L _ k v r => (k, v) :: r.entries
  | R .. => []

/-- The frame's nodes' addresses. -/
def locs : Frame α → List Loc
  | L n _ _ r => n :: r.locs
  | R n _ _ l => n :: l.locs

@[simp] theorem fill_loc (f : Frame α) (t : RB α) : (f.fill t).loc = f.loc := by
  cases f <;> rfl

theorem fill_entries (f : Frame α) (t : RB α) :
    (f.fill t).entries = f.pre ++ t.entries ++ f.post := by
  cases f <;> simp [fill, pre, post]

theorem fill_locs_perm (f : Frame α) (t : RB α) : (f.fill t).locs.Perm (t.locs ++ f.locs) := by
  cases f with
  | L n k v r =>
    simp only [fill, locs, RB.locs_node]
    exact (List.perm_middle).symm
  | R n k v l =>
    simp only [fill, locs, RB.locs_node]
    refine List.Perm.trans ?_ (List.perm_middle).symm
    exact List.Perm.cons _ List.perm_append_comm

/-- The frame's other subtree (beside the hole). -/
def sib : Frame α → RB α
  | L _ _ _ r => r
  | R _ _ _ l => l

theorem sib_locs_sub (f : Frame α) : ∀ x ∈ f.sib.locs, x ∈ f.locs := by
  cases f <;> simp only [sib, locs, List.mem_cons] <;> intro x hx <;> exact Or.inr hx

theorem mem_fill_left (f : Frame α) (t : RB α) {x : Loc} (hx : x ∈ t.locs) :
    x ∈ (f.fill t).locs :=
  (fill_locs_perm f t).symm.subset (List.mem_append_left _ hx)

theorem mem_fill_right (f : Frame α) (t : RB α) {x : Loc} (hx : x ∈ f.locs) :
    x ∈ (f.fill t).locs :=
  (fill_locs_perm f t).symm.subset (List.mem_append_right _ hx)

theorem loc_mem_locs (f : Frame α) : f.loc ∈ f.locs := by
  cases f <;> simp [loc, locs]

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

/-! ## Distinct addresses -/

/-- The addresses of `node n A (node r B E)` are distinct. -/
theorem locs_rot_facts {α : Type u} {n : Loc} {k : w64} {v : α} {A : RB α} {r : Loc} {k' : w64}
    {v' : α} {B E : RB α} (h : (RB.node n k v A (RB.node r k' v' B E)).locs.Nodup) :
    n ≠ r ∧ n ∉ A.locs ∧ n ∉ B.locs ∧ n ∉ E.locs ∧ r ∉ A.locs ∧ r ∉ B.locs ∧ r ∉ E.locs ∧
    (∀ x ∈ A.locs, x ∉ B.locs) ∧ (∀ x ∈ A.locs, x ∉ E.locs) ∧ (∀ x ∈ B.locs, x ∉ E.locs) ∧
    A.locs.Nodup ∧ B.locs.Nodup ∧ E.locs.Nodup := by
  simp only [RB.locs_node, List.nodup_cons, List.nodup_append, List.mem_append, List.mem_cons,
    not_or] at h
  grind

/-- The addresses of `node n (node l A B) E` are distinct. -/
theorem locs_rotR_facts {α : Type u} {n : Loc} {k : w64} {v : α} {l : Loc} {k' : w64} {v' : α}
    {A B E : RB α} (h : (RB.node n k v (RB.node l k' v' A B) E).locs.Nodup) :
    n ≠ l ∧ n ∉ A.locs ∧ n ∉ B.locs ∧ n ∉ E.locs ∧ l ∉ A.locs ∧ l ∉ B.locs ∧ l ∉ E.locs ∧
    (∀ x ∈ A.locs, x ∉ B.locs) ∧ (∀ x ∈ A.locs, x ∉ E.locs) ∧ (∀ x ∈ B.locs, x ∉ E.locs) ∧
    A.locs.Nodup ∧ B.locs.Nodup ∧ E.locs.Nodup := by
  simp only [RB.locs_node, List.nodup_cons, List.nodup_append, List.mem_append, List.mem_cons,
    not_or] at h
  grind

theorem Ctx.plug_loc_cons {α : Type u} (f : Frame α) (C : Ctx α) (t t' : RB α) :
    (Ctx.plug (f :: C) t).loc = (Ctx.plug (f :: C) t').loc := by
  induction C generalizing f t t' with
  | nil => simp [Ctx.plug]
  | cons g C ih => simp only [Ctx.plug_cons] at ih ⊢; exact ih g _ _

theorem Ctx.plug_locs_congr {α : Type u} (C : Ctx α) {t t' : RB α} (h : t.locs.Perm t'.locs) :
    (Ctx.plug C t).locs.Perm (Ctx.plug C t').locs :=
  (Ctx.plug_locs_perm C t).trans ((h.append_right _).trans (Ctx.plug_locs_perm C t').symm)

theorem rotL_locs_perm {α : Type u} (n : Loc) (k : w64) (v : α) (A : RB α) (r : Loc) (k' : w64)
    (v' : α) (B E : RB α) :
    (RB.node n k v A (.node r k' v' B E)).locs.Perm (RB.node r k' v' (.node n k v A B) E).locs := by
  rw [List.perm_iff_count]
  intro a
  simp only [RB.locs_node, List.count_cons, List.count_append]
  omega

theorem rotR_locs_perm {α : Type u} (n : Loc) (k : w64) (v : α) (l : Loc) (k' : w64) (v' : α)
    (A B E : RB α) :
    (RB.node n k v (.node l k' v' A B) E).locs.Perm (RB.node l k' v' A (.node n k v B E)).locs := by
  rw [List.perm_iff_count]
  intro a
  simp only [RB.locs_node, List.count_cons, List.count_append]
  omega

theorem Ctx.plug_loc_mem {α : Type u} {C : Ctx α} (t : RB α) (hC : C ≠ []) :
    (Ctx.plug C t).loc ∈ Ctx.locs C := by
  induction C generalizing t with
  | nil => exact absurd rfl hC
  | cons f C ih =>
    simp only [Ctx.plug_cons, Ctx.locs, List.mem_append]
    cases C with
    | nil => left; cases f <;> simp [Frame.fill, Frame.locs]
    | cons g C' => right; exact ih _ (by simp)

theorem rotR_entries {α : Type u} (g : Loc) (kg : w64) (vg : α) (p : Loc) (kp : w64) (vp : α)
    (A B U : RB α) :
    (RB.node g kg vg (.node p kp vp A B) U).entries = (RB.node p kp vp A (.node g kg vg B U)).entries := by
  simp

theorem rotL_entries {α : Type u} (g : Loc) (kg : w64) (vg : α) (U : RB α) (p : Loc) (kp : w64)
    (vp : α) (A B : RB α) :
    (RB.node g kg vg U (.node p kp vp A B)).entries = (RB.node p kp vp (.node g kg vg U A) B).entries := by
  simp

theorem ne_loc_of_not_mem {α : Type u} {t : RB α} {x : Loc} (hx : x ≠ null) (hm : x ∉ t.locs) :
    x ≠ t.loc := by
  cases t with
  | leaf => simpa using hx
  | node n => intro e; subst e; simp at hm

theorem Ctx.plug_loc_congr {α : Type u} (C : Ctx α) {t t' : RB α} (h : t'.loc = t.loc) :
    (Ctx.plug C t').loc = (Ctx.plug C t).loc := by
  cases C with
  | nil => exact h
  | cons f C => exact Ctx.plug_loc_cons f C t' t

theorem Ctx.plug_locs_insert {α : Type u} (C : Ctx α) {t t' : RB α} (l : Loc)
    (h : t'.locs.Perm (l :: t.locs)) : (Ctx.plug C t').locs.Perm (l :: (Ctx.plug C t).locs) :=
  (Ctx.plug_locs_perm C t').trans ((h.append_right _).trans
    (List.Perm.cons l (Ctx.plug_locs_perm C t).symm))

theorem Ctx.plug_ne_leaf {α : Type u} (C : Ctx α) {t : RB α} (ht : t ≠ .leaf) :
    Ctx.plug C t ≠ .leaf := by
  induction C generalizing t with
  | nil => exact ht
  | cons f C ih => exact ih (by cases f <;> simp [Frame.fill])

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
theorem sortedE_plug_node {C : Ctx α} {n : Loc} {k : w64} {v : α} {L R : RB α}
    (hs : sortedE (Ctx.plug C (.node n k v L R)).entries) :
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

theorem Bounds_left {C : Ctx α} {n : Loc} {k' : w64} {v : α} {L R : RB α} {k : w64}
    (hs : sortedE (Ctx.plug C (.node n k' v L R)).entries) (hb : Bounds k C)
    (hlt : sint.Z k < sint.Z k') : Bounds k (.L n k' v R :: C) := by
  obtain ⟨-, hR, -, -, -, -⟩ := sortedE_plug_node hs
  refine ⟨by simpa [Ctx.pre, Frame.pre] using hb.1, ?_⟩
  simp only [Ctx.post, Frame.post, List.cons_append, List.mem_cons, List.mem_append]
  rintro e (rfl | he | he)
  · exact hlt
  · have := hR e he; omega
  · exact hb.2 e he

theorem Bounds_right {C : Ctx α} {n : Loc} {k' : w64} {v : α} {L R : RB α} {k : w64}
    (hs : sortedE (Ctx.plug C (.node n k' v L R)).entries) (hb : Bounds k C)
    (hlt : sint.Z k' < sint.Z k) : Bounds k (.R n k' v L :: C) := by
  obtain ⟨hL, -, -, -, -, -⟩ := sortedE_plug_node hs
  refine ⟨?_, by simpa [Ctx.post, Frame.post] using hb.2⟩
  intro e he
  simp only [Ctx.pre, Frame.pre, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he | he
  · exact hb.1 e he
  · have := hL e he; omega
  · subst he; exact hlt

theorem lookupE_node_self {n : Loc} {k : w64} {v : α} {L R : RB α}
    (hL : ∀ e ∈ L.entries, sint.Z e.1 < sint.Z k) :
    lookupE (RB.node n k v L R).entries k = some v := by
  rw [RB.entries_node, lookupE_append_left _ _ k
    (fun e he heq => by have := hL e he; rw [heq] at this; omega)]
  simp [lookupE]

end search

/-! ## Insertion: `putE` on a split list -/

section put
variable [GooseExts] {α : Type u}

open github_com.emirpasic.gods.maps.treemap (mem_putE sortedE_putE sortedE_cons)

/-- Two sorted entry lists with the same members are equal. -/
theorem sortedE_ext : ∀ {a b : List (w64 × α)}, sortedE a → sortedE b →
    (∀ x, x ∈ a ↔ x ∈ b) → a = b
  | [], [], _, _, _ => rfl
  | [], y :: b, _, _, h => absurd ((h y).mpr (by simp)) (by simp)
  | x :: a, [], _, _, h => absurd ((h x).mp (by simp)) (by simp)
  | x :: a, y :: b, ha, hb, h => by
    rw [sortedE_cons] at ha hb
    have hxy : x = y := by
      have hx : x ∈ y :: b := (h x).mp (by simp)
      have hy : y ∈ x :: a := (h y).mpr (by simp)
      rcases List.mem_cons.mp hx with e | hx
      · exact e
      rcases List.mem_cons.mp hy with e | hy
      · exact e.symm
      have h1 := hb.1 x hx
      have h2 := ha.1 y hy
      omega
    subst hxy
    congr 1
    apply sortedE_ext ha.2 hb.2
    intro z
    constructor
    · intro hz
      have := (h z).mp (by simp [hz])
      rcases List.mem_cons.mp this with e | hz'
      · subst e; have := ha.1 z hz; omega
      · exact hz'
    · intro hz
      have := (h z).mpr (by simp [hz])
      rcases List.mem_cons.mp this with e | hz'
      · subst e; have := hb.1 z hz; omega
      · exact hz'

/-- `putE` of a key already present replaces its value in place. -/
theorem putE_found (A B : List (w64 × α)) (k : w64) (v0 v : α)
    (hs : sortedE (A ++ (k, v0) :: B)) : putE (A ++ (k, v0) :: B) k v = A ++ (k, v) :: B := by
  have hA : ∀ e ∈ A, sint.Z e.1 < sint.Z k := fun e he => sortedE_split hs e he (k, v0) (by simp)
  have hB : ∀ e ∈ B, sint.Z k < sint.Z e.1 := by
    have := sortedE_right hs; rw [sortedE_cons] at this; exact this.1
  have hs' : sortedE (A ++ (k, v) :: B) := by
    unfold sortedE at hs ⊢
    rw [List.pairwise_append, List.pairwise_cons] at hs ⊢
    refine ⟨hs.1, ⟨fun e he => hB e he, hs.2.1.2⟩, fun a ha b hb => ?_⟩
    rcases List.mem_cons.mp hb with e | hb
    · subst e; exact hA a ha
    · exact hs.2.2 a ha b (by simp [hb])
  apply sortedE_ext (sortedE_putE _ k v hs) hs'
  intro ⟨k', x'⟩
  rw [mem_putE _ k v hs]
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨hm, hne⟩)
    · simp
    · simp only [List.mem_append, List.mem_cons, Prod.mk.injEq] at hm ⊢
      rcases hm with hm | ⟨e, -⟩ | hm
      · exact Or.inl hm
      · exact absurd e hne
      · exact Or.inr (Or.inr hm)
  · intro hm
    simp only [List.mem_append, List.mem_cons, Prod.mk.injEq] at hm
    rcases hm with hm | ⟨rfl, rfl⟩ | hm
    · right; refine ⟨by simp [hm], fun e => ?_⟩
      subst e; have := hA _ hm; simp at this
    · left; exact ⟨rfl, rfl⟩
    · right; refine ⟨by simp [hm], fun e => ?_⟩
      subst e; have := hB _ hm; simp at this

/-- `putE` of a new key between `A` and `B` inserts it there. -/
theorem putE_between (A B : List (w64 × α)) (k : w64) (v : α) (hs : sortedE (A ++ B))
    (hA : ∀ e ∈ A, sint.Z e.1 < sint.Z k) (hB : ∀ e ∈ B, sint.Z k < sint.Z e.1) :
    putE (A ++ B) k v = A ++ (k, v) :: B := by
  have hs' : sortedE (A ++ (k, v) :: B) := by
    unfold sortedE at hs ⊢
    rw [List.pairwise_append] at hs
    rw [List.pairwise_append, List.pairwise_cons]
    refine ⟨hs.1, ⟨fun e he => hB e he, hs.2.1⟩, fun a ha b hb => ?_⟩
    rcases List.mem_cons.mp hb with e | hb
    · subst e; exact hA a ha
    · exact hs.2.2 a ha b hb
  apply sortedE_ext (sortedE_putE _ k v hs) hs'
  intro ⟨k', x'⟩
  rw [mem_putE _ k v hs]
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨hm, -⟩)
    · simp
    · simp only [List.mem_append, List.mem_cons, Prod.mk.injEq] at hm ⊢
      rcases hm with hm | hm
      · exact Or.inl hm
      · exact Or.inr (Or.inr hm)
  · intro hm
    simp only [List.mem_append, List.mem_cons, Prod.mk.injEq] at hm
    rcases hm with hm | ⟨rfl, rfl⟩ | hm
    · right; refine ⟨by simp [hm], fun e => ?_⟩
      subst e; have := hA _ hm; simp at this
    · left; exact ⟨rfl, rfl⟩
    · right; refine ⟨by simp [hm], fun e => ?_⟩
      subst e; have := hB _ hm; simp at this

end put

end Perennial.github_com.emirpasic.gods.trees.redblacktree
