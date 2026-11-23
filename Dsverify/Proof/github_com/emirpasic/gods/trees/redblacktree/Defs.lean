/-
The representation of gods' red-black tree (`trees/redblacktree`) in the heap
(notes/gods-verified.md): a model tree `T` (`Model.lean`) and a heap function `h` giving each node
address's Go `Node`; `Rep enc h T p` says that every node of `T` is at its address with its key
(the encoding `enc k` of its model key), value, color, children's addresses and parent's (`p` for
the root). The points-tos are `ownNodes h D` over a list `D` of the addresses (a permutation of
`T`'s, without duplicates); a store at a node is a `upd h l x`.

`isTree tr enc es` is a `*Tree` at `tr` holding the entries `es`: its root `T.loc`, its comparator
meeting `cmpOk` on the encoded keys, `T`'s entries `es` strictly increasing (the BST order), and
its root black (the one red-black fact the code's safety needs: a red node has a parent, so
`insertCase4`/`insertCase5` find a grandparent). The size field is not tracked (no spec reads it;
its `++` wraps without a panic).
-/
module

public import Dsverify.Proof.github_com.emirpasic.gods.trees.redblacktree.Model
public import Dsverify.Spec.github_com.emirpasic.gods.maps.treemap.Specs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.emirpasic.gods.trees.redblacktree

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Classical
open github_com.emirpasic.gods.maps.treemap (cmpOk sortedE Entries lookupE putE)

/-! ## The heap function -/

section heapfn
variable [GooseExts]

/-- `h` with `l` mapped to `x`. -/
def upd (h : Loc → Node) (l : Loc) (x : Node) : Loc → Node :=
  fun l' => if l' = l then x else h l'

@[simp] theorem upd_same (h : Loc → Node) (l : Loc) (x : Node) : upd h l x l = x := by
  simp [upd]

theorem upd_of_eq (h : Loc → Node) (l : Loc) (x : Node) (hx : h l = x) : upd h l x = h := by
  funext y
  by_cases hy : y = l
  · subst hy; simp [upd, hx]
  · simp [upd, hy]

theorem upd_ne (h : Loc → Node) (l l' : Loc) (x : Node) (hne : l' ≠ l) : upd h l x l' = h l' := by
  simp [upd, hne]

/-- The Go node of a model node. -/
abbrev nodeOf (enc : w64 → GoInterface) (k : w64) (v : GoInterface) (c : Bool) (l r p : Loc) : Node :=
  Node.mk (enc k) v c l r p

/-- The root is black (or there is none). -/
def rootBlack (h : Loc → Node) (T : RB GoInterface) : Prop := T.loc = null ∨ (h T.loc).color' = true

/-- Every node of the tree is at its address, with its key, value, children and parent (`p` the
root's); its color is the heap's. -/
def Rep (enc : w64 → GoInterface) (h : Loc → Node) : RB GoInterface → Loc → Prop
  | .leaf, _ => True
  | .node n k v l r, p =>
    n ≠ null ∧ h n = nodeOf enc k v (h n).color' l.loc r.loc p ∧ Rep enc h l n ∧ Rep enc h r n

/-- A frame's node, with `hole` the address in its hole and `p` its parent. -/
def RepF (enc : w64 → GoInterface) (h : Loc → Node) : Frame GoInterface → Loc → Loc → Prop
  | .L n k v r, hole, p => n ≠ null ∧ h n = nodeOf enc k v (h n).color' hole r.loc p ∧ Rep enc h r n
  | .R n k v l, hole, p => n ≠ null ∧ h n = nodeOf enc k v (h n).color' l.loc hole p ∧ Rep enc h l n

/-- A context's nodes, `hole` the address in its hole and `p` the root's parent. -/
def RepC (enc : w64 → GoInterface) (h : Loc → Node) : Ctx GoInterface → Loc → Loc → Prop
  | [], _, _ => True
  | f :: C, hole, p => RepF enc h f hole (Ctx.parent C p) ∧ RepC enc h C f.loc p

variable {enc : w64 → GoInterface} {h : Loc → Node}

@[simp] theorem Rep_leaf (p : Loc) : Rep enc h .leaf p := trivial

theorem Rep_node (n k v) (l r : RB GoInterface) (p : Loc) :
    Rep enc h (.node n k v l r) p ↔
      n ≠ null ∧ h n = nodeOf enc k v (h n).color' l.loc r.loc p ∧ Rep enc h l n ∧ Rep enc h r n := Iff.rfl

theorem Rep_fill (f : Frame GoInterface) (t : RB GoInterface) (p : Loc) :
    Rep enc h (f.fill t) p ↔ RepF enc h f t.loc p ∧ Rep enc h t f.loc := by
  cases f with
  | L n k v r =>
    simp only [Frame.fill, Rep, RepF, Frame.loc]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩; exact ⟨⟨h1, h2, h4⟩, h3⟩
    · rintro ⟨⟨h1, h2, h4⟩, h3⟩; exact ⟨h1, h2, h3, h4⟩
  | R n k v l =>
    simp only [Frame.fill, Rep, RepF, Frame.loc]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩; exact ⟨⟨h1, h2, h3⟩, h4⟩
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩; exact ⟨h1, h2, h3, h4⟩

/-- **A tree in a context**: the context's nodes and the subtree's, under the hole's parent. -/
theorem Rep_plug (C : Ctx GoInterface) (t : RB GoInterface) (p : Loc) :
    Rep enc h (Ctx.plug C t) p ↔ RepC enc h C t.loc p ∧ Rep enc h t (Ctx.parent C p) := by
  induction C generalizing t with
  | nil => simp [Ctx.plug, RepC, Ctx.parent]
  | cons f C ih =>
    simp only [Ctx.plug_cons, ih, Frame.fill_loc, Rep_fill, RepC, Ctx.parent_cons]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h2, h1⟩, h3⟩
    · rintro ⟨⟨h2, h1⟩, h3⟩; exact ⟨h1, h2, h3⟩

/-- `Rep` reads `h` only at the tree's nodes. -/
theorem Rep_congr (h' : Loc → Node) (t : RB GoInterface) (p : Loc)
    (hag : ∀ l ∈ t.locs, h' l = h l) (hr : Rep enc h t p) : Rep enc h' t p := by
  induction t generalizing p with
  | leaf => trivial
  | node n k v l r ihl ihr =>
    obtain ⟨h1, h2, h3, h4⟩ := hr
    refine ⟨h1, ?_, ihl _ (fun x hx => hag x (by simp [hx])) h3,
      ihr _ (fun x hx => hag x (by simp [hx])) h4⟩
    rw [hag n (by simp)]; exact h2

theorem RepF_congr (h' : Loc → Node) (f : Frame GoInterface) (hole p : Loc)
    (hag : ∀ l ∈ f.locs, h' l = h l) (hr : RepF enc h f hole p) : RepF enc h' f hole p := by
  cases f with
  | L n k v r =>
    obtain ⟨h1, h2, h3⟩ := hr
    refine ⟨h1, ?_, Rep_congr h' r n (fun x hx => hag x (by simp [Frame.locs, hx])) h3⟩
    rw [hag n (by simp [Frame.locs])]; exact h2
  | R n k v l =>
    obtain ⟨h1, h2, h3⟩ := hr
    refine ⟨h1, ?_, Rep_congr h' l n (fun x hx => hag x (by simp [Frame.locs, hx])) h3⟩
    rw [hag n (by simp [Frame.locs])]; exact h2

theorem RepC_congr (h' : Loc → Node) (C : Ctx GoInterface) (hole p : Loc)
    (hag : ∀ l ∈ Ctx.locs C, h' l = h l) (hr : RepC enc h C hole p) : RepC enc h' C hole p := by
  induction C generalizing hole with
  | nil => trivial
  | cons f C ih =>
    obtain ⟨h1, h2⟩ := hr
    exact ⟨RepF_congr h' f hole _ (fun x hx => hag x (by simp [Ctx.locs, hx])) h1,
      ih _ (fun x hx => hag x (by simp [Ctx.locs, hx])) h2⟩

/-- A node's address is not `nil`. -/
theorem Rep_loc_ne_null (t : RB GoInterface) (p : Loc) (hr : Rep enc h t p) (hn : t ≠ .leaf) :
    t.loc ≠ null := by
  cases t with
  | leaf => exact absurd rfl hn
  | node => exact hr.1

/-- No node's address is `nil`. -/
theorem Rep_locs_ne_null (t : RB GoInterface) (p : Loc) (hr : Rep enc h t p) :
    ∀ l ∈ t.locs, l ≠ null := by
  induction t generalizing p with
  | leaf => simp
  | node n k v l r ihl ihr =>
    obtain ⟨h1, -, h3, h4⟩ := hr
    intro x hx
    simp only [RB.locs_node, List.mem_cons, List.mem_append] at hx
    rcases hx with rfl | hx | hx
    · exact h1
    · exact ihl _ h3 x hx
    · exact ihr _ h4 x hx

/-- A tree's root address is `nil` or one of its nodes'. -/
theorem loc_null_or_mem (t : RB GoInterface) : t.loc = null ∨ t.loc ∈ t.locs := by
  cases t <;> simp

/-- What `tree.replaceNode(old, new)` does to the root `rt` and the nodes `h`: `old`'s parent `p`
(or the root, if none) points to `new` in place of `old` (its left child if `p.Left == old`, else
its right), and `new`, if not `nil`, gets `p` as its parent. -/
def replaceRes (rt : Loc) (h : Loc → Node) (old new : Loc) : Loc × (Loc → Node) :=
  let p := (h old).Parent'
  let r1 : Loc × (Loc → Node) :=
    if p = null then (new, h)
    else if (h p).Left' = old then (rt, upd h p { h p with Left' := new })
    else (rt, upd h p { h p with Right' := new })
  (r1.1, if new = null then r1.2 else upd r1.2 new { r1.2 new with Parent' := p })

theorem replaceRes_root {rt : Loc} {h : Loc → Node} {old new : Loc} (hp : (h old).Parent' = null) :
    replaceRes rt h old new =
      (new, if new = null then h else upd h new { h new with Parent' := (h old).Parent' }) := by
  simp only [replaceRes, hp, if_true]

theorem replaceRes_left {rt : Loc} {h : Loc → Node} {old new : Loc} (hp : (h old).Parent' ≠ null)
    (hL : (h (h old).Parent').Left' = old) :
    replaceRes rt h old new =
      (rt, if new = null then upd h (h old).Parent' { h (h old).Parent' with Left' := new }
        else upd (upd h (h old).Parent' { h (h old).Parent' with Left' := new }) new
          { upd h (h old).Parent' { h (h old).Parent' with Left' := new } new with
            Parent' := (h old).Parent' }) := by
  simp only [replaceRes]
  rw [if_neg hp, if_pos hL]

theorem replaceRes_right {rt : Loc} {h : Loc → Node} {old new : Loc} (hp : (h old).Parent' ≠ null)
    (hL : ¬ (h (h old).Parent').Left' = old) :
    replaceRes rt h old new =
      (rt, if new = null then upd h (h old).Parent' { h (h old).Parent' with Right' := new }
        else upd (upd h (h old).Parent' { h (h old).Parent' with Right' := new }) new
          { upd h (h old).Parent' { h (h old).Parent' with Right' := new } new with
            Parent' := (h old).Parent' }) := by
  simp only [replaceRes]
  rw [if_neg hp, if_neg hL]

theorem upd_apply (h : Loc → Node) (l : Loc) (x : Node) (l' : Loc) :
    upd h l x l' = if l' = l then x else h l' := rfl

/-- What `replaceNode(old, new)` leaves at the nodes (`new` a node, not `old`'s parent). -/
theorem replaceRes_facts {rt : Loc} {h : Loc → Node} {old new : Loc}
    (hon : old ≠ new) (hpo : (h old).Parent' ≠ old) (hnp : new ≠ (h old).Parent')
    (hnn : new ≠ null) :
    (replaceRes rt h old new).2 old = h old ∧
    (replaceRes rt h old new).2 new = { h new with Parent' := (h old).Parent' } ∧
    (∀ l, (l ≠ (h old).Parent' ∨ (h old).Parent' = null) → l ≠ new →
      (replaceRes rt h old new).2 l = h l) ∧
    ((h old).Parent' ≠ null → (replaceRes rt h old new).2 (h old).Parent' =
      if (h (h old).Parent').Left' = old then { h (h old).Parent' with Left' := new }
      else { h (h old).Parent' with Right' := new }) ∧
    (replaceRes rt h old new).1 = (if (h old).Parent' = null then new else rt) := by
  have hon' := Ne.symm hon
  have hpo' := Ne.symm hpo
  have hnp' := Ne.symm hnp
  by_cases hp : (h old).Parent' = null
  · rw [replaceRes_root hp, if_neg hnn]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [upd_apply, hon]
    · simp [upd_apply]
    · intro l _ hl; simp [upd_apply, hl]
    · intro h0; exact absurd hp h0
    · simp [hp]
  · by_cases hL : (h (h old).Parent').Left' = old
    · rw [replaceRes_left hp hL, if_neg hnn]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [upd_apply, hon, hpo']
      · simp [upd_apply, hnp]
      · intro l hl1 hl2
        have hl1' : l ≠ (h old).Parent' := hl1.resolve_right hp
        simp [upd_apply, hl1', hl2]
      · intro _; simp [upd_apply, hnp', hL]
      · simp [hp]
    · rw [replaceRes_right hp hL, if_neg hnn]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [upd_apply, hon, hpo']
      · simp [upd_apply, hnp]
      · intro l hl1 hl2
        have hl1' : l ≠ (h old).Parent' := hl1.resolve_right hp
        simp [upd_apply, hl1', hl2]
      · intro _; simp [upd_apply, hnp', hL]
      · simp [hp]

theorem replaceRes_color (rt : Loc) (h : Loc → Node) (old new x : Loc) :
    ((replaceRes rt h old new).2 x).color' = (h x).color' := by
  simp only [replaceRes]
  by_cases hp : (h old).Parent' = null
  · simp only [hp, if_true]
    by_cases hn : new = null
    · simp [hn]
    · simp only [hn, if_false, upd_apply]; split <;> simp_all
  · simp only [hp, if_false]
    by_cases hL : (h (h old).Parent').Left' = old
    · simp only [hL, if_true]
      by_cases hn : new = null
      · simp only [hn, if_true, upd_apply]; split <;> simp_all
      · simp only [hn, if_false, upd_apply]; split <;> split <;> simp_all
    · simp only [hL, if_false]
      by_cases hn : new = null
      · simp only [hn, if_true, upd_apply]; split <;> simp_all
      · simp only [hn, if_false, upd_apply]; split <;> split <;> simp_all

theorem color_upd' {h h0 : Loc → Node} {l : Loc} {X : Node}
    (hh : ∀ y, (h y).color' = (h0 y).color') (hX : X.color' = (h l).color') :
    ∀ y, (upd h l X y).color' = (h0 y).color' := by
  intro y
  by_cases hy : y = l
  · subst hy; rw [upd_same, hX, hh]
  · rw [upd_ne h l y X hy, hh]

/-- A color store keeps the representation (colors are the heap's). -/
theorem Rep_recolor (l : Loc) (c : Bool) {t : RB GoInterface} {p : Loc} (hr : Rep enc h t p) :
    Rep enc (upd h l { h l with color' := c }) t p := by
  induction t generalizing p with
  | leaf => trivial
  | node n k v L R ihl ihr =>
    obtain ⟨h1, h2, h3, h4⟩ := hr
    refine ⟨h1, ?_, ihl h3, ihr h4⟩
    by_cases hn : n = l
    · subst hn; rw [upd_same]; rw [h2]
    · rw [upd_ne h l n _ hn]; exact h2

/-- The leftmost node of `T` (`tree.Left()`): `nil` for an empty tree. -/
def leftmost (T : RB GoInterface) (m : Loc) : Prop :=
  (T = .leaf ∧ m = null) ∨
  ∃ (C : Ctx GoInterface) (k : w64) (v : GoInterface) (R : RB GoInterface),
    T = Ctx.plug C (.node m k v .leaf R) ∧ Ctx.pre C = []

/-- `tree.lookup(enc k)`'s result `n`: `k`'s node, or `nil` if `k` is not in `T`. -/
def lookupRes (T : RB GoInterface) (k : w64) (n : Loc) : Prop :=
  (n = null ∧ lookupE T.entries k = none) ∨
  ∃ (C : Ctx GoInterface) (v : GoInterface) (L R : RB GoInterface),
    T = Ctx.plug C (.node n k v L R) ∧ lookupE T.entries k = some v

theorem Rep_plug_node {C : Ctx GoInterface} {n : Loc} {k : w64} {v : GoInterface}
    {L R : RB GoInterface} {p : Loc} (hr : Rep enc h (Ctx.plug C (.node n k v L R)) p) :
    h n = nodeOf enc k v (h n).color' L.loc R.loc (Ctx.parent C p) ∧ n ≠ null ∧
      Rep enc h L n ∧ Rep enc h R n ∧ RepC enc h C n p := by
  rw [Rep_plug] at hr
  obtain ⟨hc, h1, h2, h3, h4⟩ := hr
  exact ⟨h2, h1, h3, h4, hc⟩

theorem mem_plug {C : Ctx GoInterface} {t : RB GoInterface} {x : Loc} (hx : x ∈ t.locs) :
    x ∈ (Ctx.plug C t).locs :=
  (Ctx.plug_locs_perm C t).symm.subset (List.mem_append_left _ hx)

theorem mem_plug_ctx {C : Ctx GoInterface} {t : RB GoInterface} {x : Loc} (hx : x ∈ Ctx.locs C) :
    x ∈ (Ctx.plug C t).locs :=
  (Ctx.plug_locs_perm C t).symm.subset (List.mem_append_right _ hx)

theorem mem_plug_node {C : Ctx GoInterface} {n : Loc} {k : w64} {v : GoInterface}
    {L R : RB GoInterface} : n ∈ (Ctx.plug C (.node n k v L R)).locs :=
  mem_plug (by simp)

/-- The addresses of a plugged tree: the subtree's and the context's are disjoint. -/
theorem nodup_plug {C : Ctx GoInterface} {t : RB GoInterface} (hnd : (Ctx.plug C t).locs.Nodup) :
    t.locs.Nodup ∧ (Ctx.locs C).Nodup ∧ ∀ x ∈ t.locs, x ∉ Ctx.locs C := by
  have h := (Ctx.plug_locs_perm C t).nodup_iff.mp hnd
  rw [List.nodup_append] at h
  refine ⟨h.1, h.2.1, fun x hx hc => ?_⟩
  exact h.2.2 x hx x hc rfl

theorem Rep_loc_eq_null {t : RB GoInterface} {p : Loc} (hr : Rep enc h t p) :
    t.loc = null ↔ t = .leaf := by
  cases t with
  | leaf => simp
  | node n k v l r => simp only [RB.loc_node, reduceCtorEq, iff_false]; exact hr.1

theorem RepC_parent_ne_null {C : Ctx GoInterface} {hole p : Loc} (hr : RepC enc h C hole p)
    (hC : C ≠ []) : Ctx.parent C p ≠ null := by
  cases C with
  | nil => exact absurd rfl hC
  | cons f C =>
    simp only [Ctx.parent_cons]
    obtain ⟨hf, -⟩ := hr
    cases f with
    | L => exact hf.1
    | R => exact hf.1

theorem Ctx.pre_cons_nil {f : Frame GoInterface} {C : Ctx GoInterface} (hp : Ctx.pre (f :: C) = []) :
    (∃ n k v r, f = .L n k v r) ∧ Ctx.pre C = [] := by
  simp only [Ctx.pre, List.append_eq_nil_iff] at hp
  cases f with
  | L n k v r => exact ⟨⟨n, k, v, r, rfl⟩, hp.1⟩
  | R n k v l => simp [Frame.pre] at hp

/-! ### Rotations -/

/-- `x`'s child pointer toward the frame's hole set to `r`. -/
def holeSet (f : Frame GoInterface) (x : Node) (r : Loc) : Node :=
  match f with
  | .L .. => { x with Left' := r }
  | .R .. => { x with Right' := r }

theorem nodeOf_eq_iff (x : Node) (k : w64) (v : GoInterface) (l r p : Loc) :
    x = nodeOf enc k v x.color' l r p ↔
      x.Key' = enc k ∧ x.Value' = v ∧ x.Left' = l ∧ x.Right' = r ∧ x.Parent' = p := by
  cases x
  simp only [nodeOf, Node.mk.injEq, true_and]

/-- The nodes of a rotation's subtree are distinct from each other and from the context's. -/
theorem rot_distinct {C : Ctx GoInterface} {t : RB GoInterface}
    (hnd : (Ctx.plug C t).locs.Nodup) : t.locs.Nodup ∧ ∀ x ∈ t.locs, x ∉ Ctx.locs C :=
  ⟨(nodup_plug hnd).1, (nodup_plug hnd).2.2⟩

/-- The context's addresses, and its innermost frame's node among them. -/
theorem frame_loc_mem {C : Ctx GoInterface} {f : Frame GoInterface} {C' : Ctx GoInterface}
    (hC : C = f :: C') : f.loc ∈ Ctx.locs C := by
  subst hC; cases f <;> simp [Ctx.locs, Frame.locs, Frame.loc]

/-- The context of a rotation, its hole's pointer now `r`: the innermost frame's node is
`holeSet`, the rest unchanged. -/
theorem RepC_rot {C : Ctx GoInterface} {old r : Loc} (h' : Loc → Node)
    (hC : RepC enc h C old null) (hndC : (Ctx.locs C).Nodup)
    (hp : ∀ f C', C = f :: C' → h' f.loc = holeSet f (h f.loc) r)
    (ho : ∀ l ∈ Ctx.locs C, (∀ f C', C = f :: C' → l ≠ f.loc) → h' l = h l) :
    RepC enc h' C r null := by
  cases C with
  | nil => trivial
  | cons f C' =>
    obtain ⟨hf, hC'⟩ := hC
    simp only [Ctx.locs, List.nodup_append] at hndC
    have hfl := hp f C' rfl
    have hfno : ∀ l ∈ Ctx.locs C', l ≠ f.loc := by
      intro l hl e; subst e
      exact hndC.2.2 _ (by cases f <;> simp [Frame.locs, Frame.loc]) _ hl rfl
    refine ⟨?_, RepC_congr h' C' f.loc null (fun l hl => ho l (by simp [Ctx.locs, hl])
      (by intro f' C'' he; cases he; exact hfno l hl)) hC'⟩
    cases f with
    | L fn fk fv fr =>
      obtain ⟨hfn, hhf, hfr⟩ := hf
      have hnd1 := hndC.1
      simp only [Frame.locs, List.nodup_cons] at hnd1
      refine ⟨hfn, ?_, Rep_congr h' fr fn (fun l hl => ho l (by simp [Ctx.locs, Frame.locs, hl])
        (by intro f' C'' he; cases he; intro e; subst e; exact hnd1.1 hl)) hfr⟩
      simp only [Frame.loc, holeSet] at hfl
      rw [hfl, hhf]
    | R fn fk fv fl =>
      obtain ⟨hfn, hhf, hfl'⟩ := hf
      have hnd1 := hndC.1
      simp only [Frame.locs, List.nodup_cons] at hnd1
      refine ⟨hfn, ?_, Rep_congr h' fl fn (fun l hl => ho l (by simp [Ctx.locs, Frame.locs, hl])
        (by intro f' C'' he; cases he; intro e; subst e; exact hnd1.1 hl)) hfl'⟩
      simp only [Frame.loc, holeSet] at hfl
      rw [hfl, hhf]

/-- **A left rotation** (`rotateLeft(n)`), by what the new heap `h'` holds at the nodes it
changes: `n`, `r`, `B`'s root and the parent of `n` (`holeSet`); elsewhere it is `h`. -/
theorem Rep_rotL {C : Ctx GoInterface} {n : Loc} {k : w64} {v : GoInterface}
    {A : RB GoInterface} {r : Loc} {k' : w64} {v' : GoInterface} {B E : RB GoInterface}
    (hrep : Rep enc h (Ctx.plug C (.node n k v A (.node r k' v' B E))) null)
    (hnd : (Ctx.plug C (.node n k v A (.node r k' v' B E))).locs.Nodup)
    (h' : Loc → Node)
    (hn : h' n = nodeOf enc k v (h' n).color' A.loc B.loc r)
    (hr : h' r = nodeOf enc k' v' (h' r).color' n E.loc (Ctx.parent C null))
    (hB : ∀ b kb vb BL BR, B = .node b kb vb BL BR → h' b = { h b with Parent' := n })
    (hp : ∀ f C', C = f :: C' → h' f.loc = holeSet f (h f.loc) r)
    (ho : ∀ l, l ≠ n → l ≠ r → (∀ b kb vb BL BR, B = .node b kb vb BL BR → l ≠ b) →
      (∀ f C', C = f :: C' → l ≠ f.loc) → h' l = h l) :
    Rep enc h' (Ctx.plug C (.node r k' v' (.node n k v A B) E)) null := by
  rw [Rep_plug] at hrep ⊢
  obtain ⟨hC, hnn, hhn, hA, hrn, hhr, hB', hE⟩ := hrep
  obtain ⟨hndt, hndC, hdis⟩ := nodup_plug hnd
  obtain ⟨hnr, hnA, hnB, hnE, hrA, hrB, hrE, hAB, hAE, hBE, -, hBnd, -⟩ := locs_rot_facts hndt
  have hdisC : ∀ x, (x ∈ A.locs ∨ x = n ∨ x = r ∨ x ∈ B.locs ∨ x ∈ E.locs) →
      x ∉ Ctx.locs C := by
    intro x hx
    apply hdis x
    simp only [RB.locs_node, List.mem_cons, List.mem_append]
    grind
  have hBroot : ∀ b kb vb BL BR, B = .node b kb vb BL BR → b ∈ B.locs := by
    intro b kb vb BL BR e; subst e; simp
  -- a node of the subtrees `A`, `E` or below `B`'s root, or of the context but its innermost
  -- frame's node, is unchanged
  have hun : ∀ l, (l ∈ A.locs ∨ l ∈ E.locs ∨
      (∃ b kb vb BL BR, B = .node b kb vb BL BR ∧ (l ∈ BL.locs ∨ l ∈ BR.locs))) →
      h' l = h l := by
    intro l hl
    apply ho l
    · intro e; subst e; rcases hl with hl | hl | ⟨b, kb, vb, BL, BR, rfl, hl⟩
      · exact hnA hl
      · exact hnE hl
      · exact hnB (by simp; grind)
    · intro e; subst e; rcases hl with hl | hl | ⟨b, kb, vb, BL, BR, rfl, hl⟩
      · exact hrA hl
      · exact hrE hl
      · exact hrB (by simp; grind)
    · intro b kb vb BL BR hBe e; subst e hBe
      simp only [RB.locs_node, List.nodup_cons, List.mem_append, not_or] at hBnd
      rcases hl with hl | hl | ⟨b', kb', vb', BL', BR', he, hl⟩
      · exact hAB _ hl (by simp)
      · exact hBE _ (by simp) hl
      · cases he; grind
    · intro f C' hC e; subst e
      apply hdisC _ _ (frame_loc_mem hC)
      rcases hl with hl | hl | ⟨b, kb, vb, BL, BR, rfl, hl⟩
      · exact Or.inl hl
      · exact Or.inr (Or.inr (Or.inr (Or.inr hl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by simp; grind))))
  refine ⟨?_, hrn, ?_, ⟨hnn, ?_, ?_, ?_⟩, ?_⟩
  · -- the context, its hole now `r`
    refine RepC_rot h' hC hndC hp (fun l hl hf => ho l ?_ ?_ ?_ hf)
    · intro e; subst e; exact hdisC _ (Or.inr (Or.inl rfl)) hl
    · intro e; subst e; exact hdisC _ (Or.inr (Or.inr (Or.inl rfl))) hl
    · intro b kb vb BL BR hBe e; subst e
      exact hdisC _ (Or.inr (Or.inr (Or.inr (Or.inl (hBroot _ _ _ _ _ hBe))))) hl
  · simpa using hr
  · simpa using hn
  · exact Rep_congr h' A n (fun l hl => hun l (Or.inl hl)) hA
  · -- B, its root's parent now `n`
    cases B with
    | leaf => trivial
    | node b kb vb BL BR =>
      obtain ⟨hbn, hhb, hBL, hBR⟩ := hB'
      have hb := hB b kb vb BL BR rfl
      refine ⟨hbn, ?_, Rep_congr h' BL b (fun l hl => hun l (Or.inr (Or.inr
          ⟨b, kb, vb, BL, BR, rfl, Or.inl hl⟩))) hBL,
        Rep_congr h' BR b (fun l hl => hun l (Or.inr (Or.inr
          ⟨b, kb, vb, BL, BR, rfl, Or.inr hl⟩))) hBR⟩
      rw [hb, hhb]
  · exact Rep_congr h' E r (fun l hl => hun l (Or.inr (Or.inl hl))) hE

/-- **A right rotation** (`rotateRight(n)`), as `Rep_rotL`. -/
theorem Rep_rotR {C : Ctx GoInterface} {n : Loc} {k : w64} {v : GoInterface} {l : Loc}
    {k' : w64} {v' : GoInterface} {A B E : RB GoInterface}
    (hrep : Rep enc h (Ctx.plug C (.node n k v (.node l k' v' A B) E)) null)
    (hnd : (Ctx.plug C (.node n k v (.node l k' v' A B) E)).locs.Nodup)
    (h' : Loc → Node)
    (hn : h' n = nodeOf enc k v (h' n).color' B.loc E.loc l)
    (hl : h' l = nodeOf enc k' v' (h' l).color' A.loc n (Ctx.parent C null))
    (hB : ∀ b kb vb BL BR, B = .node b kb vb BL BR → h' b = { h b with Parent' := n })
    (hp : ∀ f C', C = f :: C' → h' f.loc = holeSet f (h f.loc) l)
    (ho : ∀ x, x ≠ n → x ≠ l → (∀ b kb vb BL BR, B = .node b kb vb BL BR → x ≠ b) →
      (∀ f C', C = f :: C' → x ≠ f.loc) → h' x = h x) :
    Rep enc h' (Ctx.plug C (.node l k' v' A (.node n k v B E))) null := by
  rw [Rep_plug] at hrep ⊢
  obtain ⟨hC, hnn, hhn, ⟨hln, hhl, hA, hB'⟩, hE⟩ := hrep
  obtain ⟨hndt, hndC, hdis⟩ := nodup_plug hnd
  obtain ⟨hnl, hnA, hnB, hnE, hlA, hlB, hlE, hAB, hAE, hBE, -, hBnd, -⟩ := locs_rotR_facts hndt
  have hdisC : ∀ x, (x ∈ A.locs ∨ x = n ∨ x = l ∨ x ∈ B.locs ∨ x ∈ E.locs) →
      x ∉ Ctx.locs C := by
    intro x hx
    apply hdis x
    simp only [RB.locs_node, List.mem_cons, List.mem_append]
    grind
  have hBroot : ∀ b kb vb BL BR, B = .node b kb vb BL BR → b ∈ B.locs := by
    intro b kb vb BL BR e; subst e; simp
  have hun : ∀ x, (x ∈ A.locs ∨ x ∈ E.locs ∨
      (∃ b kb vb BL BR, B = .node b kb vb BL BR ∧ (x ∈ BL.locs ∨ x ∈ BR.locs))) →
      h' x = h x := by
    intro x hx
    apply ho x
    · intro e; subst e; rcases hx with hx | hx | ⟨b, kb, vb, BL, BR, rfl, hx⟩
      · exact hnA hx
      · exact hnE hx
      · exact hnB (by simp; grind)
    · intro e; subst e; rcases hx with hx | hx | ⟨b, kb, vb, BL, BR, rfl, hx⟩
      · exact hlA hx
      · exact hlE hx
      · exact hlB (by simp; grind)
    · intro b kb vb BL BR hBe e; subst e hBe
      simp only [RB.locs_node, List.nodup_cons, List.mem_append, not_or] at hBnd
      rcases hx with hx | hx | ⟨b', kb', vb', BL', BR', he, hx⟩
      · exact hAB _ hx (by simp)
      · exact hBE _ (by simp) hx
      · cases he; grind
    · intro f C' hC e; subst e
      apply hdisC _ _ (frame_loc_mem hC)
      rcases hx with hx | hx | ⟨b, kb, vb, BL, BR, rfl, hx⟩
      · exact Or.inl hx
      · exact Or.inr (Or.inr (Or.inr (Or.inr hx)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by simp; grind))))
  refine ⟨?_, hln, ?_, Rep_congr h' A l (fun x hx => hun x (Or.inl hx)) hA, ⟨hnn, ?_, ?_, ?_⟩⟩
  · refine RepC_rot h' hC hndC hp (fun x hx hf => ho x ?_ ?_ ?_ hf)
    · intro e; subst e; exact hdisC _ (Or.inr (Or.inl rfl)) hx
    · intro e; subst e; exact hdisC _ (Or.inr (Or.inr (Or.inl rfl))) hx
    · intro b kb vb BL BR hBe e; subst e
      exact hdisC _ (Or.inr (Or.inr (Or.inr (Or.inl (hBroot _ _ _ _ _ hBe))))) hx
  · simpa using hl
  · simpa using hn
  · cases B with
    | leaf => trivial
    | node b kb vb BL BR =>
      obtain ⟨hbn, hhb, hBL, hBR⟩ := hB'
      have hb := hB b kb vb BL BR rfl
      refine ⟨hbn, ?_, Rep_congr h' BL b (fun x hx => hun x (Or.inr (Or.inr
          ⟨b, kb, vb, BL, BR, rfl, Or.inl hx⟩))) hBL,
        Rep_congr h' BR b (fun x hx => hun x (Or.inr (Or.inr
          ⟨b, kb, vb, BL, BR, rfl, Or.inr hx⟩))) hBR⟩
      rw [hb, hhb]
  · exact Rep_congr h' E n (fun x hx => hun x (Or.inr (Or.inl hx))) hE

/-- The innermost frame's node points to the hole by its left child exactly for an `L`
frame, and `holeSet` is the store `replaceNode` makes. -/
theorem holeSet_eq {f : Frame GoInterface} {hole q : Loc} (hf : RepF enc h f hole q)
    (hn : hole ≠ null) (hnf : hole ∉ f.locs) (r : Loc) :
    ((h f.loc).Left' = hole ∨ (h f.loc).Right' = hole) ∧
    holeSet f (h f.loc) r =
      if (h f.loc).Left' = hole then { h f.loc with Left' := r }
      else { h f.loc with Right' := r } := by
  cases f with
  | L fn fk fv fr =>
    obtain ⟨-, hhf, -⟩ := hf
    have hl : (h fn).Left' = hole := by rw [hhf]
    simp only [Frame.loc, holeSet, hl, if_true]
    exact ⟨Or.inl trivial, trivial⟩
  | R fn fk fv fl =>
    obtain ⟨-, hhf, -⟩ := hf
    have hne : fl.loc ≠ hole := by
      intro e
      rcases loc_null_or_mem fl with h0 | h0
      · exact hn (e ▸ h0)
      · exact hnf (by simp [Frame.locs, ← e, h0])
    have hl : (h fn).Left' ≠ hole := by rw [hhf]; exact hne
    have hr : (h fn).Right' = hole := by rw [hhf]
    simp only [Frame.loc, holeSet, hl, hr, if_false]
    exact ⟨Or.inr trivial, trivial⟩

/-- After a rotation below the root (or making `top` the root), the root is black if it was. -/
theorem rootBlack_after {C : Ctx GoInterface} {t t' : RB GoInterface} {h h' : Loc → Node}
    (hrep : Rep enc h (Ctx.plug C t) null) (hdis : ∀ x ∈ t.locs, x ∉ Ctx.locs C)
    (hrb : rootBlack h (Ctx.plug C t)) (hcol : ∀ x, x ∉ t.locs → (h' x).color' = (h x).color')
    (htop : C = [] → (h' t'.loc).color' = true) :
    rootBlack h' (Ctx.plug C t') := by
  cases C with
  | nil => right; exact htop rfl
  | cons f C' =>
    right
    have hm := Ctx.plug_loc_mem (C := f :: C') t (by simp)
    have hm' := Ctx.plug_loc_mem (C := f :: C') t' (by simp)
    have heq : (Ctx.plug (f :: C') t').loc = (Ctx.plug (f :: C') t).loc := Ctx.plug_loc_cons f C' t' t
    rw [heq, hcol _ (fun hx => hdis _ hx hm)]
    rcases hrb with h0 | h0
    · exact absurd h0 (Rep_locs_ne_null _ _ hrep _ (mem_plug_ctx hm))
    · exact h0

theorem rootBlack_congr {h h' : Loc → Node} {T T' : RB GoInterface}
    (hcol : ∀ x, (h' x).color' = (h x).color') (hloc : T'.loc = T.loc) (hrb : rootBlack h T) :
    rootBlack h' T' := by
  unfold rootBlack at *
  rw [hloc, hcol]; exact hrb

/-- The uncle: the grandparent's child that is not the parent, i.e. the grandparent frame's other
subtree. -/
theorem uncle_loc {f : Frame GoInterface} {hole q : Loc} (hf : RepF enc h f hole q)
    (hn : hole ≠ null) (hnf : hole ∉ f.locs) :
    (if hole = (h f.loc).Left' then (h f.loc).Right' else (h f.loc).Left') = f.sib.loc := by
  cases f with
  | L fn fk fv fr =>
    obtain ⟨-, hhf, -⟩ := hf
    have hl : (h fn).Left' = hole := by rw [hhf]
    have hr : (h fn).Right' = fr.loc := by rw [hhf]
    simp only [Frame.loc, Frame.sib, hl, hr, if_true]
  | R fn fk fv fl =>
    obtain ⟨-, hhf, -⟩ := hf
    have hne : hole ≠ fl.loc := by
      intro e
      rcases loc_null_or_mem fl with h0 | h0
      · exact hn (e.trans h0)
      · exact hnf (by simp [Frame.locs, e, h0])
    have hl : (h fn).Left' = fl.loc := by rw [hhf]
    simp only [Frame.loc, Frame.sib, hl, hne, if_false]

theorem parent_recolor (h : Loc → Node) (l : Loc) (c : Bool) (x : Loc) :
    (upd h l { h l with color' := c } x).Parent' = (h x).Parent' := by
  by_cases hx : x = l
  · subst hx; rw [upd_same]
  · rw [upd_ne h l x _ hx]

theorem color_recolor_ne (h : Loc → Node) (l : Loc) (c : Bool) (x : Loc) (hx : x ≠ l) :
    (upd h l { h l with color' := c } x).color' = (h x).color' := by
  rw [upd_ne h l x _ hx]

/-- Replacing the subtree in a context by one at the same address. -/
theorem Rep_plug_replace {C : Ctx GoInterface} {t t' : RB GoInterface} (h' : Loc → Node)
    (hrep : Rep enc h (Ctx.plug C t) null) (hloc : t'.loc = t.loc)
    (hC : ∀ x ∈ Ctx.locs C, h' x = h x) (ht' : Rep enc h' t' (Ctx.parent C null)) :
    Rep enc h' (Ctx.plug C t') null := by
  rw [Rep_plug] at hrep ⊢
  exact ⟨hloc ▸ RepC_congr h' C t.loc null hC hrep.1, ht'⟩

/-- The node `Put` allocates: the key, the value, red, no links. -/
abbrev newNode (enc : w64 → GoInterface) (k : w64) (v : GoInterface) : Node :=
  Node.mk (enc k) v false null null null

/-- The state of `Put`'s search loop (`loop`, `node`, `insertedNode`, the nodes): searching at a
subtree of `T` (the heap unchanged), or the new node `l` linked below `s` (`loop` false; its
parent pointer not set yet). -/
def putLoop (T : RB GoInterface) (h : Loc → Node) (D : List Loc) (k : w64) (v : GoInterface)
    (b : Bool) (nd il : Loc) (hc : Loc → Node) (Dc : List Loc) : Prop :=
  if b then hc = h ∧ Dc = D ∧
    ∃ (C : Ctx GoInterface) (S : RB GoInterface), T = Ctx.plug C S ∧ S ≠ .leaf ∧ Bounds k C ∧
      nd = S.loc
  else ∃ (C : Ctx GoInterface) (s : Loc) (k' : w64) (v' : GoInterface) (X : RB GoInterface)
      (l : Loc), Dc = l :: D ∧ l ∉ D ∧ l ≠ null ∧ il = l ∧ nd = s ∧ Bounds k C ∧
    hc l = newNode enc k v ∧ (∀ x, x ≠ s → x ≠ l → hc x = h x) ∧
    ((T = Ctx.plug C (.node s k' v' .leaf X) ∧ sint.Z k < sint.Z k' ∧
        hc s = nodeOf enc k' v' (h s).color' l X.loc (Ctx.parent C null)) ∨
     (T = Ctx.plug C (.node s k' v' X .leaf) ∧ sint.Z k' < sint.Z k ∧
        hc s = nodeOf enc k' v' (h s).color' X.loc l (Ctx.parent C null)))

end heapfn

/-! ## The points-tos -/

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [redblacktree.Assumptions]

/-- The nodes at the addresses `D`, with the values `h` gives. -/
def ownNodes (h : Loc → Node) : List Loc → IProp GF
  | [] => iprop(True)
  | l :: D => iprop(l ↦ h l ∗ ownNodes h D)

@[simp] theorem ownNodes_nil (h : Loc → Node) : ownNodes (GF := GF) h [] = iprop(True) := rfl
theorem ownNodes_cons (h : Loc → Node) (l : Loc) (D : List Loc) :
    ownNodes (GF := GF) h (l :: D) = iprop(l ↦ h l ∗ ownNodes h D) := rfl

theorem ownNodes_app (h : Loc → Node) (D E : List Loc) :
    ownNodes (GF := GF) h (D ++ E) ⊣⊢ ownNodes h D ∗ ownNodes h E := by
  induction D with
  | nil =>
    simp only [List.nil_append, ownNodes_nil]
    constructor
    · iintro H; isplitr; · itrivial
      iexact H
    · iintro ⟨-, H⟩; iexact H
  | cons l D ih =>
    simp only [List.cons_append, ownNodes_cons]
    constructor
    · iintro ⟨Hl, H⟩
      ihave ⟨HD, HE⟩ := ih.1 $$ H
      iframe
    · iintro ⟨⟨Hl, HD⟩, HE⟩
      iframe Hl
      iapply ih.2
      iframe

theorem ownNodes_perm (h : Loc → Node) {D E : List Loc} (hp : D.Perm E) :
    ownNodes (GF := GF) h D ⊣⊢ ownNodes h E := by
  induction hp with
  | nil => exact .rfl
  | cons x _ ih =>
    simp only [ownNodes_cons]
    constructor
    · iintro ⟨Hx, H⟩; iframe Hx; iapply ih.1; iexact H
    · iintro ⟨Hx, H⟩; iframe Hx; iapply ih.2; iexact H
  | swap x y D =>
    simp only [ownNodes_cons]
    constructor
    · iintro ⟨Hy, Hx, H⟩; iframe
    · iintro ⟨Hx, Hy, H⟩; iframe
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem ownNodes_congr (h h' : Loc → Node) (D : List Loc) (hag : ∀ l ∈ D, h' l = h l) :
    ownNodes (GF := GF) h D ⊢ ownNodes h' D := by
  induction D with
  | nil => exact .rfl
  | cons l D ih =>
    simp only [ownNodes_cons]
    iintro ⟨Hl, H⟩
    rw [hag l (by simp)]
    iframe Hl
    iapply ih (fun x hx => hag x (by simp [hx])); iexact H

/-- Read a node (the nodes unchanged). -/
theorem ownNodes_read (h : Loc → Node) (D : List Loc) (l : Loc) (hl : l ∈ D) :
    ownNodes (GF := GF) h D ⊢ l ↦ h l ∗ (l ↦ h l -∗ ownNodes h D) := by
  induction D with
  | nil => simp at hl
  | cons x D ih =>
    simp only [ownNodes_cons]
    by_cases hx : l = x
    · subst hx
      iintro ⟨Hl, H⟩; iframe Hl; iintro Hl; iframe
    · have hl' : l ∈ D := by simpa [hx] using hl
      iintro ⟨Hx, H⟩
      ihave ⟨Hl, Hback⟩ := ih hl' $$ H
      iframe Hl
      iintro Hl; iframe Hx; iapply Hback; iexact Hl

/-- Read a node whose value is known. -/
theorem ownNodes_read' (h : Loc → Node) (D : List Loc) (l : Loc) (x : Node) (hl : l ∈ D)
    (hx : h l = x) : ownNodes (GF := GF) h D ⊢ l ↦ x ∗ (l ↦ x -∗ ownNodes h D) := by
  rw [← hx]; exact ownNodes_read h D l hl

/-- Take a node out to write it (`D` without duplicates). -/
theorem ownNodes_acc (h : Loc → Node) (D : List Loc) (l : Loc) (hl : l ∈ D) (hnd : D.Nodup) :
    ownNodes (GF := GF) h D ⊢ l ↦ h l ∗ ∀ x, l ↦ x -∗ ownNodes (upd h l x) D := by
  induction D with
  | nil => simp at hl
  | cons y D ih =>
    simp only [ownNodes_cons]
    rw [List.nodup_cons] at hnd
    by_cases hy : l = y
    · subst hy
      iintro ⟨Hl, H⟩; iframe Hl; iintro %x Hx
      rw [upd_same]; iframe Hx
      iapply ownNodes_congr h (upd h l x) D (fun z hz => upd_ne h l z x (fun e => hnd.1 (e ▸ hz)))
      iexact H
    · have hl' : l ∈ D := by simpa [hy] using hl
      iintro ⟨Hy, H⟩
      ihave ⟨Hl, Hback⟩ := ih hl' hnd.2 $$ H
      iframe Hl
      iintro %x Hx
      rw [upd_ne h l y x (Ne.symm hy)]
      iframe Hy; iapply Hback; iexact Hx

/-- Take a node whose value is known out to write it. -/
theorem ownNodes_acc' (h : Loc → Node) (D : List Loc) (l : Loc) (x : Node) (hl : l ∈ D)
    (hnd : D.Nodup) (hx : h l = x) :
    ownNodes (GF := GF) h D ⊢ l ↦ x ∗ ∀ y, l ↦ y -∗ ownNodes (upd h l y) D := by
  rw [← hx]; exact ownNodes_acc h D l hl hnd

/-- A fresh node joins the nodes. -/
theorem ownNodes_insert (h : Loc → Node) (D : List Loc) (l : Loc) (x : Node) (hl : l ∉ D) :
    ownNodes (GF := GF) h D ∗ l ↦ x ⊢ ownNodes (upd h l x) (l :: D) := by
  rw [ownNodes_cons, upd_same]
  iintro ⟨H, Hl⟩
  iframe Hl
  iapply ownNodes_congr h (upd h l x) D (fun y hy => upd_ne h l y x (fun e => hl (e ▸ hy)))
  iexact H

/-- Two full points-tos of one interface-typed location exclude each other (as
`bufio.iface_pointsto_excl`, the main tree's). -/
theorem iface_pointsto_excl (l : Loc) (v1 v2 : GoInterface) :
    (l ↦ v1 : IProp GF) ∗ l ↦ v2 ⊢ False := by
  iintro ⟨H1, H2⟩
  icombine H1 H2 gives %He
  subst He
  ihave H := (typedPointsto_frac_add (GF := GF) l v1 1 1).2 $$ [H1 H2]
  · iframe
  ihave H := typedPointsto_split l v1 _ $$ H
  have hh : (typedPointstoDef (GF := GF) l v1 (DFrac.own (1 + 1)) : IProp GF) ⊢
      heapPointsto l (DFrac.own (1 + 1)) #v1 := .rfl
  ihave H := hh $$ H
  ihave %Hv := heapPointsto_frac_valid l (1 + 1) #v1 $$ H
  exfalso
  rw [Qp.val_add] at Hv
  have h1 : (1 : Qp).val = 1 := rfl
  rw [h1] at Hv
  grind

/-- Two full points-tos of one node exclude each other. -/
theorem node_pointsto_excl (l : Loc) (x y : Node) : (l ↦ x : IProp GF) ∗ l ↦ y ⊢ False := by
  iintro ⟨H1, H2⟩
  iStructNamed H1
  iStructNamedSuffix H2 "'"
  iapply iface_pointsto_excl _ x.Key' y.Key'
  isplitl [Key]
  · iexact Key
  · iexact Key'

/-- A fresh node is not among the nodes. -/
theorem ownNodes_fresh (h : Loc → Node) (D : List Loc) (l : Loc) (x : Node) :
    ownNodes (GF := GF) h D ∗ l ↦ x ⊢ ownNodes h D ∗ l ↦ x ∗ ⌜l ∉ D⌝ := by
  induction D with
  | nil => iintro ⟨H, Hl⟩; iframe; ipureintro; simp
  | cons y D ih =>
    simp only [ownNodes_cons]
    iintro ⟨⟨Hy, H⟩, Hl⟩
    by_cases hy : l = y
    · subst hy
      iexfalso; iapply node_pointsto_excl l x (h l); iframe
    · ihave ⟨H, Hl, %Hd⟩ := ih $$ [H Hl]
      · iframe
      iframe
      ipureintro; simp [hy, Hd]

/-- The tree at `tr`: its root `T`'s, comparator `cmp`; the nodes `D` (`T`'s, without duplicates)
with the values `h`. -/
def treeRaw (tr : Loc) (enc : w64 → GoInterface) (cmp : GoFunc) (T : RB GoInterface)
    (h : Loc → Node) (D : List Loc) : IProp GF :=
  iprop(∃ sz : w64, tr ↦ Tree.mk T.loc sz cmp ∗ ownNodes h D ∗
    ⌜Rep enc h T null ∧ D.Perm T.locs ∧ D.Nodup⌝)

/-- **The tree at `tr` holds the entries `es`** (the file header). -/
def isTree (tr : Loc) (enc : w64 → GoInterface) (es : Entries) : IProp GF :=
  iprop(∃ (cmp : GoFunc) (T : RB GoInterface) (h : Loc → Node) (D : List Loc),
    treeRaw tr enc cmp T h D ∗ cmpOk cmp enc ∗
    ⌜sortedE T.entries ∧ T.entries = es ∧ rootBlack h T⌝)

/-- An iterator's position over `T`, with `rest` still to visit and `cur` its current entry:
before the first (`begin`), past the last (`end`), or at a node (`between`). -/
def iterAt (T : RB GoInterface) (nd : Loc) (pos : w8) (rest : Entries)
    (cur : Option (w64 × GoInterface)) : Prop :=
  (pos = W8 0 ∧ cur = none ∧ rest = T.entries) ∨
  (pos = W8 2 ∧ cur = none ∧ rest = []) ∨
  (pos = W8 1 ∧ ∃ (C : Ctx GoInterface) (k : w64) (v : GoInterface)
      (L R : RB GoInterface), T = Ctx.plug C (.node nd k v L R) ∧ cur = some (k, v) ∧
      rest = R.entries ++ Ctx.post C)

/-- The iterator at `q` over the tree at `tr` (`T`, `h`, `D`), which it owns. -/
def ownIterT (q tr : Loc) (enc : w64 → GoInterface) (cmp : GoFunc) (T : RB GoInterface)
    (h : Loc → Node) (D : List Loc) (rest : Entries) (cur : Option (w64 × GoInterface)) :
    IProp GF :=
  iprop(∃ (nd : Loc) (pos : w8),
    q ↦ Iterator.mk tr nd pos ∗ treeRaw tr enc cmp T h D ∗ ⌜iterAt T nd pos rest cur⌝)

theorem treeRaw_pure (tr : Loc) (enc : w64 → GoInterface) (cmp : GoFunc) (T : RB GoInterface)
    (h : Loc → Node) (D : List Loc) :
    treeRaw (GF := GF) tr enc cmp T h D ⊢
      treeRaw tr enc cmp T h D ∗ ⌜Rep enc h T null ∧ D.Perm T.locs ∧ D.Nodup⌝ := by
  unfold treeRaw
  iintro ⟨%sz, Htr, Hns, %Hp⟩
  isplitl
  · iexists sz; iframe; ipureintro; exact Hp
  · ipureintro; exact Hp

theorem treeRaw_of (tr : Loc) (enc : w64 → GoInterface) (cmp : GoFunc) (T : RB GoInterface)
    (h : Loc → Node) (D : List Loc) (sz : w64) (hp : Rep enc h T null ∧ D.Perm T.locs ∧ D.Nodup) :
    tr ↦ Tree.mk T.loc sz cmp ∗ ownNodes (GF := GF) h D ⊢ treeRaw tr enc cmp T h D := by
  unfold treeRaw
  iintro ⟨Htr, Hns⟩
  iexists sz; iframe; ipureintro; exact hp

theorem isTree_of (tr : Loc) (enc : w64 → GoInterface) (cmp : GoFunc) (T : RB GoInterface)
    (h : Loc → Node) (D : List Loc) (es : Entries)
    (hq : sortedE T.entries ∧ T.entries = es ∧ rootBlack h T) :
    treeRaw (GF := GF) tr enc cmp T h D ∗ cmpOk cmp enc ⊢ isTree tr enc es := by
  unfold isTree
  iintro ⟨Hraw, #Hcmp⟩
  iexists cmp, T, h, D
  isplitl [Hraw]
  · iexact Hraw
  isplitr
  · iexact Hcmp
  ipureintro; exact hq

end iris

/-! ## Go's boolean conditions -/

section helpers
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

include hG sem in
theorem not_of_not_decide_val {P : Prop} [Decidable P] (h : (#(!decide P) : val) = #true) : ¬P := by
  haveI : go.BasicIntoValInj := inferInstance
  intro hp
  simp only [hp, _root_.decide_true, Bool.not_true] at h
  exact Bool.false_ne_true (go.intoVal_inj h)

include hG sem in
theorem of_not_not_decide_val {P : Prop} [Decidable P] (h : ¬ (#(!decide P) : val) = #true) : P := by
  revert h; by_cases hp : P <;> simp [hp]

include hG sem in
theorem not_decide_val_false {P : Prop} [Decidable P] (hp : P) : (#(!decide P) : val) = #false := by
  simp [hp]

end helpers

end Perennial.github_com.emirpasic.gods.trees.redblacktree
