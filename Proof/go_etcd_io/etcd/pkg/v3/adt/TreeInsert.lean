/-
The pure model of the interval tree's `Insert` (`pkg/v3/adt`): a tree with a hole (`RbCtx`, a
path from the root to a subtree, `plug`), the descent (`RbT.insertBST`, mirroring `Insert`'s:
left when the new interval is below the node's, right otherwise) with its in-order list
(`inorder_insertBST`: `ivtInsert`), the `max` augmentation under a change of shape
(`maxEnd_eq_of_inorder`: a subtree's max is a function of its entries), and `insertFixup`'s loop
invariant (`FixInv`, CLRS 13.3's: the tree is red-black but for `z` red under a red parent)
preserved by each of the loop's cases (`fix_red_*`, `fix_black_*`) and giving a red-black tree
at the exit (`fixInv_exit`). Lean-first; see `notes/decisions.md`, "The watchable store: the
plan, the interval tree's contract".
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.adt.Tree

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace adt

/-! ## A tree with a hole -/

/-- A path from the root to a hole, innermost frame first: the hole is the left child of a node
(`inL c p e r`: the node's colour, its own context, its entry, its right subtree) or its right
child (`inR`). -/
inductive RbCtx (E : Type) where
  | top : RbCtx E
  | inL (c : RbColor) (p : RbCtx E) (e : E) (r : RbT E) : RbCtx E
  | inR (c : RbColor) (l : RbT E) (e : E) (p : RbCtx E) : RbCtx E

/-- `RB-INSERT`'s last step on the root: colour it black. -/
def RbT.blacken {E : Type} : RbT E → RbT E
  | .leaf => .leaf
  | .node _ l e r => .node .black l e r

namespace RbCtx
variable {E : Type}

/-- The tree with `t` in the hole. -/
def plug : RbCtx E → RbT E → RbT E
  | top, t => t
  | inL c p e r, t => plug p (.node c t e r)
  | inR c l e p, t => plug p (.node c l e t)

@[simp] theorem plug_top (t : RbT E) : plug .top t = t := rfl
@[simp] theorem plug_inL (c : RbColor) (p : RbCtx E) (e : E) (r t : RbT E) :
    plug (.inL c p e r) t = plug p (.node c t e r) := rfl
@[simp] theorem plug_inR (c : RbColor) (l : RbT E) (e : E) (p : RbCtx E) (t : RbT E) :
    plug (.inR c l e p) t = plug p (.node c l e t) := rfl

theorem inorder_plug_congr : ∀ (C : RbCtx E) {t1 t2 : RbT E}, t1.inorder = t2.inorder →
    (plug C t1).inorder = (plug C t2).inorder
  | top, _, _, h => h
  | inL _ p _ _, _, _, h => inorder_plug_congr p (by simp [h])
  | inR _ _ _ p, _, _, h => inorder_plug_congr p (by simp [h])

/-- A node plugged in is under a node. -/
theorem plug_node : ∀ (C : RbCtx E) (c : RbColor) (l : RbT E) (e : E) (r : RbT E),
    ∃ c' l' e' r', plug C (.node c l e r) = .node c' l' e' r'
  | top, c, l, e, r => ⟨c, l, e, r, rfl⟩
  | inL c' p e' r', c, l, e, r => plug_node p c' (.node c l e r) e' r'
  | inR c' l' e' p, c, l, e, r => plug_node p c' l' e' (.node c l e r)

/-- The colour of the hole's parent (the sentinel's, black, at the top). -/
def color : RbCtx E → RbColor
  | top => .black
  | inL c _ _ _ => c
  | inR c _ _ _ => c

/-- Below the root, the root's colour does not depend on the hole. -/
theorem color_plug_congr : ∀ (C : RbCtx E) (t1 t2 : RbT E), C ≠ top →
    (plug C t1).color = (plug C t2).color
  | top, _, _, h => absurd rfl h
  | inL c p e r, t1, t2, _ => by
    by_cases hp : p = top
    · subst hp; rfl
    · exact color_plug_congr p _ _ hp
  | inR c l e p, t1, t2, _ => by
    by_cases hp : p = top
    · subst hp; rfl
    · exact color_plug_congr p _ _ hp

/-! ## The red-black invariant through a context -/

/-- Plugging a subtree of black height `h` gives consistent black heights. -/
def bhOk : RbCtx E → Nat → Prop
  | top, _ => True
  | inL c p _ r, h => r.blackHeight = some h ∧ p.bhOk (h + if c = .black then 1 else 0)
  | inR c l _ p, h => l.blackHeight = some h ∧ p.bhOk (h + if c = .black then 1 else 0)

/-- No red node has a red child, given the hole's colour `ch`. -/
def redOk : RbCtx E → RbColor → Prop
  | top, _ => True
  | inL c p _ r, ch => (c = .red → ch = .black ∧ r.color = .black) ∧ r.redOk ∧ p.redOk c
  | inR c l _ p, ch => (c = .red → l.color = .black ∧ ch = .black) ∧ l.redOk ∧ p.redOk c

/-- `redOk` but for the hole's parent, which may be red over a red hole. -/
def redOkX : RbCtx E → Prop
  | top => True
  | inL c p _ r => (c = .red → r.color = .black) ∧ r.redOk ∧ p.redOk c
  | inR c l _ p => (c = .red → l.color = .black) ∧ l.redOk ∧ p.redOk c

end RbCtx

namespace RbT
variable {E : Type}

theorem blackHeight_node (c : RbColor) (l : RbT E) (e : E) (r : RbT E) (k : Nat) :
    (node c l e r).blackHeight = some k ↔
      ∃ h, l.blackHeight = some h ∧ r.blackHeight = some h ∧
        k = h + if c = .black then 1 else 0 := by
  simp only [blackHeight]
  cases hl : l.blackHeight with
  | none => simp
  | some a =>
    cases hr : r.blackHeight with
    | none => simp
    | some b =>
      simp only
      by_cases hab : a = b
      · subst hab
        rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)]
        constructor
        · intro h; exact ⟨a, rfl, rfl, (Option.some.inj h).symm⟩
        · rintro ⟨h, h1, -, rfl⟩; cases h1; rfl
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hab)]
        constructor
        · intro h; cases h
        · rintro ⟨h, h1, h2, -⟩; cases h1; cases h2; exact absurd rfl hab

theorem blackHeight_node_of (c : RbColor) (l : RbT E) (e : E) (r : RbT E) (h : Nat)
    (hl : l.blackHeight = some h) (hr : r.blackHeight = some h) :
    (node c l e r).blackHeight = some (h + if c = .black then 1 else 0) :=
  (blackHeight_node c l e r _).2 ⟨h, hl, hr, rfl⟩

@[simp] theorem blackHeight_leaf : (leaf : RbT E).blackHeight = some 0 := rfl
@[simp] theorem color_leaf : (leaf : RbT E).color = .black := rfl
@[simp] theorem color_node (c : RbColor) (l : RbT E) (e : E) (r : RbT E) :
    (node c l e r).color = c := rfl
@[simp] theorem redOk_leaf : (leaf : RbT E).redOk := trivial
theorem redOk_node (c : RbColor) (l : RbT E) (e : E) (r : RbT E) :
    (node c l e r).redOk ↔
      (c = .red → l.color = .black ∧ r.color = .black) ∧ l.redOk ∧ r.redOk := Iff.rfl

theorem inorder_blacken (t : RbT E) : t.blacken.inorder = t.inorder := by
  cases t <;> rfl

theorem color_blacken (t : RbT E) : t.blacken.color = .black := by
  cases t <;> rfl

theorem redOk_blacken (t : RbT E) (h : t.redOk) : t.blacken.redOk := by
  cases t with
  | leaf => trivial
  | node c l e r =>
    rw [redOk_node] at h
    exact (redOk_node _ _ _ _).2 ⟨fun h' => absurd h' (by decide), h.2⟩

theorem blackHeight_blacken (t : RbT E) (h : t.blackHeight.isSome) :
    t.blacken.blackHeight.isSome := by
  cases t with
  | leaf => rfl
  | node c l e r =>
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 h
    obtain ⟨h', hl, hr, -⟩ := (blackHeight_node c l e r k).1 hk
    rw [blacken, blackHeight_node_of _ _ _ _ h' hl hr]; rfl

end RbT

namespace RbCtx
variable {E : Type}

theorem bh_plug : ∀ (C : RbCtx E) (t : RbT E) (h : Nat), t.blackHeight = some h → C.bhOk h →
    (plug C t).blackHeight.isSome
  | top, t, h, ht, _ => by simp [ht]
  | inL c p e r, t, h, ht, hC => by
    obtain ⟨hr, hp⟩ := hC
    exact bh_plug p _ _ (RbT.blackHeight_node_of c t e r h ht hr) hp
  | inR c l e p, t, h, ht, hC => by
    obtain ⟨hl, hp⟩ := hC
    exact bh_plug p _ _ (RbT.blackHeight_node_of c l e t h hl ht) hp

theorem bhOk_of_plug : ∀ (C : RbCtx E) (t : RbT E), (plug C t).blackHeight.isSome →
    ∃ h, t.blackHeight = some h ∧ C.bhOk h
  | top, t, ht => by
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 ht
    exact ⟨k, hk, trivial⟩
  | inL c p e r, t, ht => by
    obtain ⟨k, hk, hp⟩ := bhOk_of_plug p _ ht
    obtain ⟨h, hl, hr, rfl⟩ := (RbT.blackHeight_node c t e r k).1 hk
    exact ⟨h, hl, hr, hp⟩
  | inR c l e p, t, ht => by
    obtain ⟨k, hk, hp⟩ := bhOk_of_plug p _ ht
    obtain ⟨h, hl, hr, rfl⟩ := (RbT.blackHeight_node c l e t k).1 hk
    exact ⟨h, hr, hl, hp⟩

theorem redOk_plug : ∀ (C : RbCtx E) (t : RbT E),
    (plug C t).redOk ↔ t.redOk ∧ C.redOk t.color
  | top, t => by simp [redOk]
  | inL c p e r, t => by
    rw [plug_inL, redOk_plug p, RbT.redOk_node]
    simp only [redOk, RbT.color_node]
    exact ⟨fun ⟨⟨a, b, c'⟩, d⟩ => ⟨b, a, c', d⟩, fun ⟨b, a, c', d⟩ => ⟨⟨a, b, c'⟩, d⟩⟩
  | inR c l e p, t => by
    rw [plug_inR, redOk_plug p, RbT.redOk_node]
    simp only [redOk, RbT.color_node]
    exact ⟨fun ⟨⟨a, b, c'⟩, d⟩ => ⟨c', a, b, d⟩, fun ⟨c', a, b, d⟩ => ⟨⟨a, b, c'⟩, d⟩⟩

theorem redOkX_of_redOk (C : RbCtx E) (ch : RbColor) (h : C.redOk ch) : C.redOkX := by
  cases C with
  | top => trivial
  | inL c p e r => exact ⟨fun hc => (h.1 hc).2, h.2⟩
  | inR c l e p => exact ⟨fun hc => (h.1 hc).1, h.2⟩

theorem redOk_of_redOkX (C : RbCtx E) (ch : RbColor) (h : C.redOkX) (hc : C.color = .black) :
    C.redOk ch := by
  cases C with
  | top => trivial
  | inL c p e r =>
    simp only [color] at hc; subst hc
    exact ⟨fun h' => absurd h' (by decide), h.2⟩
  | inR c l e p =>
    simp only [color] at hc; subst hc
    exact ⟨fun h' => absurd h' (by decide), h.2⟩

/-! ## `insertFixup`'s loop invariant -/

/-- CLRS 13.3's invariant of `RB-INSERT-FIXUP` at `z`, the subtree `t` in the context `C`: `z`
is red with black children (`t.redOk`); the black heights are consistent; the only red-red
violation is `z` under its parent (`redOkX`); the root is black unless `z` is the root. -/
def FixInv (C : RbCtx E) (t : RbT E) : Prop :=
  t.color = .red ∧ t.redOk ∧ (∃ h, t.blackHeight = some h ∧ C.bhOk h) ∧ C.redOkX ∧
    (C = .top ∨ (plug C t).color = .black)

/-- **The invariant holds for the new red leaf** of a red-black tree. -/
theorem fixInv_start (C : RbCtx E) (z : E) (hr : (plug C .leaf).redOk)
    (hb : (plug C .leaf).blackHeight.isSome) (hc : (plug C .leaf).color = .black) :
    FixInv C (.node .red .leaf z .leaf) := by
  refine ⟨rfl, ⟨fun _ => ⟨rfl, rfl⟩, trivial, trivial⟩, ?_, ?_, ?_⟩
  · obtain ⟨h, h0, hC⟩ := bhOk_of_plug C .leaf hb
    simp only [RbT.blackHeight_leaf, Option.some.injEq] at h0
    subst h0
    exact ⟨0, rfl, hC⟩
  · exact redOkX_of_redOk C _ ((redOk_plug C .leaf).1 hr).2
  · by_cases hC : C = .top
    · exact Or.inl hC
    · exact Or.inr ((color_plug_congr C _ _ hC).trans hc)

/-- **The exit**: the parent black (or none), the tree with its root blackened is red-black. -/
theorem fixInv_exit (C : RbCtx E) (t : RbT E) (h : FixInv C t) (hc : C.color = .black) :
    (plug C t).blacken.redOk ∧ (plug C t).blacken.blackHeight.isSome ∧
      (plug C t).blacken.color = .black := by
  obtain ⟨-, htr, ⟨k, hk, hC⟩, hx, -⟩ := h
  refine ⟨RbT.redOk_blacken _ ((redOk_plug C t).2 ⟨htr, redOk_of_redOkX C _ hx hc⟩),
    RbT.blackHeight_blacken _ (bh_plug C t k hk hC), RbT.color_blacken _⟩

/-- A red parent is not the root. -/
theorem fixInv_inL_top {c : RbColor} {e : E} {r t : RbT E} (h : FixInv (.inL c .top e r) t)
    (hc : c = .red) : False := by
  obtain ⟨-, -, -, -, h | h⟩ := h
  · cases h
  · subst hc; cases h

theorem fixInv_inR_top {c : RbColor} {l : RbT E} {e : E} {t : RbT E}
    (h : FixInv (.inR c l e .top) t) (hc : c = .red) : False := by
  obtain ⟨-, -, -, -, h | h⟩ := h
  · cases h
  · subst hc; cases h

theorem fixInv_red (C : RbCtx E) (t : RbT E) (h : FixInv C t) :
    ∃ l z r, t = .node .red l z r :=
  match t, h.1 with
  | .node .red l z r, _ => ⟨l, z, r, rfl⟩

/-- The root condition after a step at the grandparent `CG`'s hole. -/
theorem root_step (CG : RbCtx E) (g g' : RbT E) (h : (plug CG g).color = .black) :
    CG = .top ∨ (plug CG g').color = .black := by
  by_cases hCG : CG = .top
  · exact Or.inl hCG
  · exact Or.inr ((color_plug_congr CG _ _ hCG).trans h)

/-- The black-uncle cases' root condition: the new subtree's root is black. -/
theorem root_black (CG : RbCtx E) (g g' : RbT E) (hg : g'.color = .black)
    (h : (plug CG g).color = .black) : (plug CG g').color = .black := by
  by_cases hCG : CG = .top
  · subst hCG; exact hg
  · exact (color_plug_congr CG _ _ hCG).trans h

/-- The root condition of a context below a grandparent. -/
theorem root_of {C : RbCtx E} {t : RbT E} (h : C = .top ∨ (plug C t).color = .black)
    (CG : RbCtx E) {g : RbT E} (hp : plug C t = plug CG g) (hC : C ≠ .top) :
    (plug CG g).color = .black := by
  rcases h with h | h
  · exact absurd h hC
  · rw [← hp]; exact h

section cases
variable {cg : RbColor} {CG : RbCtx E} {ge pe ue : E} {u ul ur s1 t : RbT E}

/-- The grandparent of a red parent is black. -/
theorem cg_black {CP : RbCtx E} (hCP : CP.redOk .red) (hCPe : CP = .inL cg CG ge u ∨
    CP = .inR cg u ge CG) : cg = .black := by
  rcases hCPe with rfl | rfl <;> cases cg <;> first | rfl | exact absurd (hCP.1 rfl) (by simp)

/-- Case 1, the uncle red (`z` left of `P`, `P` left of `G`): recolour, `z` moves up to `G`. -/
theorem fix_red_LL (h : FixInv (.inL .red (.inL cg CG ge (.node .red ul ue ur)) pe s1) t) :
    FixInv CG (.node .red (.node .black t pe s1) ge (.node .black ul ue ur)) ∧
      (plug CG (.node .red (.node .black t pe s1) ge (.node .black ul ue ur))).inorder =
        (plug (.inL .red (.inL cg CG ge (.node .red ul ue ur)) pe s1) t).inorder := by
  obtain ⟨htc, htr, ⟨k, hk, hs1, hu, hG⟩, ⟨hs1c, hs1r, hCP⟩, hroot⟩ := h
  have hcg : cg = .black := cg_black hCP (Or.inl rfl)
  subst hcg
  obtain ⟨-, hulr, hurr⟩ := hCP.2.1
  obtain ⟨k', hk1, hk2, hk'⟩ := (RbT.blackHeight_node _ _ _ _ _).1 hu
  have hkk : k' = k := by simp at hk'; omega
  rw [hkk] at hk1 hk2
  refine ⟨⟨rfl, ?_, ⟨k + 1 + 0, ?_, by simpa using hG⟩, redOkX_of_redOk _ _ hCP.2.2, ?_⟩, ?_⟩
  · exact ⟨fun _ => ⟨rfl, rfl⟩, ⟨fun h => absurd h (by decide), htr, hs1r⟩,
      ⟨fun h => absurd h (by decide), hulr, hurr⟩⟩
  · rw [RbT.blackHeight_node_of _ _ _ _ (k + 1) (RbT.blackHeight_node_of _ _ _ _ k hk hs1)
      (RbT.blackHeight_node_of _ _ _ _ k hk1 hk2)]
    simp
  · exact root_step CG _ _ (root_of hroot CG rfl (by simp))
  · exact inorder_plug_congr CG (by simp)

/-- Case 1 with `z` right of `P` (`P` left of `G`). -/
theorem fix_red_RL (h : FixInv (.inR .red s1 pe (.inL cg CG ge (.node .red ul ue ur))) t) :
    FixInv CG (.node .red (.node .black s1 pe t) ge (.node .black ul ue ur)) ∧
      (plug CG (.node .red (.node .black s1 pe t) ge (.node .black ul ue ur))).inorder =
        (plug (.inR .red s1 pe (.inL cg CG ge (.node .red ul ue ur))) t).inorder := by
  obtain ⟨htc, htr, ⟨k, hk, hs1, hu, hG⟩, ⟨hs1c, hs1r, hCP⟩, hroot⟩ := h
  have hcg : cg = .black := cg_black hCP (Or.inl rfl)
  subst hcg
  obtain ⟨-, hulr, hurr⟩ := hCP.2.1
  obtain ⟨k', hk1, hk2, hk'⟩ := (RbT.blackHeight_node _ _ _ _ _).1 hu
  have hkk : k' = k := by simp at hk'; omega
  rw [hkk] at hk1 hk2
  refine ⟨⟨rfl, ?_, ⟨k + 1 + 0, ?_, by simpa using hG⟩, redOkX_of_redOk _ _ hCP.2.2, ?_⟩, ?_⟩
  · exact ⟨fun _ => ⟨rfl, rfl⟩, ⟨fun h => absurd h (by decide), hs1r, htr⟩,
      ⟨fun h => absurd h (by decide), hulr, hurr⟩⟩
  · rw [RbT.blackHeight_node_of _ _ _ _ (k + 1) (RbT.blackHeight_node_of _ _ _ _ k hs1 hk)
      (RbT.blackHeight_node_of _ _ _ _ k hk1 hk2)]
    simp
  · exact root_step CG _ _ (root_of hroot CG rfl (by simp))
  · exact inorder_plug_congr CG (by simp)

/-- Case 1 with `P` right of `G` (`z` left of `P`). -/
theorem fix_red_LR (h : FixInv (.inL .red (.inR cg (.node .red ul ue ur) ge CG) pe s1) t) :
    FixInv CG (.node .red (.node .black ul ue ur) ge (.node .black t pe s1)) ∧
      (plug CG (.node .red (.node .black ul ue ur) ge (.node .black t pe s1))).inorder =
        (plug (.inL .red (.inR cg (.node .red ul ue ur) ge CG) pe s1) t).inorder := by
  obtain ⟨htc, htr, ⟨k, hk, hs1, hu, hG⟩, ⟨hs1c, hs1r, hCP⟩, hroot⟩ := h
  have hcg : cg = .black := cg_black hCP (Or.inr rfl)
  subst hcg
  obtain ⟨-, hulr, hurr⟩ := hCP.2.1
  obtain ⟨k', hk1, hk2, hk'⟩ := (RbT.blackHeight_node _ _ _ _ _).1 hu
  have hkk : k' = k := by simp at hk'; omega
  rw [hkk] at hk1 hk2
  refine ⟨⟨rfl, ?_, ⟨k + 1 + 0, ?_, by simpa using hG⟩, redOkX_of_redOk _ _ hCP.2.2, ?_⟩, ?_⟩
  · exact ⟨fun _ => ⟨rfl, rfl⟩, ⟨fun h => absurd h (by decide), hulr, hurr⟩,
      ⟨fun h => absurd h (by decide), htr, hs1r⟩⟩
  · rw [RbT.blackHeight_node_of _ _ _ _ (k + 1) (RbT.blackHeight_node_of _ _ _ _ k hk1 hk2)
      (RbT.blackHeight_node_of _ _ _ _ k hk hs1)]
    simp
  · exact root_step CG _ _ (root_of hroot CG rfl (by simp))
  · exact inorder_plug_congr CG (by simp)

/-- Case 1 with `z` right of `P`, `P` right of `G`. -/
theorem fix_red_RR (h : FixInv (.inR .red s1 pe (.inR cg (.node .red ul ue ur) ge CG)) t) :
    FixInv CG (.node .red (.node .black ul ue ur) ge (.node .black s1 pe t)) ∧
      (plug CG (.node .red (.node .black ul ue ur) ge (.node .black s1 pe t))).inorder =
        (plug (.inR .red s1 pe (.inR cg (.node .red ul ue ur) ge CG)) t).inorder := by
  obtain ⟨htc, htr, ⟨k, hk, hs1, hu, hG⟩, ⟨hs1c, hs1r, hCP⟩, hroot⟩ := h
  have hcg : cg = .black := cg_black hCP (Or.inr rfl)
  subst hcg
  obtain ⟨-, hulr, hurr⟩ := hCP.2.1
  obtain ⟨k', hk1, hk2, hk'⟩ := (RbT.blackHeight_node _ _ _ _ _).1 hu
  have hkk : k' = k := by simp at hk'; omega
  rw [hkk] at hk1 hk2
  refine ⟨⟨rfl, ?_, ⟨k + 1 + 0, ?_, by simpa using hG⟩, redOkX_of_redOk _ _ hCP.2.2, ?_⟩, ?_⟩
  · exact ⟨fun _ => ⟨rfl, rfl⟩, ⟨fun h => absurd h (by decide), hulr, hurr⟩,
      ⟨fun h => absurd h (by decide), hs1r, htr⟩⟩
  · rw [RbT.blackHeight_node_of _ _ _ _ (k + 1) (RbT.blackHeight_node_of _ _ _ _ k hk1 hk2)
      (RbT.blackHeight_node_of _ _ _ _ k hs1 hk)]
    simp
  · exact root_step CG _ _ (root_of hroot CG rfl (by simp))
  · exact inorder_plug_congr CG (by simp)

/-- Case 3, the uncle black, `z` left of `P` left of `G`: `P` black, `G` red, rotate `G` right;
`z` stays, under the (black) `P`. -/
theorem fix_black_LL (h : FixInv (.inL .red (.inL cg CG ge u) pe s1) t) (hu : u.color = .black) :
    FixInv (.inL .black CG pe (.node .red s1 ge u)) t ∧
      (plug (.inL .black CG pe (.node .red s1 ge u)) t).inorder =
        (plug (.inL .red (.inL cg CG ge u) pe s1) t).inorder := by
  obtain ⟨htc, htr, ⟨k, hk, hs1, hub, hG⟩, ⟨hs1c, hs1r, hCP⟩, hroot⟩ := h
  have hcg : cg = .black := cg_black hCP (Or.inl rfl)
  subst hcg
  simp at hub hG
  refine ⟨⟨htc, htr, ⟨k, hk, ?_, by simpa using hG⟩, ⟨fun h => absurd h (by decide),
    ⟨fun _ => ⟨hs1c rfl, hu⟩, hs1r, hCP.2.1⟩, hCP.2.2⟩, ?_⟩, ?_⟩
  · rw [RbT.blackHeight_node_of _ _ _ _ k hs1 hub]; simp
  · exact Or.inr (root_black CG _ _ rfl (root_of hroot CG rfl (by simp)))
  · exact inorder_plug_congr CG (by simp)

/-- Case 2 then 3, `z` right of `P` left of `G`: rotate `P` left, then as `fix_black_LL` with
`z`'s old node on top; `z` moves to `P`, under it. -/
theorem fix_black_RL {tl tr : RbT E} {ze : E}
    (h : FixInv (.inR .red s1 pe (.inL cg CG ge u)) (.node .red tl ze tr))
    (hu : u.color = .black) :
    FixInv (.inL .black CG ze (.node .red tr ge u)) (.node .red s1 pe tl) ∧
      (plug (.inL .black CG ze (.node .red tr ge u)) (.node .red s1 pe tl)).inorder =
        (plug (.inR .red s1 pe (.inL cg CG ge u)) (.node .red tl ze tr)).inorder := by
  obtain ⟨-, htr, ⟨k, hk, hs1, hub, hG⟩, ⟨hs1c, hs1r, hCP⟩, hroot⟩ := h
  have hcg : cg = .black := cg_black hCP (Or.inl rfl)
  subst hcg
  obtain ⟨k', hk1, hk2, hk'⟩ := (RbT.blackHeight_node _ _ _ _ _).1 hk
  simp at hk' hub hG; subst hk'
  obtain ⟨htlr, htl, htrr⟩ := htr
  obtain ⟨htlc, htrc⟩ := htlr rfl
  refine ⟨⟨rfl, ⟨fun _ => ⟨hs1c rfl, htlc⟩, hs1r, htl⟩, ⟨k, ?_, ?_, by simpa using hG⟩,
    ⟨fun h => absurd h (by decide), ⟨fun _ => ⟨htrc, hu⟩, htrr, hCP.2.1⟩, hCP.2.2⟩, ?_⟩, ?_⟩
  · rw [RbT.blackHeight_node_of _ _ _ _ k hs1 hk1]; simp
  · rw [RbT.blackHeight_node_of _ _ _ _ k hk2 hub]; simp
  · exact Or.inr (root_black CG _ _ rfl (root_of hroot CG rfl (by simp)))
  · exact inorder_plug_congr CG (by simp)

/-- Case 2 then 3, mirrored: `z` left of `P` right of `G`. -/
theorem fix_black_LR {tl tr : RbT E} {ze : E}
    (h : FixInv (.inL .red (.inR cg u ge CG) pe s1) (.node .red tl ze tr))
    (hu : u.color = .black) :
    FixInv (.inR .black (.node .red u ge tl) ze CG) (.node .red tr pe s1) ∧
      (plug (.inR .black (.node .red u ge tl) ze CG) (.node .red tr pe s1)).inorder =
        (plug (.inL .red (.inR cg u ge CG) pe s1) (.node .red tl ze tr)).inorder := by
  obtain ⟨-, htr, ⟨k, hk, hs1, hub, hG⟩, ⟨hs1c, hs1r, hCP⟩, hroot⟩ := h
  have hcg : cg = .black := cg_black hCP (Or.inr rfl)
  subst hcg
  obtain ⟨k, hk1, hk2, hk⟩ := (RbT.blackHeight_node _ _ _ _ _).1 hk
  simp at hk hub hG; subst hk
  obtain ⟨htlr, htl, htrr⟩ := htr
  obtain ⟨htlc, htrc⟩ := htlr rfl
  refine ⟨⟨rfl, ⟨fun _ => ⟨htrc, hs1c rfl⟩, htrr, hs1r⟩, ⟨k, ?_, ?_, by simpa using hG⟩,
    ⟨fun h => absurd h (by decide), ⟨fun _ => ⟨hu, htlc⟩, hCP.2.1, htl⟩, hCP.2.2⟩, ?_⟩, ?_⟩
  · rw [RbT.blackHeight_node_of _ _ _ _ k hk2 hs1]; simp
  · rw [RbT.blackHeight_node_of _ _ _ _ k hub hk1]; simp
  · exact Or.inr (root_black CG _ _ rfl (root_of hroot CG rfl (by simp)))
  · exact inorder_plug_congr CG (by simp)

/-- Case 3 mirrored: `z` right of `P` right of `G`: rotate `G` left. -/
theorem fix_black_RR (h : FixInv (.inR .red s1 pe (.inR cg u ge CG)) t) (hu : u.color = .black) :
    FixInv (.inR .black (.node .red u ge s1) pe CG) t ∧
      (plug (.inR .black (.node .red u ge s1) pe CG) t).inorder =
        (plug (.inR .red s1 pe (.inR cg u ge CG)) t).inorder := by
  obtain ⟨htc, htr, ⟨k, hk, hs1, hub, hG⟩, ⟨hs1c, hs1r, hCP⟩, hroot⟩ := h
  have hcg : cg = .black := cg_black hCP (Or.inr rfl)
  subst hcg
  simp at hub hG
  refine ⟨⟨htc, htr, ⟨k, hk, ?_, by simpa using hG⟩, ⟨fun h => absurd h (by decide),
    ⟨fun _ => ⟨hu, hs1c rfl⟩, hCP.2.1, hs1r⟩, hCP.2.2⟩, ?_⟩, ?_⟩
  · rw [RbT.blackHeight_node_of _ _ _ _ k hub hs1]; simp
  · exact Or.inr (root_black CG _ _ rfl (root_of hroot CG rfl (by simp)))
  · exact inorder_plug_congr CG (by simp)

end cases

end RbCtx

/-! ## The descent -/

section entries
variable [ext : FfiSyntax]

/-- `Insert`'s descent and link: the new entry as a red leaf where the descent ends (left when
its interval is below the node's, by begin then end; right otherwise). -/
def RbT.insertBST (z : Entry) : RbT Entry → RbT Entry
  | .leaf => .node .red .leaf z .leaf
  | .node c l e r =>
    if ivlLt z.1 e.1 then .node c (l.insertBST z) e r else .node c l e (r.insertBST z)

theorem ivtInsert_append_left (z e : Entry) (B : List Entry) (h : ivlLt z.1 e.1) :
    ∀ A : List Entry, ivtInsert z (A ++ e :: B) = ivtInsert z A ++ e :: B
  | [] => by simp [ivtInsert, h]
  | w :: ws => by
    simp only [List.cons_append, ivtInsert]
    split
    · rfl
    · rw [ivtInsert_append_left z e B h ws]; rfl

theorem ivtInsert_append_right (z e : Entry) (B : List Entry) (h : ¬ ivlLt z.1 e.1) :
    ∀ A : List Entry, (∀ w ∈ A, ¬ ivlLt z.1 w.1) →
      ivtInsert z (A ++ e :: B) = A ++ e :: ivtInsert z B
  | [], _ => by simp [ivtInsert, h]
  | w :: ws, hA => by
    simp only [List.cons_append, ivtInsert]
    rw [ite_eq_right_of_eq_false _ _ (eq_false (hA w List.mem_cons_self)),
      ivtInsert_append_right z e B h ws (fun w' hw' => hA w' (List.mem_cons_of_mem _ hw'))]

/-- **The descent inserts in the tree's order.** -/
theorem inorder_insertBST (z : Entry) : ∀ (t : RbT Entry), IvSorted t.inorder →
    (t.insertBST z).inorder = ivtInsert z t.inorder
  | .leaf, _ => rfl
  | .node c l e r, hs => by
    obtain ⟨hl, hr, hle, -⟩ := ivSorted_node hs
    simp only [RbT.insertBST]
    split
    · rename_i h
      rw [RbT.inorder_node, RbT.inorder_node, inorder_insertBST z l hl,
        ivtInsert_append_left z e _ h]
    · rename_i h
      rw [RbT.inorder_node, RbT.inorder_node, inorder_insertBST z r hr,
        ivtInsert_append_right z e _ h _ (fun w hw hzw => h (ivlLt_of_lt_of_le hzw (hle w hw)))]

/-- The descent's step left. -/
theorem plug_insertBST_left (z : Entry) (C : RbCtx Entry) (c : RbColor) (l : RbT Entry)
    (e : Entry) (r : RbT Entry) (h : ivlLt z.1 e.1) :
    C.plug ((RbT.node c l e r).insertBST z) = (RbCtx.inL c C e r).plug (l.insertBST z) := by
  simp [RbT.insertBST, h]

/-- The descent's step right. -/
theorem plug_insertBST_right (z : Entry) (C : RbCtx Entry) (c : RbColor) (l : RbT Entry)
    (e : Entry) (r : RbT Entry) (h : ¬ ivlLt z.1 e.1) :
    C.plug ((RbT.node c l e r).insertBST z) = (RbCtx.inR c l e C).plug (r.insertBST z) := by
  simp [RbT.insertBST, h]

/-- The direction the descent took at the hole's parent. -/
def RbCtx.dirOk (z : Entry) : RbCtx Entry → Prop
  | .top => True
  | .inL _ _ e _ => ivlLt z.1 e.1
  | .inR _ _ e _ => ¬ ivlLt z.1 e.1

/-! ## The `max` augmentation under a change of shape -/

/-- A subtree's max is determined by its entries. -/
theorem maxEnd_eq_of_inorder (t1 t2 : RbT Entry) (h : t1.inorder = t2.inorder) :
    t1.maxEnd = t2.maxEnd := by
  cases t1 with
  | leaf =>
    cases t2 with
    | leaf => rfl
    | node c l e r => simp at h
  | node c1 l1 e1 r1 =>
    cases t2 with
    | leaf => simp at h
    | node c2 l2 e2 r2 =>
      simp only [maxEnd_node, Option.some.injEq]
      obtain ⟨z1, hz1, hz1e⟩ := maxEnd_mem _ _ (maxEnd_node c1 l1 e1 r1)
      obtain ⟨z2, hz2, hz2e⟩ := maxEnd_mem _ _ (maxEnd_node c2 l2 e2 r2)
      have h1 := maxEnd_ge _ _ (maxEnd_node c1 l1 e1 r1) z2 (h ▸ hz2)
      have h2 := maxEnd_ge _ _ (maxEnd_node c2 l2 e2 r2) z1 (h.symm ▸ hz1)
      rw [hz2e] at h1; rw [hz1e] at h2
      rcases affLt_trichotomy (nodeMax l1 e1 r1) (nodeMax l2 e2 r2) with h3 | h3 | h3
      · exact absurd h3 h1
      · exact h3
      · exact absurd h3 h2

/-- A node's max as its children's maxima (`updateMax`'s computation). -/
def nodeMaxO (lo : Option GoString) (e : Entry) (ro : Option GoString) : GoString :=
  affMaxO (affMaxO e.1.2 lo) ro

theorem nodeMax_eq (l : RbT Entry) (e : Entry) (r : RbT Entry) :
    nodeMax l e r = nodeMaxO l.maxEnd e r.maxEnd := rfl

/-- The rotations keep a subtree's max. -/
theorem nodeMax_rotate (a b c : RbT Entry) (x y : Entry) (cx cy : RbColor) :
    nodeMax a x (.node cy b y c) = nodeMax (.node cx a x b) y c := by
  have := maxEnd_eq_of_inorder (.node cx a x (.node cy b y c)) (.node cy (.node cx a x b) y c)
    (by simp)
  simpa using this

end entries

end adt
end EtcdGrove
end Perennial
