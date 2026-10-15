/-
The pure model of the interval tree's `Delete` (`pkg/v3/adt`): contexts composed (`RbCtx.comp`,
the path from a node down to its successor under the path from the root down to the node), the
in-order list around a hole (`inorder_plug`: what is left and right of it), the leftmost path
(`AllL`, `min`'s), the `max` augmentation through a context (`RbCtx.upMax`, `maxEnd_plug`), and
`deleteFixup`'s loop invariant (`DelInv`, CLRS 13.4's: the hole `x` carries an extra black; the
tree is red-black but for that and for a red `x` under a red parent or over a red child)
established by the splice (`del_start`), preserved by each of the loop's cases (`del_case1_L`
... `del_case4_R`) and giving a red-black tree when `x` is blackened at the exit
(`delInv_exit`). Lean-first; see `notes/decisions.md`, "The watchable store: the plan, the
interval tree's contract".
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.adt.TreeInsert

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace adt

namespace RbT
variable {E : Type}

/-- The red-black condition below the root (the root may be red over a red child: `x` after a
red-uncle step of `deleteFixup`, blackened at the exit). -/
def redOkBelow : RbT E → Prop
  | leaf => True
  | node _ l _ r => l.redOk ∧ r.redOk

theorem redOkBelow_of_redOk (t : RbT E) (h : t.redOk) : t.redOkBelow := by
  cases t with
  | leaf => trivial
  | node c l e r => exact ⟨h.2.1, h.2.2⟩

theorem redOk_of_below_black (t : RbT E) (h : t.redOkBelow) (hc : t.color = .black) :
    t.redOk := by
  cases t with
  | leaf => trivial
  | node c l e r =>
    simp only [color_node] at hc
    subst hc
    exact ⟨fun h' => absurd h' (by decide), h.1, h.2⟩

theorem redOk_blacken_below (t : RbT E) (h : t.redOkBelow) : t.blacken.redOk := by
  cases t with
  | leaf => trivial
  | node c l e r => exact ⟨fun h' => absurd h' (by decide), h.1, h.2⟩

/-- A black node has a positive black height. -/
theorem blackHeight_black_pos {l r : RbT E} {e : E} {k : Nat}
    (h : (node .black l e r).blackHeight = some k) : k ≥ 1 := by
  obtain ⟨h', -, -, rfl⟩ := (blackHeight_node _ _ _ _ _).1 h
  simp

theorem blackHeight_black {l r : RbT E} {e : E} {k : Nat}
    (h : (node .black l e r).blackHeight = some (k + 1)) :
    l.blackHeight = some k ∧ r.blackHeight = some k := by
  obtain ⟨h', h1, h2, hk⟩ := (blackHeight_node _ _ _ _ _).1 h
  simp at hk; subst hk
  exact ⟨h1, h2⟩

theorem blackHeight_red {l r : RbT E} {e : E} {k : Nat}
    (h : (node .red l e r).blackHeight = some k) :
    l.blackHeight = some k ∧ r.blackHeight = some k := by
  obtain ⟨h', h1, h2, hk⟩ := (blackHeight_node _ _ _ _ _).1 h
  simp at hk; subst hk
  exact ⟨h1, h2⟩

theorem blackHeight_leaf_iff {t : RbT E} (h : t.blackHeight = some 0) (hc : t.color = .black) :
    t = .leaf := by
  cases t with
  | leaf => rfl
  | node c l e r =>
    simp only [color_node] at hc
    subst hc
    have := blackHeight_black_pos h
    omega

/-- The colours and black heights do not depend on a node's entry. -/
theorem blackHeight_entry (c : RbColor) (l : RbT E) (e e' : E) (r : RbT E) :
    (node c l e' r).blackHeight = (node c l e r).blackHeight := rfl

end RbT

namespace RbCtx
variable {E : Type}

/-! ## Composed contexts -/

/-- The context `A` (innermost frame first) under the context `D`: `A`'s top is `D`'s hole. -/
def comp : RbCtx E → RbCtx E → RbCtx E
  | top, D => D
  | inL c A e r, D => inL c (comp A D) e r
  | inR c l e A, D => inR c l e (comp A D)

@[simp] theorem comp_top_left (D : RbCtx E) : comp top D = D := rfl
@[simp] theorem comp_inL (c : RbColor) (A : RbCtx E) (e : E) (r : RbT E) (D : RbCtx E) :
    comp (inL c A e r) D = inL c (comp A D) e r := rfl
@[simp] theorem comp_inR (c : RbColor) (l : RbT E) (e : E) (A D : RbCtx E) :
    comp (inR c l e A) D = inR c l e (comp A D) := rfl

theorem comp_top : ∀ (A : RbCtx E), comp A top = A
  | top => rfl
  | inL c A e r => by simp [comp_top A]
  | inR c l e A => by simp [comp_top A]

theorem plug_comp : ∀ (A D : RbCtx E) (t : RbT E), (comp A D).plug t = D.plug (A.plug t)
  | top, D, t => rfl
  | inL c A e r, D, t => by simp [plug_comp A D]
  | inR c l e A, D, t => by simp [plug_comp A D]

/-- The number of frames. -/
def depth : RbCtx E → Nat
  | top => 0
  | inL _ A _ _ => A.depth + 1
  | inR _ _ _ A => A.depth + 1

/-- Every frame a left one: the path from a node down to the leftmost node of its subtree
(`min`'s). -/
def AllL : RbCtx E → Prop
  | top => True
  | inL _ A _ _ => A.AllL
  | inR _ _ _ _ => False

/-! ## The in-order list around a hole -/

/-- The entries before the hole, in order. -/
def leftL : RbCtx E → List E
  | top => []
  | inL _ C _ _ => C.leftL
  | inR _ l e C => C.leftL ++ l.inorder ++ [e]

/-- The entries after the hole, in order. -/
def rightL : RbCtx E → List E
  | top => []
  | inL _ C e r => e :: r.inorder ++ C.rightL
  | inR _ _ _ C => C.rightL

theorem inorder_plug : ∀ (C : RbCtx E) (t : RbT E),
    (C.plug t).inorder = C.leftL ++ t.inorder ++ C.rightL
  | top, t => by simp [leftL, rightL]
  | inL c C e r, t => by simp [leftL, rightL, inorder_plug C]
  | inR c l e C, t => by simp [leftL, rightL, inorder_plug C]

theorem leftL_allL : ∀ (A : RbCtx E), A.AllL → A.leftL = []
  | top, _ => rfl
  | inL _ A _ _, h => leftL_allL A h
  | inR _ _ _ _, h => h.elim

/-! ## `Delete`'s in-order list -/

theorem getElem?_middle {α : Type} (P Q : List α) (z : α) : (P ++ z :: Q)[P.length]? = some z := by
  simp

theorem eraseIdx_middle {α : Type} (P Q : List α) (z : α) :
    (P ++ z :: Q).eraseIdx P.length = P ++ Q := by
  induction P with
  | nil => rfl
  | cons a P ih => simp [ih]

/-- **The splice of a node with at most one child** removes its entry (at its index). -/
theorem del_inorder_one (C : RbCtx E) (c : RbColor) (l : RbT E) (ze : E) (r tx : RbT E)
    (h : (l = .leaf ∧ tx = r) ∨ (r = .leaf ∧ tx = l)) :
    (C.plug (.node c l ze r)).inorder[C.leftL.length + l.inorder.length]? = some ze ∧
      (C.plug tx).inorder =
        (C.plug (.node c l ze r)).inorder.eraseIdx (C.leftL.length + l.inorder.length) := by
  have hL : (C.plug (.node c l ze r)).inorder = (C.leftL ++ l.inorder) ++ ze :: (r.inorder ++ C.rightL) := by
    rw [inorder_plug]; simp
  have hlen : C.leftL.length + l.inorder.length = (C.leftL ++ l.inorder).length := by simp
  rw [hL, hlen, getElem?_middle, eraseIdx_middle, inorder_plug]
  refine ⟨rfl, ?_⟩
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp

/-- **The two-children case**: the successor `y` (leftmost in the right subtree, along the left
path `A`) spliced out and its entry copied into the node: the node's entry removed. -/
theorem del_inorder_two (C A : RbCtx E) (c : RbColor) (l : RbT E) (ze : E) (cy : RbColor)
    (ye : E) (yr : RbT E) (hA : A.AllL) :
    (C.plug (.node c l ze (A.plug (.node cy .leaf ye yr)))).inorder[C.leftL.length +
        l.inorder.length]? = some ze ∧
      ((A.comp (.inR c l ye C)).plug yr).inorder =
        (C.plug (.node c l ze (A.plug (.node cy .leaf ye yr)))).inorder.eraseIdx
          (C.leftL.length + l.inorder.length) := by
  have hL : (C.plug (.node c l ze (A.plug (.node cy .leaf ye yr)))).inorder =
      (C.leftL ++ l.inorder) ++ ze :: ((A.plug (.node cy .leaf ye yr)).inorder ++ C.rightL) := by
    rw [inorder_plug]; simp
  have hlen : C.leftL.length + l.inorder.length = (C.leftL ++ l.inorder).length := by simp
  rw [hL, hlen, getElem?_middle, eraseIdx_middle, plug_comp, inorder_plug, inorder_plug A,
    inorder_plug A, leftL_allL A hA]
  refine ⟨rfl, ?_⟩
  simp [leftL, rightL]

/-! ## The red-black invariant through a context, more -/

/-- A black hole is never a violation. -/
theorem redOk_black_of (C : RbCtx E) (ch : RbColor) (h : C.redOk ch) : C.redOk .black := by
  cases C with
  | top => trivial
  | inL c p e r => exact ⟨fun hc => ⟨rfl, (h.1 hc).2⟩, h.2⟩
  | inR c l e p => exact ⟨fun hc => ⟨(h.1 hc).1, rfl⟩, h.2⟩

theorem redOk_black_of_redOkX (C : RbCtx E) (h : C.redOkX) : C.redOk .black := by
  cases C with
  | top => trivial
  | inL c p e r => exact ⟨fun hc => ⟨rfl, h.1 hc⟩, h.2⟩
  | inR c l e p => exact ⟨fun hc => ⟨h.1 hc, rfl⟩, h.2⟩

/-- The tree's red-black properties do not depend on a node's entry. -/
theorem rb_entry (C : RbCtx E) (c : RbColor) (l : RbT E) (e e' : E) (r : RbT E)
    (hr : (plug C (.node c l e r)).redOk) (hb : (plug C (.node c l e r)).blackHeight.isSome)
    (hc : (plug C (.node c l e r)).color = .black) :
    (plug C (.node c l e' r)).redOk ∧ (plug C (.node c l e' r)).blackHeight.isSome ∧
      (plug C (.node c l e' r)).color = .black := by
  obtain ⟨hn, hC⟩ := (redOk_plug C _).1 hr
  obtain ⟨k, hk, hCk⟩ := bhOk_of_plug C _ hb
  refine ⟨(redOk_plug C _).2 ⟨hn, hC⟩, bh_plug C _ k (by rw [RbT.blackHeight_entry]; exact hk) hCk,
    ?_⟩
  by_cases hCt : C = .top
  · subst hCt; exact hc
  · exact (color_plug_congr C _ _ hCt).trans hc

/-! ## `deleteFixup`'s loop invariant -/

/-- CLRS 13.4's invariant of `RB-DELETE-FIXUP` at `x`, the subtree `t` in the context `C`: `t`
is red-black below its root; the black heights are consistent counting `x` doubly black (its
context expects one more); no red node has a red child but possibly `x` under its parent
(`redOkX`); the root is black unless `x` is it. -/
def DelInv (C : RbCtx E) (t : RbT E) : Prop :=
  t.redOkBelow ∧ (∃ h, t.blackHeight = some h ∧ C.bhOk (h + 1)) ∧ C.redOkX ∧
    (C = .top ∨ (plug C t).color = .black)

/-- **The exit**: `x` the root or red, the tree with `x` blackened is red-black. -/
theorem delInv_exit (C : RbCtx E) (t : RbT E) (h : DelInv C t) (hx : C = .top ∨ t.color = .red) :
    (plug C t.blacken).redOk ∧ (plug C t.blacken).blackHeight.isSome ∧
      (plug C t.blacken).color = .black := by
  obtain ⟨hb, ⟨k, hk, hC⟩, hx', hroot⟩ := h
  rcases hx with rfl | hred
  · refine ⟨RbT.redOk_blacken_below t hb, ?_, RbT.color_blacken t⟩
    exact RbT.blackHeight_blacken t (by rw [hk]; rfl)
  · obtain ⟨l, e, r, rfl⟩ : ∃ l e r, t = .node .red l e r := by
      cases t with
      | leaf => cases hred
      | node c l e r => simp only [RbT.color_node] at hred; subst hred; exact ⟨l, e, r, rfl⟩
    obtain ⟨hl, hr⟩ := RbT.blackHeight_red hk
    have hbk : (RbT.node .black l e r).blackHeight = some (k + 1) := by
      rw [RbT.blackHeight_node_of _ _ _ _ k hl hr]; simp
    refine ⟨(redOk_plug C _).2 ⟨RbT.redOk_blacken_below _ hb, redOk_black_of_redOkX C hx'⟩,
      bh_plug C _ _ hbk hC, ?_⟩
    rcases hroot with rfl | hroot
    · rfl
    · by_cases hCt : C = .top
      · subst hCt; rfl
      · exact (color_plug_congr C _ _ hCt).trans hroot

/-- **The splice**: a node with at most one child replaced by that child (or the leaf). With the
node black, the invariant holds at the child; with it red, the child is the leaf and the tree is
red-black already. -/
theorem del_start (C : RbCtx E) (c : RbColor) (a : RbT E) (e : E) (b tx : RbT E)
    (hx : (a = .leaf ∧ tx = b) ∨ (b = .leaf ∧ tx = a))
    (hr : (plug C (.node c a e b)).redOk) (hb : (plug C (.node c a e b)).blackHeight.isSome)
    (hc : (plug C (.node c a e b)).color = .black) :
    (c = .black → DelInv C tx) ∧
      (c = .red → (plug C tx).redOk ∧ (plug C tx).blackHeight.isSome ∧
        (plug C tx).color = .black) := by
  obtain ⟨hn, hC⟩ := (redOk_plug C _).1 hr
  obtain ⟨k, hk, hCk⟩ := bhOk_of_plug C _ hb
  obtain ⟨h, ha, hb', hkh⟩ := (RbT.blackHeight_node _ _ _ _ _).1 hk
  have htx : tx.blackHeight = some h ∧ tx.redOk := by
    rcases hx with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact ⟨hb', hn.2.2⟩
    · exact ⟨ha, hn.2.1⟩
  refine ⟨fun hcb => ?_, fun hcr => ?_⟩
  · subst hcb
    simp at hkh; subst hkh
    refine ⟨RbT.redOkBelow_of_redOk _ htx.2, ⟨h, htx.1, hCk⟩, redOkX_of_redOk C _ hC, ?_⟩
    by_cases hCt : C = .top
    · exact Or.inl hCt
    · exact Or.inr ((color_plug_congr C _ _ hCt).trans hc)
  · subst hcr
    have hkh' : k = h := by simpa using hkh
    rw [hkh'] at hCk
    obtain ⟨hac, hbc⟩ := hn.1 rfl
    -- both children are black, one is the leaf: so is the other
    have hh : h = 0 := by
      rcases hx with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · simpa using ha.symm
      · simpa using hb'.symm
    subst hh
    have htl : tx = .leaf := by
      rcases hx with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact RbT.blackHeight_leaf_iff hb' hbc
      · exact RbT.blackHeight_leaf_iff ha hac
    subst htl
    refine ⟨(redOk_plug C _).2 ⟨trivial, redOk_black_of C _ hC⟩, bh_plug C _ 0 rfl hCk, ?_⟩
    by_cases hCt : C = .top
    · subst hCt; rfl
    · exact (color_plug_congr C _ _ hCt).trans hc

/-- The doubly-black `x` has a sibling node (its black height is positive). -/
theorem delInv_sib_L {c : RbColor} {CP : RbCtx E} {pe : E} {tw t : RbT E}
    (h : DelInv (inL c CP pe tw) t) : ∃ cw wl we wr, tw = .node cw wl we wr := by
  obtain ⟨-, ⟨k, -, hw, -⟩, -⟩ := h
  cases tw with
  | leaf => simp at hw
  | node cw wl we wr => exact ⟨cw, wl, we, wr, rfl⟩

theorem delInv_sib_R {c : RbColor} {CP : RbCtx E} {pe : E} {tw t : RbT E}
    (h : DelInv (inR c tw pe CP) t) : ∃ cw wl we wr, tw = .node cw wl we wr := by
  obtain ⟨-, ⟨k, -, hw, -⟩, -⟩ := h
  cases tw with
  | leaf => simp at hw
  | node cw wl we wr => exact ⟨cw, wl, we, wr, rfl⟩

/-- The root condition after a step below `CP`'s hole. -/
theorem root_below {CP : RbCtx E} {C : RbCtx E} {t : RbT E} {g g' : RbT E}
    (h : C = .top ∨ (plug C t).color = .black) (hp : plug C t = plug CP g) (hC : C ≠ .top)
    (hg : CP = .top → g'.color = .black) :
    (plug CP g').color = .black := by
  rcases h with h | h
  · exact absurd h hC
  · by_cases hCP : CP = .top
    · subst hCP; exact hg rfl
    · rw [color_plug_congr CP g' g hCP, ← hp]; exact h

/-- The root's colour, with the hole's subtree's colour unchanged. -/
theorem color_plug_inner (C : RbCtx E) (t1 t2 : RbT E) (hc : t1.color = t2.color) :
    (plug C t1).color = (plug C t2).color := by
  by_cases hC : C = .top
  · subst hC; exact hc
  · exact color_plug_congr C _ _ hC

section cases
variable {cp : RbColor} {CP : RbCtx E} {pe we e1 e2 : E} {wl wr a b t : RbT E}

/-- Case 1 (`x` left of `P`), the sibling `w` red: `w` black, `P` red, rotate `P` left; `x`'s
new sibling is `w`'s left child (black). -/
theorem del_case1_L (h : DelInv (inL cp CP pe (.node .red wl we wr)) t) :
    DelInv (inL .red (inL .black CP we wr) pe wl) t ∧ wl.color = .black ∧
      (plug (inL .red (inL .black CP we wr) pe wl) t).inorder =
        (plug (inL cp CP pe (.node .red wl we wr)) t).inorder := by
  obtain ⟨hb, ⟨k, hk, hw, hCP⟩, ⟨hcw, hwr, hCPr⟩, hroot⟩ := h
  have hcp : cp = .black := by
    cases cp
    · exact absurd (hcw rfl) (by simp)
    · rfl
  subst hcp
  obtain ⟨hwl, hwr'⟩ := RbT.blackHeight_red hw
  obtain ⟨hcol, hwlr, hwrr⟩ := (RbT.redOk_node _ _ _ _).1 hwr
  obtain ⟨hwlc, hwrc⟩ := hcol rfl
  refine ⟨⟨hb, ⟨k, hk, hwl, hwr', by simpa using hCP⟩, ⟨fun _ => hwlc, hwlr,
    ⟨fun h => absurd h (by decide), hwrr, hCPr⟩⟩, Or.inr ?_⟩, hwlc, ?_⟩
  · exact root_below (CP := CP) (g' := .node .black (.node .red t pe wl) we wr) hroot rfl
      (by simp) (fun _ => rfl)
  · exact inorder_plug_congr CP (by simp)

/-- Case 2, the sibling black with black children: `w` red, `x` moves up to `P`. -/
theorem del_case2_L (h : DelInv (inL cp CP pe (.node .black wl we wr)) t)
    (ht : t.color = .black) (hl : wl.color = .black) (hr : wr.color = .black) :
    DelInv CP (.node cp t pe (.node .red wl we wr)) ∧
      (plug CP (.node cp t pe (.node .red wl we wr))).inorder =
        (plug (inL cp CP pe (.node .black wl we wr)) t).inorder := by
  obtain ⟨hb, ⟨k, hk, hw, hCP⟩, ⟨-, hwr, hCPr⟩, hroot⟩ := h
  obtain ⟨hwl, hwr'⟩ := RbT.blackHeight_black hw
  refine ⟨⟨⟨RbT.redOk_of_below_black t hb ht, fun _ => ⟨hl, hr⟩, hwr.2.1, hwr.2.2⟩,
    ⟨k + if cp = .black then 1 else 0, ?_, ?_⟩, redOkX_of_redOk CP _ hCPr, ?_⟩, ?_⟩
  · exact RbT.blackHeight_node_of _ _ _ _ k hk
      (by rw [RbT.blackHeight_node_of _ _ _ _ k hwl hwr']; simp)
  · have : k + (if cp = .black then 1 else 0) + 1 = k + 1 + (if cp = .black then 1 else 0) := by
      omega
    rw [this]; exact hCP
  · by_cases hCPt : CP = .top
    · exact Or.inl hCPt
    · exact Or.inr (root_below hroot rfl (by simp) (fun h => absurd h hCPt))
  · exact inorder_plug_congr CP (by simp)

/-- Case 3, the sibling black with its left child red and right child black: `w`'s left black,
`w` red, rotate `w` right; the new sibling has a red right child (case 4 follows). -/
theorem del_case3_L (h : DelInv (inL cp CP pe (.node .black (.node .red a e1 b) we wr)) t)
    (hr : wr.color = .black) :
    DelInv (inL cp CP pe (.node .black a e1 (.node .red b we wr))) t ∧
      (plug (inL cp CP pe (.node .black a e1 (.node .red b we wr))) t).inorder =
        (plug (inL cp CP pe (.node .black (.node .red a e1 b) we wr)) t).inorder := by
  obtain ⟨hb, ⟨k, hk, hw, hCP⟩, ⟨-, hwr, hCPr⟩, hroot⟩ := h
  obtain ⟨hwl, hwr'⟩ := RbT.blackHeight_black hw
  obtain ⟨ha, hbb⟩ := RbT.blackHeight_red hwl
  obtain ⟨-, hwl', hwrr⟩ := (RbT.redOk_node _ _ _ _).1 hwr
  obtain ⟨hcol, har, hbr⟩ := (RbT.redOk_node _ _ _ _).1 hwl'
  obtain ⟨hac, hbc⟩ := hcol rfl
  refine ⟨⟨hb, ⟨k, hk, ?_, hCP⟩, ⟨fun _ => rfl, ⟨fun h => absurd h (by decide), har,
    ⟨fun _ => ⟨hbc, hr⟩, hbr, hwrr⟩⟩, hCPr⟩, ?_⟩, ?_⟩
  · rw [RbT.blackHeight_node_of _ _ _ _ k ha (by rw [RbT.blackHeight_node_of _ _ _ _ k hbb hwr']; simp)]
    simp
  · rcases hroot with h | h
    · exact absurd h (by simp)
    · exact Or.inr ((color_plug_inner CP (.node cp t pe (.node .black a e1 (.node .red b we wr)))
        (.node cp t pe (.node .black (.node .red a e1 b) we wr))
        rfl).trans h)
  · exact inorder_plug_congr CP (by simp)

/-- Case 4, the sibling black with a red right child: `w` takes `P`'s colour, `P` and `w`'s
right child black, rotate `P` left: the tree is red-black but for its root (`x` becomes it). -/
theorem del_case4_L (h : DelInv (inL cp CP pe (.node .black wl we (.node .red a e2 b))) t)
    (ht : t.color = .black) :
    DelInv .top (plug CP (.node cp (.node .black t pe wl) we (.node .black a e2 b))) ∧
      (plug CP (.node cp (.node .black t pe wl) we (.node .black a e2 b))).inorder =
        (plug (inL cp CP pe (.node .black wl we (.node .red a e2 b))) t).inorder := by
  obtain ⟨hb, ⟨k, hk, hw, hCP⟩, ⟨-, hwr, hCPr⟩, -⟩ := h
  obtain ⟨hwl, hwr'⟩ := RbT.blackHeight_black hw
  obtain ⟨ha, hbb⟩ := RbT.blackHeight_red hwr'
  obtain ⟨-, hwlr, hwr''⟩ := (RbT.redOk_node _ _ _ _).1 hwr
  obtain ⟨-, har, hbr⟩ := (RbT.redOk_node _ _ _ _).1 hwr''
  have hN : (RbT.node cp (.node .black t pe wl) we (.node .black a e2 b)).blackHeight =
      some (k + 1 + if cp = .black then 1 else 0) := by
    rw [RbT.blackHeight_node_of _ _ _ _ (k + 1)
      (by rw [RbT.blackHeight_node_of _ _ _ _ k hk hwl]; simp)
      (by rw [RbT.blackHeight_node_of _ _ _ _ k ha hbb]; simp)]
  have hred : (plug CP (.node cp (.node .black t pe wl) we (.node .black a e2 b))).redOk :=
    (redOk_plug CP _).2 ⟨⟨fun _ => ⟨rfl, rfl⟩,
      ⟨fun h => absurd h (by decide), RbT.redOk_of_below_black t hb ht, hwlr⟩,
      ⟨fun h => absurd h (by decide), har, hbr⟩⟩, hCPr⟩
  obtain ⟨k', hk'⟩ := Option.isSome_iff_exists.1 (bh_plug CP _ _ hN hCP)
  refine ⟨⟨RbT.redOkBelow_of_redOk _ hred, ⟨k', hk', trivial⟩, trivial, Or.inl rfl⟩, ?_⟩
  exact inorder_plug_congr CP (by simp)

/-- Case 1 mirrored (`x` right of `P`): `w` black, `P` red, rotate `P` right. -/
theorem del_case1_R (h : DelInv (inR cp (.node .red wl we wr) pe CP) t) :
    DelInv (inR .red wr pe (inR .black wl we CP)) t ∧ wr.color = .black ∧
      (plug (inR .red wr pe (inR .black wl we CP)) t).inorder =
        (plug (inR cp (.node .red wl we wr) pe CP) t).inorder := by
  obtain ⟨hb, ⟨k, hk, hw, hCP⟩, ⟨hcw, hwr, hCPr⟩, hroot⟩ := h
  have hcp : cp = .black := by
    cases cp
    · exact absurd (hcw rfl) (by simp)
    · rfl
  subst hcp
  obtain ⟨hwl, hwr'⟩ := RbT.blackHeight_red hw
  obtain ⟨hcol, hwlr, hwrr⟩ := (RbT.redOk_node _ _ _ _).1 hwr
  obtain ⟨hwlc, hwrc⟩ := hcol rfl
  refine ⟨⟨hb, ⟨k, hk, hwr', hwl, by simpa using hCP⟩, ⟨fun _ => hwrc, hwrr,
    ⟨fun h => absurd h (by decide), hwlr, hCPr⟩⟩, Or.inr ?_⟩, hwrc, ?_⟩
  · exact root_below (CP := CP) (g' := .node .black wl we (.node .red wr pe t)) hroot rfl
      (by simp) (fun _ => rfl)
  · exact inorder_plug_congr CP (by simp)

/-- Case 2 mirrored. -/
theorem del_case2_R (h : DelInv (inR cp (.node .black wl we wr) pe CP) t)
    (ht : t.color = .black) (hl : wl.color = .black) (hr : wr.color = .black) :
    DelInv CP (.node cp (.node .red wl we wr) pe t) ∧
      (plug CP (.node cp (.node .red wl we wr) pe t)).inorder =
        (plug (inR cp (.node .black wl we wr) pe CP) t).inorder := by
  obtain ⟨hb, ⟨k, hk, hw, hCP⟩, ⟨-, hwr, hCPr⟩, hroot⟩ := h
  obtain ⟨hwl, hwr'⟩ := RbT.blackHeight_black hw
  refine ⟨⟨⟨(RbT.redOk_node _ _ _ _).2 ⟨fun _ => ⟨hl, hr⟩, hwr.2.1, hwr.2.2⟩,
    RbT.redOk_of_below_black t hb ht⟩,
    ⟨k + if cp = .black then 1 else 0, ?_, ?_⟩, redOkX_of_redOk CP _ hCPr, ?_⟩, ?_⟩
  · exact RbT.blackHeight_node_of _ _ _ _ k
      (by rw [RbT.blackHeight_node_of _ _ _ _ k hwl hwr']; simp) hk
  · have : k + (if cp = .black then 1 else 0) + 1 = k + 1 + (if cp = .black then 1 else 0) := by
      omega
    rw [this]; exact hCP
  · by_cases hCPt : CP = .top
    · exact Or.inl hCPt
    · exact Or.inr (root_below hroot rfl (by simp) (fun h => absurd h hCPt))
  · exact inorder_plug_congr CP (by simp)

/-- Case 3 mirrored: the sibling's right child red, its left black: rotate `w` left. -/
theorem del_case3_R (h : DelInv (inR cp (.node .black wl we (.node .red a e1 b)) pe CP) t)
    (hl : wl.color = .black) :
    DelInv (inR cp (.node .black (.node .red wl we a) e1 b) pe CP) t ∧
      (plug (inR cp (.node .black (.node .red wl we a) e1 b) pe CP) t).inorder =
        (plug (inR cp (.node .black wl we (.node .red a e1 b)) pe CP) t).inorder := by
  obtain ⟨hb, ⟨k, hk, hw, hCP⟩, ⟨-, hwr, hCPr⟩, hroot⟩ := h
  obtain ⟨hwl, hwr'⟩ := RbT.blackHeight_black hw
  obtain ⟨ha, hbb⟩ := RbT.blackHeight_red hwr'
  obtain ⟨-, hwlr, hwr''⟩ := (RbT.redOk_node _ _ _ _).1 hwr
  obtain ⟨hcol, har, hbr⟩ := (RbT.redOk_node _ _ _ _).1 hwr''
  obtain ⟨hac, hbc⟩ := hcol rfl
  refine ⟨⟨hb, ⟨k, hk, ?_, hCP⟩, ⟨fun _ => rfl, ⟨fun h => absurd h (by decide),
    ⟨fun _ => ⟨hl, hac⟩, hwlr, har⟩, hbr⟩, hCPr⟩, ?_⟩, ?_⟩
  · rw [RbT.blackHeight_node_of _ _ _ _ k (by rw [RbT.blackHeight_node_of _ _ _ _ k hwl ha]; simp) hbb]
    simp
  · rcases hroot with h | h
    · exact absurd h (by simp)
    · exact Or.inr ((color_plug_inner CP (.node cp (.node .black (.node .red wl we a) e1 b) pe t)
        (.node cp (.node .black wl we (.node .red a e1 b)) pe t)
        rfl).trans h)
  · exact inorder_plug_congr CP (by simp)

/-- Case 4 mirrored: the sibling's left child red: rotate `P` right. -/
theorem del_case4_R (h : DelInv (inR cp (.node .black (.node .red a e2 b) we wr) pe CP) t)
    (ht : t.color = .black) :
    DelInv .top (plug CP (.node cp (.node .black a e2 b) we (.node .black wr pe t))) ∧
      (plug CP (.node cp (.node .black a e2 b) we (.node .black wr pe t))).inorder =
        (plug (inR cp (.node .black (.node .red a e2 b) we wr) pe CP) t).inorder := by
  obtain ⟨hb, ⟨k, hk, hw, hCP⟩, ⟨-, hwr, hCPr⟩, -⟩ := h
  obtain ⟨hwl, hwr'⟩ := RbT.blackHeight_black hw
  obtain ⟨ha, hbb⟩ := RbT.blackHeight_red hwl
  obtain ⟨-, hwl', hwrr⟩ := (RbT.redOk_node _ _ _ _).1 hwr
  obtain ⟨-, har, hbr⟩ := (RbT.redOk_node _ _ _ _).1 hwl'
  have hN : (RbT.node cp (.node .black a e2 b) we (.node .black wr pe t)).blackHeight =
      some (k + 1 + if cp = .black then 1 else 0) := by
    rw [RbT.blackHeight_node_of _ _ _ _ (k + 1)
      (by rw [RbT.blackHeight_node_of _ _ _ _ k ha hbb]; simp)
      (by rw [RbT.blackHeight_node_of _ _ _ _ k hwr' hk]; simp)]
  have hred : (plug CP (.node cp (.node .black a e2 b) we (.node .black wr pe t))).redOk :=
    (redOk_plug CP _).2 ⟨⟨fun _ => ⟨rfl, rfl⟩,
      ⟨fun h => absurd h (by decide), har, hbr⟩,
      ⟨fun h => absurd h (by decide), hwrr, RbT.redOk_of_below_black t hb ht⟩⟩, hCPr⟩
  obtain ⟨k', hk'⟩ := Option.isSome_iff_exists.1 (bh_plug CP _ _ hN hCP)
  refine ⟨⟨RbT.redOkBelow_of_redOk _ hred, ⟨k', hk', trivial⟩, trivial, Or.inl rfl⟩, ?_⟩
  exact inorder_plug_congr CP (by simp)

end cases

end RbCtx

/-! ## The `max` augmentation through a context -/

section entries
variable [ext : FfiSyntax]

/-- The max of the context's top subtree, given its hole's subtree's max `mh` (what the frames'
`max` fields hold, `ownCtx`'s). -/
def RbCtx.upMax : RbCtx Entry → Option GoString → Option GoString
  | .top, mh => mh
  | .inL _ C e r, mh => C.upMax (some (nodeMaxO mh e r.maxEnd))
  | .inR _ l e C, mh => C.upMax (some (nodeMaxO l.maxEnd e mh))

theorem maxEnd_plug : ∀ (C : RbCtx Entry) (t : RbT Entry), (C.plug t).maxEnd = C.upMax t.maxEnd
  | .top, _ => rfl
  | .inL c C e r, t => by
    rw [RbCtx.plug_inL, maxEnd_plug C]; rfl
  | .inR c l e C, t => by
    rw [RbCtx.plug_inR, maxEnd_plug C]; rfl

theorem upMax_comp : ∀ (A D : RbCtx Entry) (mh : Option GoString),
    (A.comp D).upMax mh = D.upMax (A.upMax mh)
  | .top, _, _ => rfl
  | .inL _ A _ _, D, _ => upMax_comp A D _
  | .inR _ _ _ A, D, _ => upMax_comp A D _

theorem maxEnd_blacken (t : RbT Entry) : t.blacken.maxEnd = t.maxEnd := by
  cases t <;> rfl

end entries

end adt
end EtcdGrove
end Perennial
