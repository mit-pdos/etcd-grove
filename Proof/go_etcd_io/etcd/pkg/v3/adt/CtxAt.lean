/-
The interval tree with a hole, its frames' locations pinned (`Delete`'s and the fixups' view of
it): `ownPathAt s q A ls n p mh`, the frames of the context `A` from the hole `n` (child of `p`)
up, at the fraction `q`, each frame's node's parent and other child listed in `ls` (innermost
first) — a path from a node `topAt A ls n p` down to the hole, its top's parent field included —;
and `ownCtxAt t s C ls n p mh`, such a path from the tree's root (`ownCtx` with the locations as
an index: `ownCtx_at`). The helpers' specs that change a tree under a hole (`updateMax`,
`replaceParent`, the rotations) keep `ls`: a caller that has moved the hole along a path (from
the node `Delete` removes down to its successor) finds the path's nodes where they were
(`ownCtxAt_comp`, `ownCtxAt_split`). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.adt.Ctx
public import Proof.go_etcd_io.etcd.pkg.v3.adt.TreeDelete

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace adt

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3.adt

section top
variable [ext : FfiSyntax]

/-- The top of a path: the node at the top of the context `A` (whose frames' parents and other
children are `ls`, innermost first) over the hole `n` (child of `p`), and its parent. -/
def topAt : RbCtx Entry → List (Loc × Loc) → Loc → Loc → Loc × Loc
  | .top, _, n, p => (n, p)
  | .inL _ _ _ _, [], n, p => (n, p)
  | .inR _ _ _ _, [], n, p => (n, p)
  | .inL _ C _ _, (pp, _) :: ls, _, p => topAt C ls p pp
  | .inR _ _ _ C, (pp, _) :: ls, _, p => topAt C ls p pp

@[simp] theorem topAt_top (ls : List (Loc × Loc)) (n p : Loc) :
    topAt .top ls n p = (n, p) := rfl

@[simp] theorem topAt_inL (c : RbColor) (C : RbCtx Entry) (e : Entry) (r : RbT Entry)
    (pp rp : Loc) (ls : List (Loc × Loc)) (n p : Loc) :
    topAt (.inL c C e r) ((pp, rp) :: ls) n p = topAt C ls p pp := rfl

@[simp] theorem topAt_inR (c : RbColor) (l : RbT Entry) (e : Entry) (C : RbCtx Entry)
    (pp lp : Loc) (ls : List (Loc × Loc)) (n p : Loc) :
    topAt (.inR c l e C) ((pp, lp) :: ls) n p = topAt C ls p pp := rfl

end top

section ctx
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.adt.Assumptions]

/-- A node is not the sentinel, nor `nil`. -/
theorem ownNode_node_ne (s : Loc) (q : Qp) (p n : Loc) (c : RbColor) (l : RbT Entry) (e : Entry)
    (r : RbT Entry) : ownNode (GF := GF) s q p n (.node c l e r) ⊢ ⌜n ≠ s ∧ n ≠ null⌝ := by
  iintro H
  icases ownNode_node_open _ _ _ _ _ _ _ _ $$ H with ⟨%lp, %rp, %Hn, -⟩
  ipureintro; exact Hn

/-- The path from `topAt A ls n p` down to the hole at `n` (child of `p`), the hole's subtree's
max being `mh`, at the fraction `q`: per frame, the parent node `p` (not the sentinel) with its
fields, its child pointer at `n`, its other child and parent as listed, its `max` as `updateMax`
computes it from `mh`, its other subtree; `ls` must have one entry per frame. -/
def ownPathAt (s : Loc) (q : Qp) :
    RbCtx Entry → List (Loc × Loc) → Loc → Loc → Option GoString → IProp GF
  | .top, [], _, _, _ => iprop(True)
  | .inL c C e r, (pp, rp) :: ls, n, p, mh => iprop(⌜p ≠ s ∧ p ≠ null⌝ ∗
      p.[intervalNode, go!"iv"] ↦{DFrac.own q}
        ({ Ivl' := affIvl e.1.1 e.1.2, Val' := e.2 } : IntervalValue) ∗
      p.[intervalNode, go!"max"] ↦{DFrac.own q} maxW (nodeMaxO mh e r.maxEnd) ∗
      p.[intervalNode, go!"left"] ↦{DFrac.own q} n ∗
      p.[intervalNode, go!"right"] ↦{DFrac.own q} rp ∗
      p.[intervalNode, go!"parent"] ↦{DFrac.own q} pp ∗
      p.[intervalNode, go!"c"] ↦{DFrac.own q} colorW c ∗
      ownNode s q p rp r ∗ ownPathAt s q C ls p pp (some (nodeMaxO mh e r.maxEnd)))
  | .inR c l e C, (pp, lp) :: ls, n, p, mh => iprop(⌜p ≠ s ∧ p ≠ null⌝ ∗
      p.[intervalNode, go!"iv"] ↦{DFrac.own q}
        ({ Ivl' := affIvl e.1.1 e.1.2, Val' := e.2 } : IntervalValue) ∗
      p.[intervalNode, go!"max"] ↦{DFrac.own q} maxW (nodeMaxO l.maxEnd e mh) ∗
      p.[intervalNode, go!"left"] ↦{DFrac.own q} lp ∗
      p.[intervalNode, go!"right"] ↦{DFrac.own q} n ∗
      p.[intervalNode, go!"parent"] ↦{DFrac.own q} pp ∗
      p.[intervalNode, go!"c"] ↦{DFrac.own q} colorW c ∗
      ownNode s q p lp l ∗ ownPathAt s q C ls p pp (some (nodeMaxO l.maxEnd e mh)))
  | .top, _ :: _, _, _, _ => iprop(False)
  | .inL _ _ _ _, [], _, _, _ => iprop(False)
  | .inR _ _ _ _, [], _, _, _ => iprop(False)

theorem ownPathAt_top (s : Loc) (q : Qp) (n p : Loc) (mh : Option GoString) :
    ownPathAt (GF := GF) s q .top [] n p mh = iprop(True) := by rw [ownPathAt]

theorem ownPathAt_top_intro (s : Loc) (q : Qp) (n p : Loc) (mh : Option GoString) :
    ⊢ ownPathAt (GF := GF) s q .top [] n p mh := by
  rw [ownPathAt_top]; exact pure_intro trivial

theorem ownPathAt_top_cons (s : Loc) (q : Qp) (f : Loc × Loc) (ls : List (Loc × Loc))
    (n p : Loc) (mh : Option GoString) :
    ownPathAt (GF := GF) s q .top (f :: ls) n p mh = iprop(False) := by rw [ownPathAt]

theorem ownPathAt_inL (s : Loc) (q : Qp) (c : RbColor) (C : RbCtx Entry) (e : Entry)
    (r : RbT Entry) (pp rp : Loc) (ls : List (Loc × Loc)) (n p : Loc) (mh : Option GoString) :
    ownPathAt (GF := GF) s q (.inL c C e r) ((pp, rp) :: ls) n p mh = iprop(⌜p ≠ s ∧ p ≠ null⌝ ∗
      p.[intervalNode, go!"iv"] ↦{DFrac.own q}
        ({ Ivl' := affIvl e.1.1 e.1.2, Val' := e.2 } : IntervalValue) ∗
      p.[intervalNode, go!"max"] ↦{DFrac.own q} maxW (nodeMaxO mh e r.maxEnd) ∗
      p.[intervalNode, go!"left"] ↦{DFrac.own q} n ∗
      p.[intervalNode, go!"right"] ↦{DFrac.own q} rp ∗
      p.[intervalNode, go!"parent"] ↦{DFrac.own q} pp ∗
      p.[intervalNode, go!"c"] ↦{DFrac.own q} colorW c ∗
      ownNode s q p rp r ∗ ownPathAt s q C ls p pp (some (nodeMaxO mh e r.maxEnd))) := by
  rw [ownPathAt]

theorem ownPathAt_inR (s : Loc) (q : Qp) (c : RbColor) (l : RbT Entry) (e : Entry)
    (C : RbCtx Entry) (pp lp : Loc) (ls : List (Loc × Loc)) (n p : Loc) (mh : Option GoString) :
    ownPathAt (GF := GF) s q (.inR c l e C) ((pp, lp) :: ls) n p mh = iprop(⌜p ≠ s ∧ p ≠ null⌝ ∗
      p.[intervalNode, go!"iv"] ↦{DFrac.own q}
        ({ Ivl' := affIvl e.1.1 e.1.2, Val' := e.2 } : IntervalValue) ∗
      p.[intervalNode, go!"max"] ↦{DFrac.own q} maxW (nodeMaxO l.maxEnd e mh) ∗
      p.[intervalNode, go!"left"] ↦{DFrac.own q} lp ∗
      p.[intervalNode, go!"right"] ↦{DFrac.own q} n ∗
      p.[intervalNode, go!"parent"] ↦{DFrac.own q} pp ∗
      p.[intervalNode, go!"c"] ↦{DFrac.own q} colorW c ∗
      ownNode s q p lp l ∗ ownPathAt s q C ls p pp (some (nodeMaxO l.maxEnd e mh))) := by
  rw [ownPathAt]

theorem ownPathAt_inL_nil (s : Loc) (q : Qp) (c : RbColor) (C : RbCtx Entry) (e : Entry)
    (r : RbT Entry) (n p : Loc) (mh : Option GoString) :
    ownPathAt (GF := GF) s q (.inL c C e r) [] n p mh = iprop(False) := by rw [ownPathAt]

theorem ownPathAt_inR_nil (s : Loc) (q : Qp) (c : RbColor) (l : RbT Entry) (e : Entry)
    (C : RbCtx Entry) (n p : Loc) (mh : Option GoString) :
    ownPathAt (GF := GF) s q (.inR c l e C) [] n p mh = iprop(False) := by rw [ownPathAt]

/-- The path's frames are as many as the context's. -/
theorem ownPathAt_length (s : Loc) (q : Qp) : ∀ (A : RbCtx Entry) (ls : List (Loc × Loc))
    (n p : Loc) (mh : Option GoString),
    ownPathAt (GF := GF) s q A ls n p mh ⊢ ⌜ls.length = A.depth⌝
  | .top, [], _, _, _ => by rw [ownPathAt_top]; iintro -; ipureintro; rfl
  | .top, _ :: _, _, _, _ => by rw [ownPathAt_top_cons]; iintro %h; exact h.elim
  | .inL c C e r, [], _, _, _ => by rw [ownPathAt_inL_nil]; iintro %h; exact h.elim
  | .inR c l e C, [], _, _, _ => by rw [ownPathAt_inR_nil]; iintro %h; exact h.elim
  | .inL c C e r, (pp, rp) :: ls, n, p, mh => by
    rw [ownPathAt_inL]
    iintro ⟨-, -, -, -, -, -, -, -, H⟩
    ihave %h := ownPathAt_length s q C ls p pp _ $$ H
    ipureintro; simp [RbCtx.depth, h]
  | .inR c l e C, (pp, lp) :: ls, n, p, mh => by
    rw [ownPathAt_inR]
    iintro ⟨-, -, -, -, -, -, -, -, H⟩
    ihave %h := ownPathAt_length s q C ls p pp _ $$ H
    ipureintro; simp [RbCtx.depth, h]

/-- **The path with its hole's subtree** is the subtree of its top. -/
theorem ownPathAt_plug (s : Loc) (q : Qp) : ∀ (A : RbCtx Entry) (ls : List (Loc × Loc))
    (n p : Loc) (T : RbT Entry),
    ownPathAt (GF := GF) s q A ls n p T.maxEnd ∗ ownNode s q p n T ⊢
      ownNode s q (topAt A ls n p).2 (topAt A ls n p).1 (A.plug T)
  | .top, [], n, p, T => by iintro ⟨-, H⟩; simp only [topAt_top, RbCtx.plug_top]; iexact H
  | .top, _ :: _, _, _, _ => by rw [ownPathAt_top_cons]; iintro ⟨%h, -⟩; exact h.elim
  | .inL c C e r, [], _, _, _ => by rw [ownPathAt_inL_nil]; iintro ⟨%h, -⟩; exact h.elim
  | .inR c l e C, [], _, _, _ => by rw [ownPathAt_inR_nil]; iintro ⟨%h, -⟩; exact h.elim
  | .inL c C e r, (pp, rp) :: ls, n, p, T => by
    rw [ownPathAt_inL]
    iintro ⟨⟨%Hp, Hiv, Hmx, Hl, Hr, Hpp, Hc, Hnr, HC⟩, Hn⟩
    rw [topAt_inL, RbCtx.plug_inL]
    iapply ownPathAt_plug s q C ls p pp (.node c T e r)
    rw [maxEnd_node, nodeMax_eq]
    iframe HC
    iapply ownNode_node_close
    iexists n, rp
    simp only [nodeMax_eq]
    iframe
    ipureintro; exact Hp
  | .inR c l e C, (pp, lp) :: ls, n, p, T => by
    rw [ownPathAt_inR]
    iintro ⟨⟨%Hp, Hiv, Hmx, Hl, Hr, Hpp, Hc, Hnl, HC⟩, Hn⟩
    rw [topAt_inR, RbCtx.plug_inR]
    iapply ownPathAt_plug s q C ls p pp (.node c l e T)
    rw [maxEnd_node, nodeMax_eq]
    iframe HC
    iapply ownNode_node_close
    iexists lp, n
    simp only [nodeMax_eq]
    iframe
    ipureintro; exact Hp

theorem ownPathAt_plug' (s : Loc) (q : Qp) (A : RbCtx Entry) (ls : List (Loc × Loc))
    (n p m pm : Loc) (T : RbT Entry) (h : topAt A ls n p = (m, pm)) :
    ownPathAt (GF := GF) s q A ls n p T.maxEnd ∗ ownNode s q p n T ⊢ ownNode s q pm m (A.plug T) := by
  have := ownPathAt_plug (GF := GF) s q A ls n p T
  rw [h] at this; exact this

/-- One level down to the left child, from the node's fields (a descent that read them). -/
theorem ownPathAt_push_inL (s : Loc) (q : Qp) (C : RbCtx Entry) (ls : List (Loc × Loc))
    (x y : Loc) (c : RbColor) (l : RbT Entry) (e : Entry) (r : RbT Entry) (lp rp : Loc)
    (hx : x ≠ s ∧ x ≠ null) :
    ownPathAt (GF := GF) s q C ls x y (some (nodeMax l e r)) ∗
      x.[intervalNode, go!"iv"] ↦{DFrac.own q}
        ({ Ivl' := affIvl e.1.1 e.1.2, Val' := e.2 } : IntervalValue) ∗
      x.[intervalNode, go!"max"] ↦{DFrac.own q} maxW (nodeMax l e r) ∗
      x.[intervalNode, go!"left"] ↦{DFrac.own q} lp ∗
      x.[intervalNode, go!"right"] ↦{DFrac.own q} rp ∗
      x.[intervalNode, go!"parent"] ↦{DFrac.own q} y ∗
      x.[intervalNode, go!"c"] ↦{DFrac.own q} colorW c ∗
      ownNode s q x rp r ⊢ ownPathAt s q (.inL c C e r) ((y, rp) :: ls) lp x l.maxEnd := by
  iintro ⟨HC, Hiv, Hmx, Hl, Hr, Hp, Hc, Hnr⟩
  rw [ownPathAt_inL]
  simp only [nodeMax_eq]
  iframe
  ipureintro; exact hx

theorem ownPathAt_push_inR (s : Loc) (q : Qp) (C : RbCtx Entry) (ls : List (Loc × Loc))
    (x y : Loc) (c : RbColor) (l : RbT Entry) (e : Entry) (r : RbT Entry) (lp rp : Loc)
    (hx : x ≠ s ∧ x ≠ null) :
    ownPathAt (GF := GF) s q C ls x y (some (nodeMax l e r)) ∗
      x.[intervalNode, go!"iv"] ↦{DFrac.own q}
        ({ Ivl' := affIvl e.1.1 e.1.2, Val' := e.2 } : IntervalValue) ∗
      x.[intervalNode, go!"max"] ↦{DFrac.own q} maxW (nodeMax l e r) ∗
      x.[intervalNode, go!"left"] ↦{DFrac.own q} lp ∗
      x.[intervalNode, go!"right"] ↦{DFrac.own q} rp ∗
      x.[intervalNode, go!"parent"] ↦{DFrac.own q} y ∗
      x.[intervalNode, go!"c"] ↦{DFrac.own q} colorW c ∗
      ownNode s q x lp l ⊢ ownPathAt s q (.inR c l e C) ((y, lp) :: ls) rp x r.maxEnd := by
  iintro ⟨HC, Hiv, Hmx, Hl, Hr, Hp, Hc, Hnl⟩
  rw [ownPathAt_inR]
  simp only [nodeMax_eq]
  iframe
  ipureintro; exact hx

/-- The path's top is not the sentinel when the path has a frame. -/
theorem ownPathAt_top_ne (s : Loc) (q : Qp) : ∀ (A : RbCtx Entry) (ls : List (Loc × Loc))
    (n p : Loc) (mh : Option GoString), A ≠ .top →
    ownPathAt (GF := GF) s q A ls n p mh ⊢ ⌜(topAt A ls n p).1 ≠ s⌝
  | .top, _, _, _, _, h => absurd rfl h
  | .inL c C e r, [], _, _, _, _ => by rw [ownPathAt_inL_nil]; iintro %h; exact h.elim
  | .inR c l e C, [], _, _, _, _ => by rw [ownPathAt_inR_nil]; iintro %h; exact h.elim
  | .inL c C e r, (pp, rp) :: ls, n, p, mh, _ => by
    rw [ownPathAt_inL, topAt_inL]
    iintro ⟨%Hp, -, -, -, -, -, -, -, H⟩
    by_cases hC : C = .top
    · subst hC
      ipureintro; simp only [topAt_top]; exact Hp.1
    · iapply ownPathAt_top_ne s q C ls p pp _ hC $$ H
  | .inR c l e C, (pp, lp) :: ls, n, p, mh, _ => by
    rw [ownPathAt_inR, topAt_inR]
    iintro ⟨%Hp, -, -, -, -, -, -, -, H⟩
    by_cases hC : C = .top
    · subst hC
      ipureintro; simp only [topAt_top]; exact Hp.1
    · iapply ownPathAt_top_ne s q C ls p pp _ hC $$ H

/-- The path's top is not a node whose `parent` field is owned elsewhere. -/
theorem ownPathAt_top_ne_node (s : Loc) : ∀ (A : RbCtx Entry) (ls : List (Loc × Loc))
    (n p : Loc) (mh : Option GoString) (x v : Loc), A ≠ .top →
    ownPathAt (GF := GF) s 1 A ls n p mh ∗ x.[intervalNode, go!"parent"] ↦ v ⊢
      ⌜(topAt A ls n p).1 ≠ x⌝
  | .top, _, _, _, _, _, _, h => absurd rfl h
  | .inL c C e r, [], _, _, _, _, _, _ => by
    rw [ownPathAt_inL_nil]; iintro ⟨%h, -⟩; exact h.elim
  | .inR c l e C, [], _, _, _, _, _, _ => by
    rw [ownPathAt_inR_nil]; iintro ⟨%h, -⟩; exact h.elim
  | .inL c C e r, (pp, rp) :: ls, n, p, mh, x, v, _ => by
    rw [ownPathAt_inL, topAt_inL]
    iintro ⟨⟨%Hp, -, -, -, -, Hpp, -, -, H⟩, Hx⟩
    by_cases hC : C = .top
    · subst hC
      simp only [topAt_top]
      by_cases h : p = x
      · subst h
        iexfalso; iapply locField_excl; iframe
      · ipureintro; exact h
    · iapply ownPathAt_top_ne_node s C ls p pp _ x v hC; iframe
  | .inR c l e C, (pp, lp) :: ls, n, p, mh, x, v, _ => by
    rw [ownPathAt_inR, topAt_inR]
    iintro ⟨⟨%Hp, -, -, -, -, Hpp, -, -, H⟩, Hx⟩
    by_cases hC : C = .top
    · subst hC
      simp only [topAt_top]
      by_cases h : p = x
      · subst h
        iexfalso; iapply locField_excl; iframe
      · ipureintro; exact h
    · iapply ownPathAt_top_ne_node s C ls p pp _ x v hC; iframe

/-! ## The tree with a hole, its frames pinned -/

/-- `ownCtx` with the frames' locations as an index: a path from the root (the tree's `root`
field, its parent the sentinel). -/
def ownCtxAt (t s : Loc) (C : RbCtx Entry) (ls : List (Loc × Loc)) (n p : Loc)
    (mh : Option GoString) : IProp GF :=
  iprop(ownPathAt s 1 C ls n p mh ∗ ⌜(topAt C ls n p).2 = s⌝ ∗
    t.[intervalTree, go!"root"] ↦ (topAt C ls n p).1)

theorem ownCtxAt_top (t s n p : Loc) (mh : Option GoString) :
    ownCtxAt (GF := GF) t s .top [] n p mh ⊣⊢ ⌜p = s⌝ ∗ t.[intervalTree, go!"root"] ↦ n := by
  unfold ownCtxAt
  rw [ownPathAt_top, topAt_top]
  constructor
  · iintro ⟨-, %h, Hr⟩; iframe; ipureintro; exact h
  · iintro ⟨%h, Hr⟩; iframe; ipureintro; exact h

theorem ownCtxAt_inL (t s : Loc) (c : RbColor) (C : RbCtx Entry) (e : Entry) (r : RbT Entry)
    (pp rp : Loc) (ls : List (Loc × Loc)) (n p : Loc) (mh : Option GoString) :
    ownCtxAt (GF := GF) t s (.inL c C e r) ((pp, rp) :: ls) n p mh ⊣⊢ ⌜p ≠ s ∧ p ≠ null⌝ ∗
      p.[intervalNode, go!"iv"] ↦
        ({ Ivl' := affIvl e.1.1 e.1.2, Val' := e.2 } : IntervalValue) ∗
      p.[intervalNode, go!"max"] ↦ maxW (nodeMaxO mh e r.maxEnd) ∗
      p.[intervalNode, go!"left"] ↦ n ∗
      p.[intervalNode, go!"right"] ↦ rp ∗
      p.[intervalNode, go!"parent"] ↦ pp ∗
      p.[intervalNode, go!"c"] ↦ colorW c ∗
      ownNode s 1 p rp r ∗ ownCtxAt t s C ls p pp (some (nodeMaxO mh e r.maxEnd)) := by
  unfold ownCtxAt
  rw [ownPathAt_inL, topAt_inL]
  constructor
  · iintro ⟨⟨%Hp, Hiv, Hmx, Hl, Hr, Hpp, Hc, Hnr, HC⟩, %Ht, Hroot⟩
    iframe; ipureintro; exact ⟨Hp, Ht⟩
  · iintro ⟨%Hp, Hiv, Hmx, Hl, Hr, Hpp, Hc, Hnr, HC, %Ht, Hroot⟩
    iframe; ipureintro; exact ⟨Hp, Ht⟩

theorem ownCtxAt_inR (t s : Loc) (c : RbColor) (l : RbT Entry) (e : Entry) (C : RbCtx Entry)
    (pp lp : Loc) (ls : List (Loc × Loc)) (n p : Loc) (mh : Option GoString) :
    ownCtxAt (GF := GF) t s (.inR c l e C) ((pp, lp) :: ls) n p mh ⊣⊢ ⌜p ≠ s ∧ p ≠ null⌝ ∗
      p.[intervalNode, go!"iv"] ↦
        ({ Ivl' := affIvl e.1.1 e.1.2, Val' := e.2 } : IntervalValue) ∗
      p.[intervalNode, go!"max"] ↦ maxW (nodeMaxO l.maxEnd e mh) ∗
      p.[intervalNode, go!"left"] ↦ lp ∗
      p.[intervalNode, go!"right"] ↦ n ∗
      p.[intervalNode, go!"parent"] ↦ pp ∗
      p.[intervalNode, go!"c"] ↦ colorW c ∗
      ownNode s 1 p lp l ∗ ownCtxAt t s C ls p pp (some (nodeMaxO l.maxEnd e mh)) := by
  unfold ownCtxAt
  rw [ownPathAt_inR, topAt_inR]
  constructor
  · iintro ⟨⟨%Hp, Hiv, Hmx, Hl, Hr, Hpp, Hc, Hnl, HC⟩, %Ht, Hroot⟩
    iframe; ipureintro; exact ⟨Hp, Ht⟩
  · iintro ⟨%Hp, Hiv, Hmx, Hl, Hr, Hpp, Hc, Hnl, HC, %Ht, Hroot⟩
    iframe; ipureintro; exact ⟨Hp, Ht⟩

theorem ownCtxAt_top_cons (t s : Loc) (f : Loc × Loc) (ls : List (Loc × Loc)) (n p : Loc)
    (mh : Option GoString) : ownCtxAt (GF := GF) t s .top (f :: ls) n p mh ⊢ False := by
  unfold ownCtxAt; rw [ownPathAt_top_cons]; iintro ⟨%h, -⟩; exact h.elim

theorem ownCtxAt_inL_nil (t s : Loc) (c : RbColor) (C : RbCtx Entry) (e : Entry)
    (r : RbT Entry) (n p : Loc) (mh : Option GoString) :
    ownCtxAt (GF := GF) t s (.inL c C e r) [] n p mh ⊢ False := by
  unfold ownCtxAt; rw [ownPathAt_inL_nil]; iintro ⟨%h, -⟩; exact h.elim

theorem ownCtxAt_inR_nil (t s : Loc) (c : RbColor) (l : RbT Entry) (e : Entry)
    (C : RbCtx Entry) (n p : Loc) (mh : Option GoString) :
    ownCtxAt (GF := GF) t s (.inR c l e C) [] n p mh ⊢ False := by
  unfold ownCtxAt; rw [ownPathAt_inR_nil]; iintro ⟨%h, -⟩; exact h.elim

/-- **`ownCtx` is `ownCtxAt` with the locations hidden.** -/
theorem ownCtx_at (t s : Loc) : ∀ (C : RbCtx Entry) (n p : Loc) (mh : Option GoString),
    ownCtx (GF := GF) t s C n p mh ⊣⊢ ∃ ls, ownCtxAt t s C ls n p mh
  | .top, n, p, mh => by
    rw [ownCtx_top]
    constructor
    · iintro H; iexists []; iapply (ownCtxAt_top t s n p mh).2; iexact H
    · iintro ⟨%ls, H⟩
      cases ls with
      | nil => iapply (ownCtxAt_top t s n p mh).1; iexact H
      | cons f ls => iexfalso; iapply ownCtxAt_top_cons $$ H
  | .inL c C e r, n, p, mh => by
    rw [ownCtx_inL]
    constructor
    · iintro ⟨%pp, %rp, %Hp, Hiv, Hmx, Hl, Hr, Hpp, Hc, Hnr, HC⟩
      icases (ownCtx_at t s C p pp _).1 $$ HC with ⟨%ls, HC⟩
      iexists (pp, rp) :: ls
      iapply (ownCtxAt_inL t s c C e r pp rp ls n p mh).2
      iframe; ipureintro; exact Hp
    · iintro ⟨%ls, H⟩
      cases ls with
      | nil => iexfalso; iapply ownCtxAt_inL_nil $$ H
      | cons f ls =>
        obtain ⟨pp, rp⟩ := f
        icases (ownCtxAt_inL t s c C e r pp rp ls n p mh).1 $$ H with
          ⟨%Hp, Hiv, Hmx, Hl, Hr, Hpp, Hc, Hnr, HC⟩
        iexists pp, rp
        iframe
        isplitl []
        · ipureintro; exact Hp
        iapply (ownCtx_at t s C p pp _).2
        iexists ls; iexact HC
  | .inR c l e C, n, p, mh => by
    rw [ownCtx_inR]
    constructor
    · iintro ⟨%pp, %lp, %Hp, Hiv, Hmx, Hl, Hr, Hpp, Hc, Hnl, HC⟩
      icases (ownCtx_at t s C p pp _).1 $$ HC with ⟨%ls, HC⟩
      iexists (pp, lp) :: ls
      iapply (ownCtxAt_inR t s c l e C pp lp ls n p mh).2
      iframe; ipureintro; exact Hp
    · iintro ⟨%ls, H⟩
      cases ls with
      | nil => iexfalso; iapply ownCtxAt_inR_nil $$ H
      | cons f ls =>
        obtain ⟨pp, lp⟩ := f
        icases (ownCtxAt_inR t s c l e C pp lp ls n p mh).1 $$ H with
          ⟨%Hp, Hiv, Hmx, Hl, Hr, Hpp, Hc, Hnl, HC⟩
        iexists pp, lp
        iframe
        isplitl []
        · ipureintro; exact Hp
        iapply (ownCtx_at t s C p pp _).2
        iexists ls; iexact HC

theorem ownCtxAt_ctx (t s : Loc) (C : RbCtx Entry) (ls : List (Loc × Loc)) (n p : Loc)
    (mh : Option GoString) : ownCtxAt (GF := GF) t s C ls n p mh ⊢ ownCtx t s C n p mh := by
  iintro H; iapply (ownCtx_at t s C n p mh).2; iexists ls; iexact H

/-- The hole's parent is the sentinel exactly at the top. -/
theorem ownCtxAt_parent (t s : Loc) (C : RbCtx Entry) (ls : List (Loc × Loc)) (n p : Loc)
    (mh : Option GoString) : ownCtxAt (GF := GF) t s C ls n p mh ⊢ ⌜C = .top ↔ p = s⌝ := by
  iintro H
  iapply ownCtx_parent
  iapply ownCtxAt_ctx; iexact H

/-- At the top, the hole's max does not matter. -/
theorem ownCtxAt_top_any (t s n p : Loc) (ls : List (Loc × Loc)) (mh mh' : Option GoString) :
    ownCtxAt (GF := GF) t s .top ls n p mh ⊢ ownCtxAt t s .top ls n p mh' := by
  unfold ownCtxAt
  cases ls with
  | nil => rw [ownPathAt_top, ownPathAt_top]
  | cons f ls => rw [ownPathAt_top_cons]; iintro ⟨%h, -⟩; exact h.elim

/-- **A path under a context**, joined (the path's top the context's hole). -/
theorem ownCtxAt_comp (t s : Loc) (D : RbCtx Entry) (ls2 : List (Loc × Loc)) (m pm : Loc) :
    ∀ (A : RbCtx Entry) (ls1 : List (Loc × Loc)) (n p : Loc) (mh : Option GoString),
    topAt A ls1 n p = (m, pm) →
    ownPathAt (GF := GF) s 1 A ls1 n p mh ∗ ownCtxAt t s D ls2 m pm (A.upMax mh) ⊢
      ownCtxAt t s (A.comp D) (ls1 ++ ls2) n p mh
  | .top, [], n, p, mh, h => by
    simp only [topAt_top, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [RbCtx.upMax, RbCtx.comp_top_left, List.nil_append]
    iintro ⟨-, H⟩; iexact H
  | .top, _ :: _, _, _, _, _ => by rw [ownPathAt_top_cons]; iintro ⟨%h, -⟩; exact h.elim
  | .inL c C e r, [], _, _, _, _ => by rw [ownPathAt_inL_nil]; iintro ⟨%h, -⟩; exact h.elim
  | .inR c l e C, [], _, _, _, _ => by rw [ownPathAt_inR_nil]; iintro ⟨%h, -⟩; exact h.elim
  | .inL c C e r, (pp, rp) :: ls, n, p, mh, h => by
    rw [ownPathAt_inL]
    simp only [RbCtx.upMax]
    iintro ⟨⟨%Hp, Hiv, Hmx, Hl, Hr, Hpp, Hc, Hnr, HC⟩, HD⟩
    rw [RbCtx.comp_inL, List.cons_append]
    iapply (ownCtxAt_inL t s c (C.comp D) e r pp rp (ls ++ ls2) n p mh).2
    iframe
    isplitl []
    · ipureintro; exact Hp
    iapply ownCtxAt_comp t s D ls2 m pm C ls p pp _ h
    iframe
  | .inR c l e C, (pp, lp) :: ls, n, p, mh, h => by
    rw [ownPathAt_inR]
    simp only [RbCtx.upMax]
    iintro ⟨⟨%Hp, Hiv, Hmx, Hl, Hr, Hpp, Hc, Hnl, HC⟩, HD⟩
    rw [RbCtx.comp_inR, List.cons_append]
    iapply (ownCtxAt_inR t s c l e (C.comp D) pp lp (ls ++ ls2) n p mh).2
    iframe
    isplitl []
    · ipureintro; exact Hp
    iapply ownCtxAt_comp t s D ls2 m pm C ls p pp _ h
    iframe

/-- **A context split at a path's top**, the path's frames listed first. -/
theorem ownCtxAt_split (t s : Loc) (D : RbCtx Entry) (ls2 : List (Loc × Loc)) :
    ∀ (A : RbCtx Entry) (ls1 : List (Loc × Loc)) (n p : Loc) (mh : Option GoString),
    ls1.length = A.depth →
    ownCtxAt (GF := GF) t s (A.comp D) (ls1 ++ ls2) n p mh ⊢
      ownPathAt s 1 A ls1 n p mh ∗
        ownCtxAt t s D ls2 (topAt A ls1 n p).1 (topAt A ls1 n p).2 (A.upMax mh)
  | .top, [], n, p, mh, _ => by
    rw [ownPathAt_top]; simp only [topAt_top, RbCtx.comp_top_left, List.nil_append, RbCtx.upMax]
    iintro H; iframe
  | .top, _ :: _, _, _, _, h => by simp [RbCtx.depth] at h
  | .inL c C e r, [], _, _, _, h => by simp [RbCtx.depth] at h
  | .inR c l e C, [], _, _, _, h => by simp [RbCtx.depth] at h
  | .inL c C e r, (pp, rp) :: ls, n, p, mh, h => by
    rw [RbCtx.comp_inL, List.cons_append, ownPathAt_inL, topAt_inL]
    simp only [RbCtx.upMax]
    iintro H
    icases (ownCtxAt_inL t s c (C.comp D) e r pp rp (ls ++ ls2) n p mh).1 $$ H with
      ⟨%Hp, Hiv, Hmx, Hl, Hr, Hpp, Hc, Hnr, HC⟩
    icases ownCtxAt_split t s D ls2 C ls p pp _ (by simpa [RbCtx.depth] using h) $$ HC with
      ⟨HA, HD⟩
    iframe
    ipureintro; exact Hp
  | .inR c l e C, (pp, lp) :: ls, n, p, mh, h => by
    rw [RbCtx.comp_inR, List.cons_append, ownPathAt_inR, topAt_inR]
    simp only [RbCtx.upMax]
    iintro H
    icases (ownCtxAt_inR t s c l e (C.comp D) pp lp (ls ++ ls2) n p mh).1 $$ H with
      ⟨%Hp, Hiv, Hmx, Hl, Hr, Hpp, Hc, Hnl, HC⟩
    icases ownCtxAt_split t s D ls2 C ls p pp _ (by simpa [RbCtx.depth] using h) $$ HC with
      ⟨HA, HD⟩
    iframe
    ipureintro; exact Hp

/-- The root field, lent out: the path's top (the hole itself at the top). -/
theorem ownCtxAt_root (t s : Loc) (C : RbCtx Entry) (ls : List (Loc × Loc)) (n p : Loc)
    (mh : Option GoString) :
    ownCtxAt (GF := GF) t s C ls n p mh ⊢
      t.[intervalTree, go!"root"] ↦ (topAt C ls n p).1 ∗
        (t.[intervalTree, go!"root"] ↦ (topAt C ls n p).1 -∗ ownCtxAt t s C ls n p mh) := by
  unfold ownCtxAt
  iintro ⟨HP, %Ht, Hr⟩
  iframe Hr
  iintro Hr
  iframe; ipureintro; exact Ht

/-- **One level up**, the frames pinned. -/
theorem ownCtxAt_up_inL (t s : Loc) (c : RbColor) (C : RbCtx Entry) (e : Entry) (r : RbT Entry)
    (pp rp : Loc) (ls : List (Loc × Loc)) (n p : Loc) (T : RbT Entry) :
    ownCtxAt (GF := GF) t s (.inL c C e r) ((pp, rp) :: ls) n p T.maxEnd ∗ ownNode s 1 p n T ⊢
      ownCtxAt t s C ls p pp (some (nodeMax T e r)) ∗ ownNode s 1 pp p (.node c T e r) := by
  iintro ⟨H, Hn⟩
  icases (ownCtxAt_inL t s c C e r pp rp ls n p _).1 $$ H with
    ⟨%Hp, Hiv, Hmx, Hl, Hr, Hpp, Hc, Hnr, HC⟩
  rw [nodeMax_eq]
  iframe HC
  iapply ownNode_node_close
  iexists n, rp
  simp only [nodeMax_eq]
  iframe
  ipureintro; exact Hp

theorem ownCtxAt_up_inR (t s : Loc) (c : RbColor) (l : RbT Entry) (e : Entry) (C : RbCtx Entry)
    (pp lp : Loc) (ls : List (Loc × Loc)) (n p : Loc) (T : RbT Entry) :
    ownCtxAt (GF := GF) t s (.inR c l e C) ((pp, lp) :: ls) n p T.maxEnd ∗ ownNode s 1 p n T ⊢
      ownCtxAt t s C ls p pp (some (nodeMax l e T)) ∗ ownNode s 1 pp p (.node c l e T) := by
  iintro ⟨H, Hn⟩
  icases (ownCtxAt_inR t s c l e C pp lp ls n p _).1 $$ H with
    ⟨%Hp, Hiv, Hmx, Hl, Hr, Hpp, Hc, Hnl, HC⟩
  rw [nodeMax_eq]
  iframe HC
  iapply ownNode_node_close
  iexists lp, n
  simp only [nodeMax_eq]
  iframe
  ipureintro; exact Hp

/-- **The hole moved to its sibling** (left to right): the same frame, the other child. -/
theorem ownCtxAt_swap_L (t s : Loc) (c : RbColor) (C : RbCtx Entry) (e : Entry) (r : RbT Entry)
    (pp rp : Loc) (ls : List (Loc × Loc)) (n p : Loc) (T : RbT Entry) :
    ownCtxAt (GF := GF) t s (.inL c C e r) ((pp, rp) :: ls) n p T.maxEnd ∗ ownNode s 1 p n T ⊢
      ownCtxAt t s (.inR c T e C) ((pp, n) :: ls) rp p r.maxEnd ∗ ownNode s 1 p rp r := by
  iintro ⟨H, Hn⟩
  icases (ownCtxAt_inL t s c C e r pp rp ls n p _).1 $$ H with
    ⟨%Hp, Hiv, Hmx, Hl, Hr, Hpp, Hc, Hnr, HC⟩
  iframe Hnr
  iapply (ownCtxAt_inR t s c T e C pp n ls rp p _).2
  iframe
  ipureintro; exact Hp

theorem ownCtxAt_swap_R (t s : Loc) (c : RbColor) (l : RbT Entry) (e : Entry) (C : RbCtx Entry)
    (pp lp : Loc) (ls : List (Loc × Loc)) (n p : Loc) (T : RbT Entry) :
    ownCtxAt (GF := GF) t s (.inR c l e C) ((pp, lp) :: ls) n p T.maxEnd ∗ ownNode s 1 p n T ⊢
      ownCtxAt t s (.inL c C e T) ((pp, n) :: ls) lp p l.maxEnd ∗ ownNode s 1 p lp l := by
  iintro ⟨H, Hn⟩
  icases (ownCtxAt_inR t s c l e C pp lp ls n p _).1 $$ H with
    ⟨%Hp, Hiv, Hmx, Hl, Hr, Hpp, Hc, Hnl, HC⟩
  iframe Hnl
  iapply (ownCtxAt_inL t s c C e T pp n ls lp p _).2
  iframe
  ipureintro; exact Hp

/-- The hole is the root exactly at the top (the hole the sentinel or a node whose `parent`
field is owned elsewhere). -/
theorem ownCtxAt_root_ne (t s : Loc) (C : RbCtx Entry) (ls : List (Loc × Loc)) (n p x v : Loc)
    (mh : Option GoString) (hC : C ≠ .top) :
    ownCtxAt (GF := GF) t s C ls n p mh ∗ x.[intervalNode, go!"parent"] ↦ v ⊢
      ⌜(topAt C ls n p).1 ≠ x⌝ := by
  unfold ownCtxAt
  iintro ⟨⟨HP, -, -⟩, Hx⟩
  iapply ownPathAt_top_ne_node s C ls n p mh x v hC; iframe

theorem ownCtxAt_root_ne_s (t s : Loc) (C : RbCtx Entry) (ls : List (Loc × Loc)) (n p : Loc)
    (mh : Option GoString) (hC : C ≠ .top) :
    ownCtxAt (GF := GF) t s C ls n p mh ⊢ ⌜(topAt C ls n p).1 ≠ s⌝ := by
  unfold ownCtxAt
  iintro ⟨HP, -, -⟩
  iapply ownPathAt_top_ne s 1 C ls n p mh hC $$ HP

/-! ## The sentinel's fields -/

/-- The sentinel, its `parent` the hole's parent when the hole is the sentinel (`Delete`'s
`x.parent = y.parent` with `x` the sentinel; `deleteFixup` reads it back). -/
def sentAt (s x p : Loc) : IProp GF :=
  iprop(∃ v : intervalNode, s ↦ v ∗ ⌜x = s → v.parent' = p⌝)

theorem sentAt_ownSentinel (s x p : Loc) : sentAt (GF := GF) s x p ⊢ ownSentinel s 1 := by
  unfold sentAt ownSentinel
  iintro ⟨%v, H, -⟩
  iexists v; iexact H

/-- Another hole: the sentinel's fields are any. -/
theorem sentAt_other (s x p x' p' : Loc) (h : x' ≠ s) :
    sentAt (GF := GF) s x p ⊢ sentAt s x' p' := by
  unfold sentAt
  iintro ⟨%v, H, -⟩
  iexists v; iframe; ipureintro; intro h'; exact absurd h' h

omit package_sem in
/-- A node's points-to as its fields. -/
theorem node_fields (n : Loc) (v : intervalNode) :
    (n ↦ v : IProp GF) ⊢
      n.[intervalNode, go!"iv"] ↦ v.iv' ∗ n.[intervalNode, go!"max"] ↦ v.max' ∗
      n.[intervalNode, go!"left"] ↦ v.left' ∗ n.[intervalNode, go!"right"] ↦ v.right' ∗
      n.[intervalNode, go!"parent"] ↦ v.parent' ∗ n.[intervalNode, go!"c"] ↦ v.c' ∗
      ⌜n ≠ null⌝ := by
  iintro H
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ H
  iStructNamed H
  iframe iv max left right parent c
  ipureintro; exact Hnn

omit package_sem in
/-- A node's fields as its points-to. -/
theorem node_combine (n : Loc) (v : intervalNode) (h : n ≠ null) :
    n.[intervalNode, go!"iv"] ↦ v.iv' ∗ n.[intervalNode, go!"max"] ↦ v.max' ∗
      n.[intervalNode, go!"left"] ↦ v.left' ∗ n.[intervalNode, go!"right"] ↦ v.right' ∗
      n.[intervalNode, go!"parent"] ↦ v.parent' ∗ n.[intervalNode, go!"c"] ↦ v.c' ⊢
      (n ↦ v : IProp GF) := by
  iintro ⟨Hiv, Hmx, Hl, Hr, Hp, Hc⟩
  iapply typedPointsto_combine _ _ _ h
  simp only [TypedPointsto.typedPointstoDef]
  iframe

omit package_sem in
/-- The sentinel's `parent` field, lent out (to be read or written). -/
theorem node_parent (n : Loc) (v : intervalNode) :
    (n ↦ v : IProp GF) ⊢ n.[intervalNode, go!"parent"] ↦ v.parent' ∗ ⌜n ≠ null⌝ ∗
      (∀ w, n.[intervalNode, go!"parent"] ↦ w -∗ n ↦ { v with parent' := w }) := by
  iintro H
  icases node_fields _ _ $$ H with ⟨Hiv, Hmx, Hl, Hr, Hp, Hc, %Hn⟩
  iframe Hp
  isplitl []
  · ipureintro; exact Hn
  iintro %w Hp
  iapply node_combine _ _ Hn
  iframe

omit package_sem in
/-- The sentinel's `c` field, lent out (to be written). -/
theorem node_c (n : Loc) (v : intervalNode) :
    (n ↦ v : IProp GF) ⊢ n.[intervalNode, go!"c"] ↦ v.c' ∗ ⌜n ≠ null⌝ ∗
      (∀ w, n.[intervalNode, go!"c"] ↦ w -∗ n ↦ { v with c' := w }) := by
  iintro H
  icases node_fields _ _ $$ H with ⟨Hiv, Hmx, Hl, Hr, Hp, Hc, %Hn⟩
  iframe Hc
  isplitl []
  · ipureintro; exact Hn
  iintro %w Hc
  iapply node_combine _ _ Hn
  iframe

/-- The hole's `parent` field, lent out: in its node, or the sentinel's when it is the
sentinel. -/
theorem parentAt_open (s p x : Loc) (tx : RbT Entry) :
    ownNode (GF := GF) s 1 p x tx ∗ sentAt s x p ⊢ x.[intervalNode, go!"parent"] ↦ p ∗
      (x.[intervalNode, go!"parent"] ↦ p -∗ ownNode s 1 p x tx ∗ sentAt s x p) := by
  cases tx with
  | leaf =>
    rw [ownNode_leaf]
    unfold sentAt
    iintro ⟨%hx, %v, H, %hv⟩
    subst hx
    icases node_parent _ _ $$ H with ⟨Hp, %Hn, Hback⟩
    rw [hv rfl]
    iframe Hp
    iintro Hp
    ihave H := Hback $$ %p Hp
    isplitl []
    · ipureintro; rfl
    iexists { v with parent' := p }
    iframe
    ipureintro; intro _; rfl
  | node c l e r =>
    iintro ⟨H, Hs⟩
    icases ownNode_node_open _ _ _ _ _ _ _ _ $$ H with
      ⟨%lp, %rp, %Hn, Hiv, Hmx, Hl, Hr, Hp, Hc, Hnl, Hnr⟩
    iframe Hp
    iintro Hp
    iframe Hs
    iapply ownNode_node_close
    iexists lp, rp
    iframe
    ipureintro; exact Hn

/-- The hole is the root exactly at the top. -/
theorem ownCtxAt_root_ne_hole (t s : Loc) (C : RbCtx Entry) (ls : List (Loc × Loc)) (x p : Loc)
    (mh : Option GoString) (tx : RbT Entry) (hC : C ≠ .top) :
    ownCtxAt (GF := GF) t s C ls x p mh ⊢ ownNode s 1 p x tx -∗ ⌜(topAt C ls x p).1 ≠ x⌝ := by
  cases tx with
  | leaf =>
    rw [ownNode_leaf]
    iintro H %hx
    subst hx
    iapply ownCtxAt_root_ne_s t _ C ls _ p mh hC $$ H
  | node c l e r =>
    iintro H Hn
    icases ownNode_node_open _ _ _ _ _ _ _ _ $$ Hn with
      ⟨%lp, %rp, %Hn, -, -, -, -, Hp, -⟩
    iapply ownCtxAt_root_ne t s C ls x p x p mh hC
    iframe

/-- The hole is not its sibling node. -/
theorem ownNode_hole_ne_sib (s p x p' w : Loc) (tx : RbT Entry) (c : RbColor) (l : RbT Entry)
    (e : Entry) (r : RbT Entry) :
    ownNode (GF := GF) s 1 p x tx ⊢ ownNode s 1 p' w (.node c l e r) -∗ ⌜w ≠ x⌝ := by
  cases tx with
  | leaf =>
    rw [ownNode_leaf]
    iintro %hx Hw
    ihave %Hw := ownNode_node_ne _ _ _ _ _ _ _ _ $$ Hw
    ipureintro; rw [hx]; exact Hw.1
  | node cx lx ex rx =>
    iintro Hx Hw
    icases ownNode_node_open _ _ _ _ _ _ _ _ $$ Hx with ⟨%a, %b, %Hxn, -, -, -, -, Hxp, -⟩
    iapply ownNode_ne s p' w x p (.node c l e r) Hxn.1 $$ Hw Hxp

/-- The spliced child's `parent` field, to be written (`x.parent = y.parent`): in its node, or
the sentinel's. -/
theorem parent_write (s z x : Loc) (tx : RbT Entry) :
    ownNode (GF := GF) s 1 z x tx ∗ ownSentinel s 1 ⊢ ∃ v : Loc,
      x.[intervalNode, go!"parent"] ↦ v ∗
        (∀ w, x.[intervalNode, go!"parent"] ↦ w -∗ ownNode s 1 w x tx ∗ sentAt s x w) := by
  cases tx with
  | leaf =>
    rw [ownNode_leaf]
    unfold ownSentinel sentAt
    iintro ⟨%hx, %v, H⟩
    subst hx
    icases node_parent _ _ $$ H with ⟨Hp, %Hn, Hback⟩
    iexists v.parent'
    iframe Hp
    iintro %w Hp
    ihave H := Hback $$ %w Hp
    rw [ownNode_leaf]
    isplitl []
    · ipureintro; rfl
    iexists { v with parent' := w }
    iframe
    ipureintro; intro _; rfl
  | node c l e r =>
    iintro ⟨H, Hs⟩
    icases ownNode_node_open _ _ _ _ _ _ _ _ $$ H with
      ⟨%lp, %rp, %Hn, Hiv, Hmx, Hl, Hr, Hp, Hc, Hnl, Hnr⟩
    iexists z
    iframe Hp
    iintro %w Hp
    isplitl [Hiv Hmx Hl Hr Hp Hc Hnl Hnr]
    · iapply ownNode_node_close
      iexists lp, rp
      iframe
      ipureintro; exact Hn
    unfold ownSentinel sentAt
    icases Hs with ⟨%v, Hs⟩
    iexists v
    iframe
    ipureintro; intro h; exact absurd h Hn.1

omit package_sem in
/-- Two nodes whose `parent` fields are owned are distinct. -/
theorem parent_ne (y z a b : Loc) :
    y.[intervalNode, go!"parent"] ↦ a ⊢ z.[intervalNode, go!"parent"] ↦ b -∗ (⌜y ≠ z⌝ : IProp GF) := by
  iintro Hy Hz
  by_cases h : y = z
  · subst h
    iexfalso; iapply locField_excl; iframe
  · ipureintro; exact h

/-- The `max` field of a path's top node (a frame), lent out. -/
theorem ownPathAt_top_max (s : Loc) : ∀ (A : RbCtx Entry) (ls : List (Loc × Loc)) (n p : Loc)
    (mh : Option GoString), A ≠ .top →
    ownPathAt (GF := GF) s 1 A ls n p mh ⊢ ∃ M, ⌜A.upMax mh = some M⌝ ∗
      (topAt A ls n p).1.[intervalNode, go!"max"] ↦ maxW M ∗
      ((topAt A ls n p).1.[intervalNode, go!"max"] ↦ maxW M -∗ ownPathAt s 1 A ls n p mh)
  | .top, _, _, _, _, h => absurd rfl h
  | .inL c C e r, [], _, _, _, _ => by rw [ownPathAt_inL_nil]; iintro %h; exact h.elim
  | .inR c l e C, [], _, _, _, _ => by rw [ownPathAt_inR_nil]; iintro %h; exact h.elim
  | .inL c C e r, (pp, rp) :: ls, n, p, mh, _ => by
    rw [ownPathAt_inL, topAt_inL]
    iintro ⟨%Hp, Hiv, Hmx, Hl, Hr, Hpp, Hc, Hnr, H⟩
    by_cases hC : C = .top
    · subst hC
      cases ls with
      | cons f ls => rw [ownPathAt_top_cons]; icases H with %h; exact h.elim
      | nil =>
      simp only [topAt_top]
      iexists nodeMaxO mh e r.maxEnd
      iframe Hmx
      isplitl []
      · ipureintro; rfl
      iintro Hmx
      iframe
      ipureintro; exact Hp
    · icases ownPathAt_top_max s C ls p pp _ hC $$ H with ⟨%M, %HM, Hm, Hback⟩
      iexists M
      iframe Hm
      isplitl []
      · ipureintro; exact HM
      iintro Hm
      ihave H := Hback $$ Hm
      iframe
      ipureintro; exact Hp
  | .inR c l e C, (pp, lp) :: ls, n, p, mh, _ => by
    rw [ownPathAt_inR, topAt_inR]
    iintro ⟨%Hp, Hiv, Hmx, Hl, Hr, Hpp, Hc, Hnl, H⟩
    by_cases hC : C = .top
    · subst hC
      cases ls with
      | cons f ls => rw [ownPathAt_top_cons]; icases H with %h; exact h.elim
      | nil =>
      simp only [topAt_top]
      iexists nodeMaxO l.maxEnd e mh
      iframe Hmx
      isplitl []
      · ipureintro; rfl
      iintro Hmx
      iframe
      ipureintro; exact Hp
    · icases ownPathAt_top_max s C ls p pp _ hC $$ H with ⟨%M, %HM, Hm, Hback⟩
      iexists M
      iframe Hm
      isplitl []
      · ipureintro; exact HM
      iintro Hm
      ihave H := Hback $$ Hm
      iframe
      ipureintro; exact Hp

/-- A subtree is the leaf exactly at the sentinel. -/
theorem ownNode_leaf_iff (s : Loc) (q : Qp) (p n : Loc) (T : RbT Entry) :
    ownNode (GF := GF) s q p n T ⊢ ⌜n = s ↔ T = .leaf⌝ := by
  cases T with
  | leaf => rw [ownNode_leaf]; iintro %h; ipureintro; simp [h]
  | node c l e r =>
    iintro H
    ihave %Hn := ownNode_node_ne _ _ _ _ _ _ _ _ $$ H
    ipureintro; simp [Hn.1]

/-- The child `Delete` splices in for a node with at most one child: the left one if it is a
node, else the right one (the other one dropped: it is the leaf). -/
theorem ownNode_one_child (s z lp rp : Loc) (l r : RbT Entry) :
    ownNode (GF := GF) s 1 z lp l ∗ ownNode s 1 z rp r ⊢
      ownNode s 1 z (if lp = s then rp else lp) (if lp = s then r else l) := by
  iintro ⟨Hl, Hr⟩
  by_cases h : lp = s
  · simp only [h, ↓reduceIte]; iexact Hr
  · simp only [h, ↓reduceIte]; iexact Hl

/-- The `max` of a path's top node, as `updateMax` reads it from the node above (the hole's
subtree's root when the path is empty), lent out. -/
theorem ownPathAt_childMax (s : Loc) (A : RbCtx Entry) (ls : List (Loc × Loc)) (n p : Loc)
    (T : RbT Entry) :
    ownPathAt (GF := GF) s 1 A ls n p T.maxEnd ∗ ownNode s 1 p n T ⊢
      childMax s (topAt A ls n p).1 (A.upMax T.maxEnd) ∗
        (childMax s (topAt A ls n p).1 (A.upMax T.maxEnd) -∗
          ownPathAt s 1 A ls n p T.maxEnd ∗ ownNode s 1 p n T) := by
  by_cases hA : A = .top
  · subst hA
    cases ls with
    | cons f ls => rw [ownPathAt_top_cons]; iintro ⟨%h, -⟩; exact h.elim
    | nil =>
    rw [ownPathAt_top]
    simp only [topAt_top, RbCtx.upMax]
    iintro ⟨-, Hn⟩
    icases ownNode_childMax _ _ _ T $$ Hn with ⟨Hm, Hback⟩
    iframe Hm
    iintro Hm
    ihave Hn := Hback $$ Hm
    iframe
  · iintro ⟨HP, Hn⟩
    ihave %Hne := ownPathAt_top_ne s 1 A ls n p _ hA $$ HP
    icases ownPathAt_top_max s A ls n p _ hA $$ HP with ⟨%M, %HM, Hm, Hback⟩
    rw [HM, childMax_some]
    isplitl [Hm]
    · iframe; ipureintro; exact Hne
    iintro ⟨-, Hm⟩
    ihave HP := Hback $$ Hm
    iframe

theorem colorAt_intro (s n : Loc) (c : RbColor) (dq : DFrac) (h : n ≠ s) :
    n.[intervalNode, go!"c"] ↦{dq} colorW c ⊢ colorAt (GF := GF) s n c dq := by
  unfold colorAt
  iintro H; iright; iframe; ipureintro; exact h

theorem colorAt_elim (s n : Loc) (c : RbColor) (dq : DFrac) (h : n ≠ s) :
    colorAt (GF := GF) s n c dq ⊢ n.[intervalNode, go!"c"] ↦{dq} colorW c := by
  unfold colorAt
  iintro (%h' | ⟨-, H⟩)
  · exact absurd h'.1 h
  · iexact H

end ctx

end adt
end EtcdGrove
end Perennial
