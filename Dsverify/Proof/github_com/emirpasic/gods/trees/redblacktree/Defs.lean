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

/-- The iterator at `q` over a tree it owns. -/
def ownIterR (q : Loc) (enc : w64 → GoInterface) (rest : Entries)
    (cur : Option (w64 × GoInterface)) : IProp GF :=
  iprop(∃ (tr : Loc) (cmp : GoFunc) (T : RB GoInterface) (h : Loc → Node) (D : List Loc)
      (nd : Loc) (pos : w8),
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

end Perennial.github_com.emirpasic.gods.trees.redblacktree
