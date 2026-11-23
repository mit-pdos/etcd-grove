/-
**gods' red-black tree** (`github.com/emirpasic/gods/trees/redblacktree`, v1.18.1 through its model
`models/gods`: gods' code but the iterator's `Next`/`Prev` without `goto`; notes/gods-verified.md):
the specs of the functions the treemap reaches from the kits' calls (`NewWith`, `Put` with its
`insertCase` fix-up and rotations, `Get` through `lookup`, `Iterator`, `Left`, the iterator's
`Next`, `Value`, `Key`), over the representation of `Defs.lean` (`isTree`, `treeRaw`, `ownIterR`).

The public functions' specs are over `isTree tr enc es` (the entries `es`); the internal ones over
`treeRaw` (the model tree `T` and the heap function `h` explicit), since the fix-up's
intermediate trees break the root's color, and each states what it does to `T`.
-/
module

public import Dsverify.Proof.github_com.emirpasic.gods.trees.redblacktree.Defs

@[expose] public section

noncomputable section

namespace Perennial.github_com.emirpasic.gods.trees.redblacktree

open Iris Iris.BI Iris.ProgramLogic Iris.Std
open github_com.emirpasic.gods.maps.treemap (cmpOk sortedE Entries lookupE putE)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [redblacktree.Assumptions]

/-- `NewWith(cmp)`: an empty tree. -/
abbrev NewWith.spec : Prop :=
  ∀ (cmp : GoFunc) (enc : w64 → GoInterface),
  {{ cmpOk (GF := GF) cmp enc }}
    (App (Val (@! redblacktree.NewWith)) (Val #cmp))
  {{ (tr : Loc), RET #tr; isTree tr enc [] }}

/-- `tree.Put(enc k, v)`. -/
abbrev Tree.Put.spec : Prop :=
  ∀ (tr : Loc) (enc : w64 → GoInterface) (es : Entries) (k : w64) (v : GoInterface),
  {{ isTree (GF := GF) tr enc es }}
    (App (App (Val (tr @!! go.GoType.PointerType Tree.ty @!! go!"Put")) (Val #(enc k))) (Val #v))
  {{ RET #(); isTree tr enc (putE es k v) }}

/-- `tree.Get(enc k)`. -/
abbrev Tree.Get.spec : Prop :=
  ∀ (tr : Loc) (enc : w64 → GoInterface) (es : Entries) (k : w64),
  {{ isTree (GF := GF) tr enc es }}
    (App (Val (tr @!! go.GoType.PointerType Tree.ty @!! go!"Get")) (Val #(enc k)))
  {{ RET (PairV #((lookupE es k).getD interface.nil) #((lookupE es k).isSome));
      isTree tr enc es }}

/-- `tree.lookup(enc k)`: `k`'s node or `nil`. -/
abbrev Tree.lookup.spec : Prop :=
  ∀ (tr : Loc) (enc : w64 → GoInterface) (cmp : GoFunc) (T : RB GoInterface) (h : Loc → Node)
    (D : List Loc) (k : w64),
  {{ treeRaw (GF := GF) tr enc cmp T h D ∗ cmpOk cmp enc ∗ ⌜sortedE T.entries⌝ }}
    (App (Val (tr @!! go.GoType.PointerType Tree.ty @!! go!"lookup")) (Val #(enc k)))
  {{ (n : Loc), RET #n; treeRaw tr enc cmp T h D ∗ ⌜lookupRes T k n⌝ }}

/-- `tree.Iterator()`: before the first entry. -/
abbrev Tree.Iterator.spec : Prop :=
  ∀ (tr : Loc),
  {{ (True : IProp GF) }}
    (App (Val (tr @!! go.GoType.PointerType Tree.ty @!! go!"Iterator")) (Val #()))
  {{ RET #(Iterator.mk tr null (W8 0)); True }}

/-- `tree.Left()`: the leftmost node, `nil` if none. -/
abbrev Tree.Left.spec : Prop :=
  ∀ (tr : Loc) (enc : w64 → GoInterface) (cmp : GoFunc) (T : RB GoInterface) (h : Loc → Node)
    (D : List Loc),
  {{ treeRaw (GF := GF) tr enc cmp T h D }}
    (App (Val (tr @!! go.GoType.PointerType Tree.ty @!! go!"Left")) (Val #()))
  {{ (m : Loc), RET #m; treeRaw tr enc cmp T h D ∗ ⌜leftmost T m⌝ }}

/-- `iterator.Next()`: the next entry, if any. -/
abbrev Iterator.Next.spec : Prop :=
  ∀ (q : Loc) (enc : w64 → GoInterface) (rest : Entries) (cur : Option (w64 × GoInterface)),
  {{ ownIterR (GF := GF) q enc rest cur }}
    (App (Val (q @!! go.GoType.PointerType Iterator.ty @!! go!"Next")) (Val #()))
  {{ (b : Bool), RET #b;
      match rest with
      | [] => ⌜b = false⌝ ∗ ownIterR q enc [] none
      | e :: r => ⌜b = true⌝ ∗ ownIterR q enc r (some e) }}

/-- `iterator.Value()` at the entry `(k, v)`. -/
abbrev Iterator.Value.spec : Prop :=
  ∀ (q : Loc) (enc : w64 → GoInterface) (rest : Entries) (k : w64) (v : GoInterface),
  {{ ownIterR (GF := GF) q enc rest (some (k, v)) }}
    (App (Val (q @!! go.GoType.PointerType Iterator.ty @!! go!"Value")) (Val #()))
  {{ RET #v; ownIterR q enc rest (some (k, v)) }}

/-- `iterator.Key()` at the entry `(k, v)`. -/
abbrev Iterator.Key.spec : Prop :=
  ∀ (q : Loc) (enc : w64 → GoInterface) (rest : Entries) (k : w64) (v : GoInterface),
  {{ ownIterR (GF := GF) q enc rest (some (k, v)) }}
    (App (Val (q @!! go.GoType.PointerType Iterator.ty @!! go!"Key")) (Val #()))
  {{ RET #(enc k); ownIterR q enc rest (some (k, v)) }}

/-! ### The fix-up after an insertion -/

/-- `tree.replaceNode(old, new)` (`replaceRes`): `old`'s parent `p` is `nil` and `old` the root,
or a node with `old` as a child; `new` is `nil` or a node; `old` is not its own parent. -/
abbrev Tree.replaceNode.spec : Prop :=
  ∀ (tr : Loc) (rt : Loc) (sz : w64) (cmp : GoFunc) (h : Loc → Node) (D : List Loc)
    (old new : Loc),
  {{ tr ↦ Tree.mk rt sz cmp ∗ ownNodes (GF := GF) h D ∗
      ⌜D.Nodup ∧ old ∈ D ∧ (h old).Parent' ≠ old ∧ (new = null ∨ new ∈ D) ∧
        ((h old).Parent' = null ∨ ((h old).Parent' ∈ D ∧
          ((h (h old).Parent').Left' = old ∨ (h (h old).Parent').Right' = old)))⌝ }}
    (App (App (Val (tr @!! go.GoType.PointerType Tree.ty @!! go!"replaceNode")) (Val #old))
      (Val #new))
  {{ RET #(); tr ↦ Tree.mk (replaceRes rt h old new).1 sz cmp ∗
      ownNodes (replaceRes rt h old new).2 D }}

/-- `tree.rotateLeft(n)` at the subtree `node n A (node r B E)` in the context `C`. -/
abbrev Tree.rotateLeft.spec : Prop :=
  ∀ (tr : Loc) (enc : w64 → GoInterface) (cmp : GoFunc) (C : Ctx GoInterface) (h : Loc → Node)
    (D : List Loc) (n : Loc) (k : w64) (v : GoInterface) (c : Bool) (A : RB GoInterface)
    (r : Loc) (k' : w64) (v' : GoInterface) (c' : Bool) (B E : RB GoInterface),
  {{ treeRaw (GF := GF) tr enc cmp (Ctx.plug C (.node n k v c A (.node r k' v' c' B E))) h D }}
    (App (Val (tr @!! go.GoType.PointerType Tree.ty @!! go!"rotateLeft")) (Val #n))
  {{ RET #(); ∃ h', treeRaw tr enc cmp (Ctx.plug C (.node r k' v' c' (.node n k v c A B) E)) h' D }}

/-- `tree.rotateRight(n)` at the subtree `node n (node l A B) E` in the context `C`. -/
abbrev Tree.rotateRight.spec : Prop :=
  ∀ (tr : Loc) (enc : w64 → GoInterface) (cmp : GoFunc) (C : Ctx GoInterface) (h : Loc → Node)
    (D : List Loc) (n : Loc) (k : w64) (v : GoInterface) (c : Bool) (l : Loc) (k' : w64)
    (v' : GoInterface) (c' : Bool) (A B E : RB GoInterface),
  {{ treeRaw (GF := GF) tr enc cmp (Ctx.plug C (.node n k v c (.node l k' v' c' A B) E)) h D }}
    (App (Val (tr @!! go.GoType.PointerType Tree.ty @!! go!"rotateRight")) (Val #n))
  {{ RET #(); ∃ h', treeRaw tr enc cmp (Ctx.plug C (.node l k' v' c' A (.node n k v c B E))) h' D }}

/-- The fix-up's result: the same entries, the root black. -/
def fixPost (tr : Loc) (enc : w64 → GoInterface) (cmp : GoFunc) (T : RB GoInterface)
    (D : List Loc) : IProp GF :=
  iprop(∃ (T' : RB GoInterface) (h' : Loc → Node), treeRaw tr enc cmp T' h' D ∗
    ⌜T'.entries = T.entries ∧ T'.color = true⌝)

/-- `tree.insertCase1(n)`, `n` a node of `T` (in the context `C`): the root is black unless it
is `n`. -/
abbrev Tree.insertCase1.spec : Prop :=
  ∀ (tr : Loc) (enc : w64 → GoInterface) (cmp : GoFunc) (C : Ctx GoInterface)
    (h : Loc → Node) (D : List Loc) (n : Loc) (k : w64) (v : GoInterface) (c : Bool)
    (L R : RB GoInterface),
  {{ treeRaw (GF := GF) tr enc cmp (Ctx.plug C (.node n k v c L R)) h D ∗
      ⌜(Ctx.plug C (.node n k v c L R)).color = true ∨ C = []⌝ }}
    (App (Val (tr @!! go.GoType.PointerType Tree.ty @!! go!"insertCase1")) (Val #n))
  {{ RET #(); fixPost tr enc cmp (Ctx.plug C (.node n k v c L R)) D }}

/-- `tree.insertCase4(n)`, `n` with a parent and a grandparent, the root black. -/
abbrev Tree.insertCase4.spec : Prop :=
  ∀ (tr : Loc) (enc : w64 → GoInterface) (cmp : GoFunc) (f1 f2 : Frame GoInterface)
    (C : Ctx GoInterface) (h : Loc → Node) (D : List Loc) (S : RB GoInterface),
  {{ treeRaw (GF := GF) tr enc cmp (Ctx.plug (f1 :: f2 :: C) S) h D ∗
      ⌜S ≠ .leaf ∧ (Ctx.plug (f1 :: f2 :: C) S).color = true⌝ }}
    (App (Val (tr @!! go.GoType.PointerType Tree.ty @!! go!"insertCase4")) (Val #S.loc))
  {{ RET #(); fixPost tr enc cmp (Ctx.plug (f1 :: f2 :: C) S) D }}

/-- Two frames on the same side (a "zig-zig"). -/
def sameSide {α : Type} : Frame α → Frame α → Prop
  | .L .., .L .. => True
  | .R .., .R .. => True
  | _, _ => False

/-- `tree.insertCase5(n)`, `n` with a parent and a grandparent on the same side, the root black. -/
abbrev Tree.insertCase5.spec : Prop :=
  ∀ (tr : Loc) (enc : w64 → GoInterface) (cmp : GoFunc) (f1 f2 : Frame GoInterface)
    (C : Ctx GoInterface) (h : Loc → Node) (D : List Loc) (S : RB GoInterface),
  {{ treeRaw (GF := GF) tr enc cmp (Ctx.plug (f1 :: f2 :: C) S) h D ∗
      ⌜S ≠ .leaf ∧ sameSide f1 f2 ∧ (Ctx.plug (f1 :: f2 :: C) S).color = true⌝ }}
    (App (Val (tr @!! go.GoType.PointerType Tree.ty @!! go!"insertCase5")) (Val #S.loc))
  {{ RET #(); fixPost tr enc cmp (Ctx.plug (f1 :: f2 :: C) S) D }}

end spec

end Perennial.github_com.emirpasic.gods.trees.redblacktree
