/-
# etcd's interval tree: internal vocabulary (batch 3f)

What the specs of the tree's internal helpers (`intervalNode.{color,min,successor,updateMax,visit}`,
`intervalTree.{find,createIntervalNode,insertFixup,deleteFixup,rotateLeft,rotateRight,
replaceParent}`) are stated over: the red-black model of the nodes, and the ownership of subtrees,
of a tree with a hole (a zipper context), of the sentinel. Ported from `specs-ref`'s proof
(`Proof/go_etcd_io/etcd/pkg/v3/adt/{Tree,TreeInsert,TreeDelete,Defs,Ctx,CtxAt,Holes}.lean`, where
these helpers have proofs), at a key kind `c : Cmp` in place of a key representation. No client of
the package sees these names (`Api.lean`'s `ivt` is realized from them: the tree struct, the
sentinel, `ownNode` from the root over a red-black `RbT` whose in-order list is the entries).

## The model (pure, transparent)

`RbColor`, `RbT` (a leaf, the sentinel; or a node with its colour, children and entry), its in-order
list, colour, black height, `redOk`, `RbOk` (the red-black invariant, the root black); the `max`
augmentation (`affMaxO`, `RbT.maxEnd`, `nodeMax`, `nodeMaxO`); `RbT.findE` (`find`'s descent);
`RbCtx` (a path from the root to a hole, innermost frame first) with `plug`, its colour, the
invariants through a context (`bhOk`, `redOk`, `redOkX`), `AllL` (only left frames: `min`'s path),
`FixInv` (CLRS 13.3's `insertFixup` invariant), `DelInv` (13.4's `deleteFixup` invariant); `topAt`
(the top of a path with its frames' locations).

## Resources (opaque; intended definitions)

* `ownNode c s dq p n T`: the subtree at `n` (child of `p`) holding `T`, sentinel `s`: the leaf is
  `n = s`; a node `n ≠ s, null` with its fields at `dq`: `iv` (`ivAt` of its entry), `max`
  (`maxAt`: `nodeMax` of its subtree), `left`/`right` (its children's subtrees), `parent` (`p`),
  `c` (`colorW`).
* `ownSentinel s dq`: the sentinel's struct, any value.
* `ownCtx c t s C n p mh`: the path from the root (the tree's `root` field) to the hole at `n`
  (child of `p`) in the context `C`, the hole's subtree's max `mh`: each frame's node with its
  fields, its `max` as `updateMax` computes it from `mh`, its other subtree.
* `ownPathAt c s dq A ls n p mh`: the same from the top of the path `A`, the frames' parents and
  other children listed in `ls`, at `dq`; `ownCtxAt c t s C ls n p mh` the path from the root
  (`ownPathAt` with the top's parent the sentinel and the tree's `root` at the top).
* `childMax c s n mo`: what `updateMax` reads of a child: nothing at the sentinel, else its `max`.
* `colorAt s x k dq`: what `color(sentinel)` reads: black at the sentinel, else the `c` field.
* `sentAt s x p`: the sentinel, its `parent` field `p` when the hole `x` is the sentinel (`Delete`
  writes it; `deleteFixup` reads it back).
* `ownNodeH c s dq p n T ns es`: `ownNode` with the nodes `ns` (entries `es`, in order) having lent
  their `iv` fields out (`visit`'s visitor keeps them).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.adt.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Adt

open Iris Iris.BI go_etcd_io.etcd.pkg.v3.adt
open Classical

/-! ## The red-black model -/

/-- A node's colour (`rbcolor`: `black` is `0`, `red` is `1`). -/
inductive RbColor where
  | red
  | black

/-- The tree: a leaf (the sentinel), or a node with its colour, its children and its entry. -/
inductive RbT (E : Type) where
  | leaf : RbT E
  | node (c : RbColor) (l : RbT E) (e : E) (r : RbT E) : RbT E

namespace RbT
variable {E : Type}

def inorder : RbT E → List E
  | leaf => []
  | node _ l e r => l.inorder ++ e :: r.inorder

/-- The colour (the sentinel is black). -/
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

/-- A red node has black children. -/
def redOk : RbT E → Prop
  | leaf => True
  | node c l _ r => (c = .red → l.color = .black ∧ r.color = .black) ∧ l.redOk ∧ r.redOk

/-- The red-black condition below the root. -/
def redOkBelow : RbT E → Prop
  | leaf => True
  | node _ l _ r => l.redOk ∧ r.redOk

end RbT

/-- `updateMax`'s step: the larger of `m` and the child's max (if any), under `affCmp`. -/
def affMaxO (m : GoString) : Option GoString → GoString
  | none => m
  | some x => if affCmp x m > 0 then x else m

section entries
variable [GooseExts]

/-- The largest end of a subtree's entries; `none` for the leaf. -/
def RbT.maxEnd : RbT Entry → Option GoString
  | .leaf => none
  | .node _ l e r => some (affMaxO (affMaxO e.1.2 l.maxEnd) r.maxEnd)

/-- A node's `max` field. -/
def nodeMax (l : RbT Entry) (e : Entry) (r : RbT Entry) : GoString :=
  affMaxO (affMaxO e.1.2 l.maxEnd) r.maxEnd

/-- A node's max from its children's maxima. -/
def nodeMaxO (lo : Option GoString) (e : Entry) (ro : Option GoString) : GoString :=
  affMaxO (affMaxO e.1.2 lo) ro

/-- The red-black invariant: a red node's children black, one black height, the root black. -/
def RbOk (t : RbT Entry) : Prop := t.redOk ∧ t.blackHeight.isSome ∧ t.color = .black

/-- `find`'s descent: by begin, then end; the entry with exactly the interval `k`. -/
def RbT.findE (k : IvlS) : RbT Entry → Option Entry
  | .leaf => none
  | .node _ l e r =>
    if affCmp k.1 e.1.1 = 0 ∧ affCmp k.2 e.1.2 = 0 then some e
    else if affCmp k.1 e.1.1 < 0 then l.findE k
    else if affCmp k.1 e.1.1 = 0 then (if affCmp k.2 e.1.2 < 0 then l.findE k else r.findE k)
    else r.findE k

end entries

/-- A path from the root to a hole, innermost frame first. -/
inductive RbCtx (E : Type) where
  | top : RbCtx E
  | inL (c : RbColor) (p : RbCtx E) (e : E) (r : RbT E) : RbCtx E
  | inR (c : RbColor) (l : RbT E) (e : E) (p : RbCtx E) : RbCtx E

namespace RbCtx
variable {E : Type}

/-- The tree with `t` in the hole. -/
def plug : RbCtx E → RbT E → RbT E
  | top, t => t
  | inL c p e r, t => plug p (.node c t e r)
  | inR c l e p, t => plug p (.node c l e t)

/-- The colour of the hole's parent (the sentinel's, black, at the top). -/
def color : RbCtx E → RbColor
  | top => .black
  | inL c _ _ _ => c
  | inR c _ _ _ => c

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

/-- Every frame a left one (`min`'s path). -/
def AllL : RbCtx E → Prop
  | top => True
  | inL _ A _ _ => A.AllL
  | inR _ _ _ _ => False

/-- `insertFixup`'s loop invariant at the subtree `t` (CLRS 13.3). -/
def FixInv (C : RbCtx E) (t : RbT E) : Prop :=
  t.color = .red ∧ t.redOk ∧ (∃ h, t.blackHeight = some h ∧ C.bhOk h) ∧ C.redOkX ∧
    (C = .top ∨ (plug C t).color = .black)

/-- `deleteFixup`'s loop invariant at the subtree `t` (CLRS 13.4: `t` doubly black). -/
def DelInv (C : RbCtx E) (t : RbT E) : Prop :=
  t.redOkBelow ∧ (∃ h, t.blackHeight = some h ∧ C.bhOk (h + 1)) ∧ C.redOkX ∧
    (C = .top ∨ (plug C t).color = .black)

end RbCtx

section top
variable [GooseExts]

/-- The top of a path (its node and parent), the frames' locations listed innermost first. -/
def topAt : RbCtx Entry → List (Loc × Loc) → Loc → Loc → Loc × Loc
  | .top, _, n, p => (n, p)
  | .inL _ _ _ _, [], n, p => (n, p)
  | .inR _ _ _ _, [], n, p => (n, p)
  | .inL _ C _ _, (pp, _) :: ls, _, p => topAt C ls p pp
  | .inR _ _ _ C, (pp, _) :: ls, _, p => topAt C ls p pp

end top

/-! ## Resources -/

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- A node's colour as its Go value. -/
def colorW : RbColor → w64
  | .black => W64 0
  | .red => W64 1

/-- **A node's `max` field** at `l` holds the key `m`: a comparable of a key value (read-only). -/
def maxAt (c : Cmp) (l : Loc) (dq : DFrac) (m : GoString) : IProp GF :=
  iprop(∃ vm : val, l ↦{dq} interface.mkOk c.ty vm ∗ keyAt c DFrac.discard vm m)

/-- The subtree at `n` (child of `p`) holding `T`. -/
opaque ownNode [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (c : Cmp) (s : Loc) (dq : DFrac) (p n : Loc) (T : RbT Entry) : IProp GF := iprop(True)

/-- The sentinel's struct. -/
opaque ownSentinel [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (s : Loc) (dq : DFrac) : IProp GF := iprop(True)

/-- The path from the root to the hole at `n` (child of `p`) in the context `C`. -/
opaque ownCtx [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (c : Cmp) (t s : Loc) (C : RbCtx Entry) (n p : Loc) (mh : Option GoString) :
  IProp GF := iprop(True)

/-- The path from the top of `A` to the hole at `n`, its frames' locations `ls`. -/
opaque ownPathAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (c : Cmp) (s : Loc) (dq : DFrac) (A : RbCtx Entry) (ls : List (Loc × Loc))
  (n p : Loc) (mh : Option GoString) : IProp GF := iprop(True)

/-- `ownPathAt` from the root (the tree's `root` field at the top, the top's parent the
sentinel). -/
opaque ownCtxAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (c : Cmp) (t s : Loc) (C : RbCtx Entry) (ls : List (Loc × Loc)) (n p : Loc)
  (mh : Option GoString) : IProp GF := iprop(True)

/-- What `updateMax` reads of a child. -/
opaque childMax [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (c : Cmp) (s n : Loc) (mo : Option GoString) : IProp GF := iprop(True)

/-- What `color(sentinel)` reads at `x`. -/
opaque colorAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (s x : Loc) (k : RbColor) (dq : DFrac) : IProp GF := iprop(True)

/-- The sentinel, its `parent` field `p` when the hole `x` is the sentinel. -/
opaque sentAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (s x p : Loc) : IProp GF := iprop(True)

/-- `ownNode` with the nodes `ns` (entries `es`) having lent their `iv` fields out. -/
opaque ownNodeH [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (c : Cmp) (s : Loc) (dq : DFrac) (p n : Loc) (T : RbT Entry) (ns : List Loc)
  (es : List Entry) : IProp GF := iprop(True)

/-- **The contract of `visit`'s node visitor** (`Visit`'s closure around the caller's `ivv`): on
each visited node, in order, its `iv` lent and kept. -/
def nodeVisitorOk (c : Cmp) (dq : DFrac) (S : List Entry) (hq : Prop) (nv : GoFunc)
    (I J : List (Loc × Entry) → IProp GF) : IProp GF :=
  iprop(□ ∀ (n : Loc) (z : Entry) (acc : List (Loc × Entry)),
    {{ ⌜List.Sublist (acc.map Prod.snd ++ [z]) S ∧ (hq → acc.map Prod.snd ++ [z] <+: S)⌝ ∗ I acc ∗
        ivAt c (n.[intervalNode, go!"iv"]) dq z }}
      (App (Val #nv) (Val #n))
    {{ (r : Bool), RET #r; if r then I (acc ++ [(n, z)]) else J (acc ++ [(n, z)]) }})

end res

end Adt
end EtcdGrove
end Perennial
