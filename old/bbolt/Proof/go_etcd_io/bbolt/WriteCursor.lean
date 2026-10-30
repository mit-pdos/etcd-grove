/-
A cursor of a write transaction (pure): its stack refers to nodes and to pages.

A bucket's position `pid` (a page id) is its node, if materialized (`resolve`: `b.nodes[pid]`,
or for an inline bucket its root node), else its page (`wpageAt`: page `pid` of the view, or the
inline page). `posOK W hwm B pid`: the position is a node of the bucket, or a well-formed page
whose subtree has no node (in a clean bucket, every position a search reaches is one).
`wpath W B pid es`: the stack elements `es` are a path of references from position `pid` down
to a leaf, each element's index one of its entries, the next element its child.
-/
module

public import Proof.go_etcd_io.bbolt.WriteTxModel

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section cursor
variable [ext : FfiSyntax]

/-- The node at position `pid` of the bucket (`Bucket.pageNode`'s node). -/
def resolve (B : BRec) (pid : w64) : Option Loc :=
  if B.ib.root' = W64 0 then (if B.bv.rootNode' = null then none else some B.bv.rootNode')
  else B.nm !! pid

/-- The page at position `pid` of the bucket: where it is, its bytes. -/
def wpageAt (W : WView) (B : BRec) (pid : w64) : Option (Loc × List w8) :=
  if B.ib.root' = W64 0 then (if pid = W64 0 then some (B.bv.page', B.ipg) else none)
  else (W.pages !! uint.nat pid).map fun pg => (W.data +ₗ ((uint.nat pid * W.ps : Nat) : Int), pg)

/-- The position `pid` is a node of the bucket, or a page whose subtree has no node. -/
def posOK (W : WView) (hwm : Nat) (B : BRec) (pid : w64) : Prop :=
  (B.ib.root' = W64 0 → pid = W64 0) ∧
  ((∃ l r, resolve B pid = some l ∧ B.ns !! l = some r) ∨
  (resolve B pid = none ∧
    ((B.ib.root' = W64 0 ∧ pid = W64 0 ∧ B.bv.page' ≠ null ∧ B.isrc ≠ Src.stale ∧
        inlineOK B.ipg) ∨
     (B.ib.root' ≠ W64 0 ∧ treeWF W.pages hwm (uint.nat pid) ∧
        ∀ d, treeHas W.pages (uint.nat pid) d → B.nm !! W64 (d : Int) = none))))

/-- The stack element `r` refers to position `pid`. -/
def refAt (W : WView) (B : BRec) (pid : w64) (r : elemRef) : Prop :=
  (∃ l, resolve B pid = some l ∧ r.node' = l ∧ r.page' = null) ∨
  (resolve B pid = none ∧ r.node' = null ∧ ∃ pg, wpageAt W B pid = some (r.page', pg))

/-- Position `pid`: whether it is a leaf, and its children (none for a leaf). -/
def kidsAt (W : WView) (B : BRec) (pid : w64) : Option (Bool × List w64) :=
  match resolve B pid with
  | some l => (B.ns !! l).map fun r =>
      (r.nv.isLeaf', if r.nv.isLeaf' then [] else r.ws.map WEntry.pgid)
  | none => (wpageAt W B pid).map fun lp =>
      (decide (pageFlags lp.2 = leafPageFlag),
        if pageFlags lp.2 = leafPageFlag then []
        else (List.range (pageCount lp.2)).map fun i => W64 (branchPgid lp.2 i : Int))

/-- The stack elements `es` go from position `pid` down to a leaf (see the module doc). -/
def wpath (W : WView) (B : BRec) : w64 → List elemRef → Prop
  | _, [] => False
  | pid, [r] => refAt W B pid r ∧ 0 ≤ sint.Z r.index' ∧ ∃ ks, kidsAt W B pid = some (true, ks)
  | pid, r :: r2 :: rs => refAt W B pid r ∧ 0 ≤ sint.Z r.index' ∧ ∃ ks c,
      kidsAt W B pid = some (false, ks) ∧ ks[(sint.Z r.index').toNat]? = some c ∧
      wpath W B c (r2 :: rs)

end cursor

end bbolt
end EtcdGrove
end Perennial
