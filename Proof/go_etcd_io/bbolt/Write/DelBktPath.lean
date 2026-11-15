/-
U7j (`notes/bbolt-proof-plan.md`; U7h's finding (b) for `DeleteBucket`): **a search's stack stays a
search's stack** across changes that leave the searched bucket's tree alone. `DeleteBucket`
searches the root bucket (`c.seek(newKey)`) and only after opening the child (`b.Bucket`),
deleting it from the root's cache (`delete(b.buckets, …)`), and freeing it (`child.free()`) asks
the cursor for the leaf (`c.node().del(newKey)`); none of these changes the root bucket's tree
(its header's root, root node, page, inline page, node cache and nodes; `sameTreeB`), so the
stack, its routing and its leaf are the same (`lPath_congr_bkt`, `lRoutes_congr_bkt`,
`lLeaf_congr_bkt`).
-/
module

public import Proof.go_etcd_io.bbolt.Model.WOps

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt


namespace Write

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section delbktpath
variable [GooseExts]

/-- Two records of a bucket with the same tree: the fields `ltree`, `refAt` and the root position
read. -/
def sameTreeB (B B' : BRec) : Prop :=
  B'.ib.root' = B.ib.root' ∧ B'.bv.rootNode' = B.bv.rootNode' ∧ B'.nm = B.nm ∧ B'.ns = B.ns ∧
    B'.bv.page' = B.bv.page' ∧ B'.ipg = B.ipg

theorem sameTreeB_bm (B : BRec) (bm : GMap GoString Loc) : sameTreeB B { B with bm := bm } :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem resolve_congr (B B' : BRec) (h : sameTreeB B B') : resolve B' = resolve B := by
  obtain ⟨h1, h2, h3, -, -, -⟩ := h
  funext pid; unfold resolve; rw [h1, h2, h3]

theorem wpageAt_congr (v : View) (B B' : BRec) (h : sameTreeB B B') :
    wpageAt v B' = wpageAt v B := by
  obtain ⟨h1, -, -, -, h5, h6⟩ := h
  funext pid; unfold wpageAt; rw [h1, h5, h6]

section congr
variable (X X' : WX) (bl : Loc) (B B' : BRec) (hv : X'.v = X.v) (hB : X.t.bs !! bl = some B)
  (hB' : X'.t.bs !! bl = some B') (h : sameTreeB B B')
include hv hB hB' h

theorem ltree_congr_bkt : ltree X' bl = ltree X bl := by
  funext pid
  unfold ltree
  rw [hB, hB', hv]
  simp only
  rw [resolve_congr B B' h, wpageAt_congr X.v B B' h, h.2.2.2.1]

theorem refAt_congr_bkt : refAt X' bl = refAt X bl := by
  funext pid e
  unfold refAt
  rw [hB, hB', hv]
  simp only [Option.some.injEq, exists_eq_left']
  rw [resolve_congr B B' h, wpageAt_congr X.v B B' h]

theorem rootPid_congr_bkt : X'.rootPid bl = X.rootPid bl := by
  unfold WX.rootPid; rw [hB, hB']; simp [h.1]

/-- **A stack of the bucket stays one.** -/
theorem lPath_congr_bkt (els : List elemRef) (pids : List w64) :
    lPath X' bl els pids ↔ lPath X bl els pids := by
  unfold lPath
  rw [rootPid_congr_bkt X X' bl B B' hv hB hB' h, refAt_congr_bkt X X' bl B B' hv hB hB' h,
    ltree_congr_bkt X X' bl B B' hv hB hB' h]

/-- **Its routing stays.** -/
theorem lRoutes_congr_bkt (els : List elemRef) (pids : List w64) (k : List w8) :
    lRoutes X' bl els pids k ↔ lRoutes X bl els pids k := by
  unfold lRoutes
  rw [ltree_congr_bkt X X' bl B B' hv hB hB' h]

/-- **Its leaf stays.** -/
theorem lLeaf_congr_bkt (pids : List w64) : lLeaf X' bl pids = lLeaf X bl pids := by
  unfold lLeaf
  rw [ltree_congr_bkt X X' bl B B' hv hB hB' h]

end congr

end delbktpath

end Write

end bbolt
end EtcdGrove
end Perennial
