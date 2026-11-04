/-
`rebalance`'s three steps on the logical tree (U8b, `notes/bbolt-proof-plan.md`), over any
`LTree` (`L` before, `L'` after, equal off the positions the step changes):
- **merge** (`rt_merge`): the parent `P`'s entries `k`, `k + 1` (positions `A`, `R`, of one kind)
  become one, `A`'s, holding `A`'s entries then `R`'s; `R` is gone;
- **removal** (`rt_remove`): the parent `P`'s entry `k`, an empty leaf `E`, is gone;
- **root collapse** (`rt_collapse`): the root `P`, a branch of one entry (position `C`), takes
  `C`'s kind and entries; `C` is gone.

Each keeps the leaves' entries (flattened: the data), does not grow the height, keeps the leaves
at one depth (one less after a collapse), and keeps the positions but the one gone. The changed
positions occur where the step expects them: a child position `A`, `R`, `E`, `C` only under `P`
(`RTree.edge`), which the bucket's records give (`Rebalance/RTreeX.lean`).
-/
module

public import Proof.go_etcd_io.bbolt.Rebalance.RTreeRep

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section steps
variable [GooseExts]

namespace RTree

mutual
/-- Every subtree (the tree itself first). -/
def subs : RTree → List RTree
  | mk p lf ws cs => mk p lf ws cs :: subsL cs
def subsL : List RTree → List RTree
  | [] => []
  | t :: ts => subs t ++ subsL ts
end

/-- `c` is the position of a child of a branch at position `x` in `t`. -/
def edge (t : RTree) (x c : w64) : Prop :=
  ∃ s ∈ t.subs, s.pid = x ∧ s.lf = false ∧ c ∈ s.cs.map RTree.pid

end RTree

open RTree

/-- The data, height, depths and positions `t'` keeps of `t`, the position `gone` removed
(`dd` the depth change of the leaves: `0`, or `1` for a collapse). -/
def rtKept (t t' : RTree) (gone : w64) (dd : Nat) : Prop :=
  t'.pid = t.pid ∧ t'.lvs.flatten = t.lvs.flatten ∧ t'.ht ≤ t.ht ∧
  (∀ D, (∀ x ∈ t.dps 0, x = D) → ∀ x ∈ t'.dps 0, x = D - dd) ∧
  (∀ x ∈ t'.pos, x ∈ t.pos ∧ x ≠ gone) ∧ (∀ x ∈ t.pos, x ≠ gone → x ∈ t'.pos)

/-- **The merge** of `P`'s children `k` (position `A`) and `k + 1` (`R`), of one kind `lf`. -/
theorem rt_merge (L L' : LTree) (bl : Loc) (t : RTree) (ht : ltIs L bl t)
    (P A R : w64) (k : Nat) (wsP wsA wsR : List WEntry) (lf : Bool) (wa wr : WEntry)
    (hPA : P ≠ A) (hPR : P ≠ R) (hAR : A ≠ R)
    (hP : L bl P = some (false, wsP)) (hwa : wsP[k]? = some wa) (hwr : wsP[k + 1]? = some wr)
    (hA : wa.pgid = A) (hR : wr.pgid = R)
    (hLA : L bl A = some (lf, wsA)) (hLR : L bl R = some (lf, wsR))
    (h'P : L' bl P = some (false, wsP.eraseIdx (k + 1)))
    (h'A : L' bl A = some (lf, wsA ++ wsR))
    (hfr : ∀ q, q ≠ P → q ≠ A → q ≠ R → L' bl q = L bl q)
    (hroot : t.pid ≠ A ∧ t.pid ≠ R) (hedge : ∀ x c, edge t x c → (c = A ∨ c = R) → x = P) :
    ∃ t', ltIs L' bl t' ∧ rtKept t t' R 0 := by
  sorry

/-- **The removal** of `P`'s child `k`, the empty leaf at position `E`. -/
theorem rt_remove (L L' : LTree) (bl : Loc) (t : RTree) (ht : ltIs L bl t)
    (P E : w64) (k : Nat) (wsP : List WEntry) (we : WEntry) (hPE : P ≠ E)
    (hP : L bl P = some (false, wsP)) (hwe : wsP[k]? = some we) (hE : we.pgid = E)
    (hLE : L bl E = some (true, []))
    (h'P : L' bl P = some (false, wsP.eraseIdx k))
    (hfr : ∀ q, q ≠ P → q ≠ E → L' bl q = L bl q)
    (hroot : t.pid ≠ E) (hedge : ∀ x c, edge t x c → c = E → x = P) :
    ∃ t', ltIs L' bl t' ∧ rtKept t t' E 0 := by
  sorry

/-- **The root collapse**: the root `P`, a branch of one entry (position `C`), takes `C`'s kind
and entries. -/
theorem rt_collapse (L L' : LTree) (bl : Loc) (t : RTree) (ht : ltIs L bl t)
    (P C : w64) (w0 : WEntry) (lf : Bool) (wsC : List WEntry) (hPC : P ≠ C) (hroot : t.pid = P)
    (hP : L bl P = some (false, [w0])) (hC : w0.pgid = C) (hLC : L bl C = some (lf, wsC))
    (h'P : L' bl P = some (lf, wsC))
    (hfr : ∀ q, q ≠ P → q ≠ C → L' bl q = L bl q)
    (hedge : ∀ x c, edge t x c → c = C → x = P) :
    ∃ t', ltIs L' bl t' ∧ rtKept t t' C 1 := by
  sorry

/-- **A step that changes no position of the tree** (the unbalanced flags, the parents, another
bucket's records). -/
theorem rt_frame (L L' : LTree) (bl : Loc) (t : RTree) (ht : ltIs L bl t)
    (hfr : ∀ q ∈ t.pos, L' bl q = L bl q) : ltIs L' bl t := by
  sorry

end steps

end bbolt
end EtcdGrove
end Perennial
