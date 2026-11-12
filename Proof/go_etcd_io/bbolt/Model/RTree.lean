/-
The logical tree as a finite tree, the definitions (moved from U8b's `Rebalance/RTree` and
`Rebalance/RTreeX` by batch 37, so that `spillPre` and `rebalOK` can say every bucket's tree is
finite, `rtOK`): `RTree`, its walks (`ht`, `lvs`, `pos`, `dps`), `ltIs L bl t` (the walk of `L`
from `t`'s root follows `t`), and `rtOK X bl` (bucket `bl`'s logical tree is such a finite tree of
height below the walks' fuel, its leaves at one depth). The lemmas stay in `Rebalance/RTree*`.
-/
module

public import Proof.go_etcd_io.bbolt.Model.LTree

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section lt
variable [GooseExts]

/-- A finite logical tree: each node's position, kind (leaf), entries and children. -/
inductive RTree where
  | mk (pid : w64) (lf : Bool) (ws : List WEntry) (cs : List RTree)

namespace RTree

def pid : RTree → w64 | mk p _ _ _ => p
def lf : RTree → Bool | mk _ b _ _ => b
def ws : RTree → List WEntry | mk _ _ w _ => w
def cs : RTree → List RTree | mk _ _ _ c => c

mutual
/-- The height (a leaf, or a branch without children, `0`). -/
def ht : RTree → Nat
  | mk _ _ _ cs => htL cs
def htL : List RTree → Nat
  | [] => 0
  | t :: ts => max (ht t + 1) (htL ts)
end

mutual
/-- The leaves' entries, in order. -/
def lvs : RTree → List (List WEntry)
  | mk _ true ws _ => [ws]
  | mk _ false _ cs => lvsL cs
def lvsL : List RTree → List (List WEntry)
  | [] => []
  | t :: ts => lvs t ++ lvsL ts
end

mutual
/-- The positions, in pre-order. -/
def pos : RTree → List w64
  | mk p true _ _ => [p]
  | mk p false _ cs => p :: posL cs
def posL : List RTree → List w64
  | [] => []
  | t :: ts => pos t ++ posL ts
end

mutual
/-- The leaves' depths, from depth `d`. -/
def dps : Nat → RTree → List Nat
  | d, mk _ true _ _ => [d]
  | d, mk _ false _ cs => dpsL (d + 1) cs
def dpsL : Nat → List RTree → List Nat
  | _, [] => []
  | d, t :: ts => dps d t ++ dpsL d ts
end

end RTree

mutual
/-- **`t` is the tree of `L` from its root's position** (bucket `bl`): a leaf has `L`'s entries
there and no children; a branch has `L`'s entries and one child per entry, at its position. -/
def ltIs (L : LTree) (bl : Loc) : RTree → Prop
  | .mk p true ws cs => L bl p = some (true, ws) ∧ cs = []
  | .mk p false ws cs => L bl p = some (false, ws) ∧ ltIsL L bl ws cs
def ltIsL (L : LTree) (bl : Loc) : List WEntry → List RTree → Prop
  | [], [] => True
  | w :: ws, t :: ts => t.pid = w.pgid ∧ ltIs L bl t ∧ ltIsL L bl ws ts
  | _, _ => False
end

/-- **Bucket `bl`'s logical tree is finite** (`Rebalance/RTreeX`'s module doc): a finite tree of
the walk from its root position, of height below the walks' fuel, its leaves at one depth. -/
def rtOK (X : WX) (bl : Loc) : Prop :=
  ∃ t, ltIs (ltree X) bl t ∧ t.pid = X.rootPid bl ∧ t.ht < X.fuel ∧ ∃ D, ∀ x ∈ t.dps 0, x = D

end lt

end bbolt
end EtcdGrove
end Perennial
