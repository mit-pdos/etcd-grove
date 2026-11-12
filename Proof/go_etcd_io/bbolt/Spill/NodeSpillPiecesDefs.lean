/-
`node.spill` after its children's loop (U9l, `notes/bbolt-proof-plan.md`; pure): **the state
after the loop** (`spEnd`), what `Spill/NodeSpillPieces`'s `spillTail_wp` takes: for a leaf,
nothing happened (the sort and the loop of an empty `children`); for a branch, the loop's
invariant (`Spill/NodeSpillLoop`'s `spLoop`, relative to the start of `n`'s spill: `n`'s record
`rn` before the sort, the slots `D`, nodes `N` and elements `E` of `n`'s `uTree`) at an index past
the children, and `n`'s children then its children at the start or nodes the loop made (its
children's pieces, in `T`: their kill is framed).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpillLoop

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section defs
variable [GooseExts]

/-- **`n`'s state after its children's loop** (see the module doc): from `(X, w)` (the spill's
start, `n`'s record `rn`, of height `h`, owning `D`, `N`, `E`) to `(X', w')` (`n`'s record `r'`)
by the steps `st`, the fresh nodes `T` touched. -/
def spEnd (X : WX) (w : WDb) (bl n : Loc) (rn : NRec) (O : List Nat) (lo hi : Option (List w8))
    (h : Nat) (D : List Nat) (N : List Loc) (E : List El) (X' : WX) (w' : WDb) (r' : NRec)
    (st : List FLStep) (T : List Loc) : Prop :=
  (rn.nv.isLeaf' = true ∧ X' = X ∧ w' = w ∧ r' = rn ∧ st = [] ∧ T = []) ∨
  (rn.nv.isLeaf' = false ∧ ∃ h' es i, h = h' + 1 ∧
    spLoop X w bl n rn O lo hi h' D N E X' w' r' es i st T ∧ r'.cs.length ≤ i ∧
    ∀ c ∈ r'.cs, c ∈ rn.cs ∨ c ∈ T)

end defs

end Spill

end bbolt
end EtcdGrove
end Perennial
