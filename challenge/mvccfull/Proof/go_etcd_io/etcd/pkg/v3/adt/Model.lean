/-
The pure model of etcd's interval tree (`pkg/v3/adt`), specialized to string-affine intervals
(its only client, the watcher group, uses `StringAffineComparable` intervals). Lean-first (no
Rocq counterpart); see `notes/decisions.md`, "The watchable store: the plan, the interval
tree's contract".

An interval is a pair `(begin, end)` of Go strings, `[begin, end)`, under the affine order
`affCmp` (`StringAffineComparable.Compare`: `""` is +∞). The tree holds a list of entries
(an interval and the `any` value stored with it), sorted by the tree's order `ivlLt` (by begin,
then end), equal intervals allowed, in insertion order among equals (`Insert` descends left when
the new interval is below the node's, right otherwise, so after the equal ones; rotations and the
successor-based delete keep the in-order sequence).
`ivlCmp` is `Interval.Compare` (overlap is `0`), `stab` the entries a query overlaps.
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.adt.Base
public import Perennial.Golang.Defn.String

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace adt

/-! ## Go's string order -/

/-! ## Intervals -/

/-- A string-affine interval `[begin, end)`: `""` is +∞ (as `End`, unbounded;
`StringAffineComparable.Compare` puts it above every string). -/
abbrev IvlS := GoString × GoString

/-- `StringAffineComparable.Compare` -/
def affCmp (a b : GoString) : Int :=
  if a = go!"" then (if b = go!"" then 0 else 1) else if b = go!"" then -1
  else if go.GoStringLt a b then -1 else if go.GoStringLt b a then 1 else 0

/-- The tree's order on intervals: by begin, then end (`Insert` descends left on it, right
otherwise). -/
def ivlLt (x y : IvlS) : Prop :=
  affCmp x.1 y.1 < 0 ∨ (affCmp x.1 y.1 = 0 ∧ affCmp x.2 y.2 < 0)

section entries
variable [GooseExts]

/-- An entry of the tree: an interval and the value stored with it. -/
abbrev Entry := IvlS × GoInterface

end entries

/-! ## The affine order -/

/-! ## `Insert` -/

section entries
variable [GooseExts]

end entries

end adt
end EtcdGrove
end Perennial
