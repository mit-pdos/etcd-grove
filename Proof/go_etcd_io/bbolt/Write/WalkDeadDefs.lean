/-
U7n (`notes/bbolt-proof-plan.md`): **a dead bucket's walk**, the definitions. `DeleteBucket` moves
the child to `X.t.deadB` and sets `child.nodes = nil`, `child.rootNode = nil` before
`child.free()`: no node is reached, so the walk reads only the view's pages, along the page tree
(`pltree`), and frees each page's extent (`pExt`). `WX.setDead` replaces a dead bucket's record.
-/
module

public import Proof.go_etcd_io.bbolt.Model.LTree

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section deaddefs
variable [GooseExts]

/-- **The view's page tree**: at each position its page's kind and entries (any bucket). -/
def pltree (v : View) : LTree := fun _ pid =>
  (v.pages !! pid.toNat).map fun pg => (decide (pageFlags pg = leafPageFlag), pageWs pg)

/-- The extent `Free(txid, tx.page(pid))` frees at a page position: its id and size. -/
def pExt (v : View) (pid : w64) : Option (w64 × Nat) :=
  (v.pages !! pid.toNat).map fun pg => (pid, 1 + pageOverflow pg)

/-- `X` with the dead bucket `bl`'s record replaced. -/
def WX.setDead (X : WX) (bl : Loc) (B' : BRec) : WX :=
  { X with t := { X.t with deadB := X.t.deadB.insert bl B' } }

end deaddefs

end bbolt
end EtcdGrove
end Perennial
