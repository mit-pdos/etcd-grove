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

/-- A dead bucket (not in `bs`) is its bucket object. -/
theorem bobjs_dead (T : WTx) (bl : Loc) (B : BRec) (hbs : T.bs !! bl = none)
    (hd : T.deadB !! bl = some B) : T.bobjs !! bl = some B := by
  unfold WTx.bobjs
  rw [GMap.lookup_union, hbs, hd]; rfl

/-- A dead bucket's objects after its record is replaced. -/
theorem bobjs_setDead (X : WX) (bl : Loc) (B' : BRec) (hbs : X.t.bs !! bl = none) :
    (X.setDead bl B').t.bobjs = X.t.bobjs.insert bl B' := by
  apply GMap.map_eq
  intro k
  by_cases hk : k = bl
  · subst hk
    simp only [WX.setDead, WTx.bobjs, GMap.lookup_union, GMap.lookup_insert, hbs]; rfl
  · have hk' : bl ≠ k := Ne.symm hk
    simp only [WX.setDead, WTx.bobjs, GMap.lookup_union, GMap.lookup_insert_ne _ _ hk']

theorem setDead_lookup (X : WX) (bl : Loc) (B' : BRec) :
    (X.setDead bl B').t.deadB !! bl = some B' := by
  unfold WX.setDead; simp only [GMap.lookup_insert]

end deaddefs

end bbolt
end EtcdGrove
end Perennial
