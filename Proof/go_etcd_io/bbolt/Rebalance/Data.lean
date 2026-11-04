/-
`rebalance` keeps the writer's data (U8, `notes/bbolt-proof-plan.md`): `wtxData_rebalance'`, the
statement `Model/LTree`'s `wtxData_rebalance` needs. `wtxData_rebalance` as stated is false: an
unopened top-level bucket's data is read from the view's pages (`bktDataOf`'s `none` branch,
`bktOfPage X.v.pages v`), and its hypotheses do not fix `X'.v.pages`; `rebalOK` gives `X'.v = X.v`,
so the premise `X'.v.pages = X.v.pages` costs its user nothing (reported: a shared statement).
-/
module

public import Proof.go_etcd_io.bbolt.Model.LTree

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section data
variable [GooseExts]

theorem bktDataOf_eq (X : WX) (n : GoString) (v : List w8) :
    bktDataOf X n v = match bktLoc X n with
      | some c => GMap.ofList (lbktEnts X c)
      | none => bktOfPage X.v.pages v := rfl

/-- **`rebalance` keeps the data**: the root's bucket entries, the opened top-level buckets, each
one's logical entries and the view's pages unchanged. -/
theorem wtxData_rebalance' (X X' : WX)
    (hroot : rootEnts X' = rootEnts X)
    (hbkts : ∀ n, bktLoc X' n = bktLoc X n)
    (hents : ∀ n bl, bktLoc X n = some bl → lbktEnts X' bl = lbktEnts X bl)
    (hv : X'.v.pages = X.v.pages) :
    wtxData X' = wtxData X := by
  unfold wtxData
  rw [hroot]
  congr 1
  apply List.map_congr_left
  intro e _
  congr 1
  rw [bktDataOf_eq, bktDataOf_eq, hbkts, hv]
  cases h : bktLoc X e.1 with
  | none => rfl
  | some c => simp only [hents e.1 c h]

end data

end bbolt
end EtcdGrove
end Perennial
