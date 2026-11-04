/-
The records' updates `rebalance`'s steps name (U8b, `Rebalance/RblXSteps.lean`): `WX.kill` (a
node removed from its bucket, now dead) and `nsLive`.
-/
module

public import Proof.go_etcd_io.bbolt.Rebalance.RblX

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section defs
variable [GooseExts]

/-- `X` with bucket `bl`'s record `B'` (without the node `n`) and `n` dead (its record `rn`). -/
def WX.kill (X : WX) (bl : Loc) (B' : BRec) (n : Loc) (rn : NRec) : WX :=
  { X with t := { X.t with bs := X.t.bs.insert bl B', dead := X.t.dead.insert n (.node bl rn) },
           live := X.live.delete n }

/-- Every node of every bucket is live (before `Commit`, no node of a bucket is dead). -/
def nsLive (X : WX) : Prop :=
  ∀ bl B l r, X.t.bs !! bl = some B → B.ns !! l = some r → l ∈ X.live

end defs

end bbolt
end EtcdGrove
end Perennial
