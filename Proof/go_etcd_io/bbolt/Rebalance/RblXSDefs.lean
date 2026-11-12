/-
The records' updates `rebalance`'s steps name (U8b, `Rebalance/RblXSteps.lean`): `WX.kill` (a
node removed from its bucket, now dead; `nsLive` is `Model/Wtx`'s).
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
  { X with t := { X.t with bs := X.t.bs.insert bl B', dead := X.t.dead.insert n (bl, rn) },
           live := X.live.delete n }

-- `nsLive`: `Model/Wtx` (batch 20).

end defs

end bbolt
end EtcdGrove
end Perennial
