/-
`Bucket.spill`'s root loop's end (U9x5, `notes/bbolt-proof-plan.md`), part 2: **the root bucket's
tree at the loop's end**: the meta's txid (`end_txid`). With a root node, the root's unspilled
tree is `Spill/BktEndRoot.end_rootTree` (U9x9); with none, `Spill/BktEndNil.end_nilTree'`.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.BktEndPost

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section tree
variable [GooseExts]

/-- **The meta's txid at the end is the start's** (`RInv.mvEq`). -/
theorem end_txid {X0 X : WX} {w0 w : WDb} {B0 : BRec} {keys : List GoString}
    {Lroot : List Nat} {st : List FLStep} {Dc : GoString → List Nat} {ks : GoString → KSt}
    (hI : RInv X0 w0 B0 keys Lroot X w st Dc ks) : X.t.mv.txid' = X0.t.mv.txid' := by
  rw [hI.mvEq]

end tree

end Spill

end bbolt
end EtcdGrove
end Perennial
