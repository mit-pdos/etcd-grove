/-
`Bucket.spill`'s root loop's end (U9x5, `notes/bbolt-proof-plan.md`), part 2: **the root bucket's
tree at the loop's end** (statements; proofs in `Spill/BktEnd*`):
- `end_rootTree`: with a root node, its unspilled tree over the current page map and mark (`InitB`
  for the root bucket, its nested values the children's new ones or `BktVal`'s), its base pages
  freeable, its slots `D` exactly the slots `RInv` owns (`Lroot` and the children's), its leaf
  elements' shape and data (`endEls`);
(with no root node, `Spill/BktEndNil.end_nilTree'`).
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

/-- **The root bucket's unspilled tree at the loop's end** (see the module doc). -/
theorem end_rootTree {X0 X : WX} {w0 w : WDb} {B0 B : BRec} {keys : List GoString}
    {Lroot : List Nat} {st : List FLStep} {Dc : GoString → List Nat} {ks : GoString → KSt}
    (hpre : spillPre X0 w0.fl) (hreach : liveReach X0) (hfv : flViewU X0 w0.fl)
    (hB0 : X0.t.bs !! X0.rl = some B0) (hk : ∀ k, k ∈ keys ↔ (B0.bm !! k).isSome)
    (hI : RInv X0 w0 B0 keys Lroot X w st Dc ks) (hks : ksAt keys keys.length ks)
    (hB : X.t.bs !! X0.rl = some B) (hrn : B.bv.rootNode' ≠ null)
    (hvC : X.v = View.ofC X.v.base w.C) :
    ∃ rn h F D N E, X.node X0.rl B.bv.rootNode' = some rn ∧ rn.nv.parent' = null ∧
      rn.nv.spilled' = false ∧
      uTree X X0.rl (spP X) X.t.mv.pgid'.toNat B.bv.rootNode' none none h F D N E ∧
      spFree X w.fl w0.wtxid F ∧ D.Nodup ∧ (∀ s ∈ Lroot ++ keys.flatMap Dc, s ∈ D) ∧
      (∀ s ∈ D, s ∈ Lroot ++ keys.flatMap Dc) ∧ endEls X0 (spP X) D E := by
  sorry

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
