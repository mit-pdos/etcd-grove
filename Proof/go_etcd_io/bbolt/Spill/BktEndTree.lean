/-
`Bucket.spill`'s root loop's end (U9x5, `notes/bbolt-proof-plan.md`), part 2: **the root bucket's
tree at the loop's end** (statements; proofs in `Spill/BktEnd*`):
- `end_rootTree`: with a root node, its unspilled tree over the current page map and mark (`InitB`
  for the root bucket, its nested values the children's new ones or `BktVal`'s), its base pages
  freeable, its slots `D` exactly the slots `RInv` owns (`Lroot` and the children's), its leaf
  elements' shape and data (`endEls`);
- `end_nilTree`: with no root node (and every cached child without one), its base tree at its root
  page, an `sTree` whose slots are base slots, every base slot its or pending, with `endEls`.
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

/-- **The root bucket's base tree at the end with no root node** (see the module doc). -/
theorem end_nilTree {X0 : WX} {w0 : WDb} {B0 : BRec}
    (hpre : spillPre X0 w0.fl) (hreach : liveReach X0) (hfv : flViewU X0 w0.fl)
    (hB0 : X0.t.bs !! X0.rl = some B0) (hrn : B0.bv.rootNode' = null)
    (hkids : ∀ k c, B0.bm !! k = some c →
      ∃ C0, X0.t.bs !! c = some C0 ∧ C0.bv.rootNode' = null)
    (hvC : X0.v = View.ofC X0.v.base w0.C) (hcok : treeOK w0.C)
    (hhwm : w0.C.hwm ≤ X0.t.mv.pgid'.toNat) :
    ∃ h S, sTree (spP X0) X0.t.mv.pgid'.toNat X0.rootPage none none h S ∧
      (∀ s ∈ treeSlots w0.C, s ∈ pgSlots (spP X0) S ∨ s ∈ pendSlots w0.fl) ∧
      (∀ s ∈ pgSlots (spP X0) S, s ∈ treeSlots w0.C) ∧
      endEls X0 (spP X0) (pgSlots (spP X0) S) (treeEls (spP X0) X0.rootPage) := by
  sorry

/-- **The meta's txid at the end is the start's** (needs `RInv`'s meta field, `mvEq`, U9x4). -/
theorem end_txid {X0 X : WX} {w0 w : WDb} {B0 : BRec} {keys : List GoString}
    {Lroot : List Nat} {st : List FLStep} {Dc : GoString → List Nat} {ks : GoString → KSt}
    (hI : RInv X0 w0 B0 keys Lroot X w st Dc ks) : X.t.mv.txid' = X0.t.mv.txid' := by
  sorry

end tree

end Spill

end bbolt
end EtcdGrove
end Perennial
