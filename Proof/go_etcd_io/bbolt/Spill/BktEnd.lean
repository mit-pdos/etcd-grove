/-
`Bucket.spill`'s root loop (U9q, `notes/bbolt-proof-plan.md`; U9x5): **the loop's end**
(`rinv_end_nil`, `rinv_end`; moved here from `Spill/BktLoopInv`): from `RInv` after the last key,
the spill's success (`spillOK`, `spillBufs`) with no root node, or the root node's spill's pre and,
after it, the spill's success. The pieces are `Spill/BktEnd*`.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.BktLoopInv

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section fin
variable [GooseExts]


/-- **The end, no root node**: nothing was put, the root bucket has no root node, and the records
are the spill's success as they are. (`hsame`, `hput`: RInv fields to be, approved, U9x5;
`hvC`: `wdbW_ofC` at the call.) -/
theorem rinv_end_nil {X0 X : WX} {w0 w : WDb} {B0 B : BRec} {keys : List GoString}
    {Lroot : List Nat} {st : List FLStep} {Dc : GoString → List Nat} {ks : GoString → KSt}
    (hpre : spillPre X0 w0.fl) (hreach : liveReach X0) (hfv : flViewU X0 w0.fl)
    (hB0 : X0.t.bs !! X0.rl = some B0) (hk : ∀ k, k ∈ keys ↔ (B0.bm !! k).isSome)
    (hI : RInv X0 w0 B0 keys Lroot X w st Dc ks) (hks : ksAt keys keys.length ks)
    (hB : X.t.bs !! X0.rl = some B) (hrn : B.bv.rootNode' = null)
    (hvC : X.v = View.ofC X.v.base w.C) (htx : X0.t.mv.txid'.toNat < 2 ^ 63)
    (hsame : (∀ k ∈ keys, ∀ v p, ks k ≠ .val v p) → X = X0 ∧ w = w0 ∧ st = [])
    (hput : (∃ k v, ks k = .val v true) → ∀ B, X.t.bs !! X0.rl = some B → B.bv.rootNode' ≠ null) :
    spillOK X0 X w0.C w0.fl w.fl w0.wtxid ∧ spillBufs X w0.C w.fl := by
  sorry

/-- **The end, with a root node**: the root bucket's root node is the top of an unspilled tree
over the current page map and mark (`InitB`: its nested values `bvalS`, the visited children's new
ones, `BktVal`'s for the others), owning every owned slot (`O = []`); and after its spill and
`b.rootNode = root; SetRootPage` the spill's success. -/
theorem rinv_end {X0 X : WX} {w0 w : WDb} {B0 B : BRec} {keys : List GoString}
    {Lroot : List Nat} {st : List FLStep} {Dc : GoString → List Nat} {ks : GoString → KSt}
    (hpre : spillPre X0 w0.fl) (hreach : liveReach X0) (hfv : flViewU X0 w0.fl)
    (hB0 : X0.t.bs !! X0.rl = some B0) (hk : ∀ k, k ∈ keys ↔ (B0.bm !! k).isSome)
    (hI : RInv X0 w0 B0 keys Lroot X w st Dc ks) (hks : ksAt keys keys.length ks)
    (hB : X.t.bs !! X0.rl = some B) (hrn : B.bv.rootNode' ≠ null)
    (hvC : X.v = View.ofC X.v.base w.C) (htx : X0.t.mv.txid'.toNat < 2 ^ 63) :
    ∃ rn h F D N E, rn.nv.spilled' = false ∧
      spPre X w X0.rl B.bv.rootNode' rn [] none none h F D N E .top ∧
      ∀ (X1 : WX) (w1 : WDb) (st1 : List FLStep) (B1 : BRec) (rt : Loc) (rr : NRec),
        spDone X X1 w w1 X0.rl B.bv.rootNode' rn [] none none h D N E .top st1 →
        X1.t.bs !! X0.rl = some B1 → B1.ns !! rt = some rr → rt ∈ X1.live →
        rr.nv.spilled' = true → rr.nv.parent' = null → nodeRootIn B1 B1.bv.rootNode' rt →
        spillOK X0 (X1.setBkt X0.rl (bkRooted B1 rt rr.nv.pgid')) w0.C w0.fl w1.fl w0.wtxid ∧
          spillBufs (X1.setBkt X0.rl (bkRooted B1 rt rr.nv.pgid')) w0.C w1.fl := by
  sorry

end fin

end Spill

end bbolt
end EtcdGrove
end Perennial
