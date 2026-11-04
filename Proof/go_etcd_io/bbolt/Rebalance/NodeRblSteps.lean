/-
`node.rebalance`'s removal step with the parent's inodes as `node.del` gives them (U8b,
`notes/bbolt-proof-plan.md`). `node.del`'s spec gives the parent a new inode list of which it
says nothing (`NRec.withEntsU s ins …`, `ins` existential) but its length (through `objOwn`'s
`[∗list] it;w ∈ ins;ws`), while `rmParent` fixes it to `rp.ins.eraseIdx i`. Nothing in `rblX` or
`rblRel` reads a node's inodes but through their number, so `rblX_rm` holds of any list of the
right length: `rblX_rm_ins` (a `sorry` until `rmParent` takes the list, or `node.del`'s spec
gives it).
-/
module

public import Proof.go_etcd_io.bbolt.Rebalance.RblXSteps

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section steps
variable [GooseExts]

/-- **`rblX_rm` with the parent's inodes `insP`** (any list of the right length). -/
theorem rblX_rm_ins (X : WX) (fl : FLPg) (bl : Loc) (B : BRec) (n : Loc) (r : NRec) (pl : Loc)
    (rp : NRec) (i : Nat) (w : WEntry) (sI sC : GoSlice) (pg : List w8) (insP : List Inode)
    (hI : rblX X fl bl (some n)) (hb : X.t.bs !! bl = some B) (hr : B.ns !! n = some r)
    (hleaf : r.nv.isLeaf' = true) (hemp : r.ws = []) (hpl : r.nv.parent' = pl) (hpn : pl ≠ null)
    (hrp : B.ns !! pl = some rp) (hw : rp.ws[i]? = some w) (hwp : w.pgid = r.nv.pgid')
    (hpg : X.v.pages !! r.nv.pgid'.toNat = some pg) (hins : insP.length + 1 = rp.ins.length) :
    rblX (X.kill bl (rmBkt B n pl r.nv.pgid' { rmParent rp i n sI sC with ins := insP }) n
        { r with nv := { r.nv with pgid' := W64 0 } })
      (fl.freePages X.t.mv.txid' r.nv.pgid' (1 + pageOverflow pg)) bl (some pl) ∧
    rblRel X fl (X.kill bl (rmBkt B n pl r.nv.pgid' { rmParent rp i n sI sC with ins := insP }) n
        { r with nv := { r.nv with pgid' := W64 0 } })
      (fl.freePages X.t.mv.txid' r.nv.pgid' (1 + pageOverflow pg)) X.t.mv.txid' ∧
    r.nv.pgid' ≠ W64 0 ∧ 2 ≤ rp.ws.length := by
  sorry

end steps

end bbolt
end EtcdGrove
end Perennial
