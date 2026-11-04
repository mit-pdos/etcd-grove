/-
`node.rebalance`'s merge over the writer's records (U8b, `notes/bbolt-proof-plan.md`): two
siblings `ll`, `lr` (the parent `pl`'s entries `k`, `k + 1`, one of them the deficient node)
merged into `ll` (`Rebalance/RblMg`: `mgBkt`, `mgParent`, `mgLeft`, the moved children
reparented), the right node `lr` dead (`WX.kill`) with its page freed; the parent the deficient
node. The records are those after all of the merge's code (the reparenting loop, the append, the
parent's `del` and `removeChild`, the cache's delete, `rightNode.free()`).

The parent's inodes are any of the right length (`node.del`'s spec gives a new inode list, not
its value), and the dead right node's `children` slice and list are any (the loop's
`removeChild`s change them; a dead node keeps only its struct).
-/
module

public import Proof.go_etcd_io.bbolt.Rebalance.RblXSteps
public import Proof.go_etcd_io.bbolt.Rebalance.RblMg

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section steps
variable [GooseExts]

/-- The bucket after the merge (the parent's inodes `insP`). -/
def mgBktX (B : BRec) (pl : Loc) (rp : NRec) (k : Nat) (ll lr : Loc) (rl rr : NRec)
    (sI sC sI' sC' : GoSlice) (insP : List Inode) : BRec :=
  mgBkt B pl ll lr rr.nv.pgid' { mgParent rp (k + 1) lr sI' sC' with ins := insP }
    (mgLeft rl rr (kidsOf B rr.ws) sI sC)

/-- The dead right node (its page id `0`, its children slice `sCr` and list `csr`). -/
def mgDead (rr : NRec) (sCr : GoSlice) (csr : List Loc) : NRec :=
  { rr with nv := { rr.nv with pgid' := W64 0, children' := sCr }, cs := csr }

/-- **Two siblings merged** (see the module doc): the invariant with the parent deficient, the
steps' relation with the right node's page extent freed, the right node read from a page, and
the unbalanced nodes after (`rblPre`'s form). -/
theorem rblX_mg (X : WX) (fl : FLPg) (bl : Loc) (B : BRec) (n : Loc) (pl : Loc) (rp : NRec)
    (k : Nat) (wl wr : WEntry) (ll lr : Loc) (rl rr : NRec) (sI sC sI' sC' sCr : GoSlice)
    (insP : List Inode) (csr : List Loc) (pg : List w8)
    (hI : rblX X fl bl (some n)) (hb : X.t.bs !! bl = some B) (hn : n = ll ∨ n = lr)
    (hpn : pl ≠ null) (hrp : B.ns !! pl = some rp) (hbr : rp.nv.isLeaf' = false)
    (hwl : rp.ws[k]? = some wl) (hwr : rp.ws[k + 1]? = some wr)
    (hll : B.nm !! wl.pgid = some ll) (hlr : B.nm !! wr.pgid = some lr)
    (hrl : B.ns !! ll = some rl) (hrr : B.ns !! lr = some rr) (hne : 0 < (rl.ws ++ rr.ws).length)
    (hins : insP.length + 1 = rp.ins.length)
    (hpg : X.v.pages !! rr.nv.pgid'.toNat = some pg) :
    rblX (X.kill bl (mgBktX B pl rp k ll lr rl rr sI sC sI' sC' insP) lr (mgDead rr sCr csr))
      (fl.freePages X.t.mv.txid' rr.nv.pgid' (1 + pageOverflow pg)) bl (some pl) ∧
    rblRel X fl (X.kill bl (mgBktX B pl rp k ll lr rl rr sI sC sI' sC' insP) lr (mgDead rr sCr csr))
      (fl.freePages X.t.mv.txid' rr.nv.pgid' (1 + pageOverflow pg)) X.t.mv.txid' ∧
    rr.nv.pgid' ≠ W64 0 ∧
    (∀ y ry', (mgBktX B pl rp k ll lr rl rr sI sC sI' sC' insP).ns !! y = some ry' →
      ry'.nv.unbalanced' = true →
      y = pl ∨ (y ≠ lr ∧ ∃ ry, B.ns !! y = some ry ∧ ry.nv.unbalanced' = true ∧
        ry'.nv.pgid' = ry.nv.pgid')) := by
  sorry

end steps

end bbolt
end EtcdGrove
end Perennial
