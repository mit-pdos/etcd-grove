/-
`Bucket.free_dead` (bbolt, internal): `Bucket.free` of a dead bucket (U7n,
`notes/bbolt-proof-plan.md`): `DeleteBucket`'s `child.free()`, after the child moved to
`X.t.deadB` and `child.nodes = nil`. Proved by U7n; used by U7n (`DeleteBucket`). Proof:
`Proof/go_etcd_io/bbolt/Bucket__free_dead.lean`.
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx
public import Proof.go_etcd_io.bbolt.Write.WalkDeadDefs
public import Proof.go_etcd_io.bbolt.Model.RTree

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `b.free()` of a dead bucket `bl` (in `X.t.deadB`, not in `X.t.bs` nor `X.liveB`; its `tx`
field the writer's, its node cache nil), the writer's database side live: nothing for an inline
bucket; else, no node being reached, every extent of its root page's tree `t` in the view
(`pltree`: the walk's pre-order, `t.pos`) freed for the writer's txid (`pExt`), and its header's
root `0`. The premises in the tree case: `page` nil (`forEachPageNode` walks the tree), the view's
pages well-formed and none in the page cache (`tx.page` reads the view), the frees possible and
the records' meta txid the writer's (`Free` takes `tx.meta.Txid()`). -/
abbrev Bucket.free_dead.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (w : WDb) (bl : Loc) (B : BRec)
    (t : RTree),
  X.t.bs !! bl = none → X.t.deadB !! bl = some B → bl ∉ X.liveB → B.bv.tx' = tx →
  B.bv.nodes' = null →
  (B.ib.root' ≠ W64 0 → B.bv.page' = null ∧ viewWF X.v ∧ ltIs (pltree X.v) bl t ∧
    t.pid = B.ib.root' ∧ (∀ pid ∈ t.pos, X.t.pm !! pid = none) ∧
    w.fl.canFreeAll w.wtxid (t.pos.filterMap (pExt X.v)) ∧ X.t.mv.txid' = w.wtxid) →
  {{ wtxW (GF := GF) K tx r m X ∗ wdbW K tx X.v w }}
    (App (Val (bl @!! go.GoType.PointerType Bucket.ty @!! go!"free")) (Val #()))
  {{ RET #(); ∃ (X' : WX) (w' : WDb), wtxW K tx r m X' ∗ wdbW K tx X.v w' ∗
      ⌜(B.ib.root' = W64 0 ∧ X' = X ∧ w' = w) ∨
       (B.ib.root' ≠ W64 0 ∧ X' = X.setDead bl { B with ib := { B.ib with root' := W64 0 } } ∧
         w' = w.withFl (w.fl.freeAll w.wtxid (t.pos.filterMap (pExt X.v))))⌝ }}

end spec

end bbolt
end EtcdGrove
end Perennial
