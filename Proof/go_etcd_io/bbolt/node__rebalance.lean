/-
`node.rebalance` (bbolt, internal to U8b, `notes/bbolt-proof-plan.md`): its spec and proof. Its
only caller is `Bucket.rebalance` (and itself, `n.parent.rebalance()`), so the spec is U8b's own:
over `rebalance`'s invariant `rblX` (`Rebalance/RblX.lean`) with at most one deficient node, the
one being rebalanced.
-/
module

public import Proof.go_etcd_io.bbolt.Rebalance.RblXSteps
public import Spec.go_etcd_io.bbolt.node__size
public import Spec.go_etcd_io.bbolt.node__numChildren
public import Spec.go_etcd_io.bbolt.node__childIndex
public import Spec.go_etcd_io.bbolt.node__nextSibling
public import Spec.go_etcd_io.bbolt.node__prevSibling
public import Spec.go_etcd_io.bbolt.node__del
public import Spec.go_etcd_io.bbolt.node__removeChild
public import Spec.go_etcd_io.bbolt.node__free
public import Spec.go_etcd_io.bbolt.Bucket__node
public import Spec.go_etcd_io.bbolt.TxStats__IncRebalance
public import Spec.go_etcd_io.bbolt.internal.common.Assert

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- What `n.rebalance()` did to the buckets: the other buckets' records unchanged; in `bl`, the
unbalanced nodes after are some of those before (the same page ids), not `n`. -/
def rblStepX (X X' : WX) (bl n : Loc) : Prop :=
  (∀ bl', bl' ≠ bl → X'.t.bs !! bl' = X.t.bs !! bl') ∧
  ∀ B B', X.t.bs !! bl = some B → X'.t.bs !! bl = some B' → rblStep B B' n

/-- **`n.rebalance()`** of a node `n` of bucket `bl`: from `rebalance`'s invariant with `n` the
deficient node (if any, then marked unbalanced), to the invariant with none; the steps' frees
(`Free` steps for the writer's txid, `rblRel`), `n` no longer unbalanced and no node newly so
(`rblStepX`). -/
def node.rebalance.spec' : Prop :=
  ∀ (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (w : WDb) (bl : Loc) (B : BRec) (n : Loc)
    (rn : NRec) (dfc : Option Loc),
  rblX X w.fl bl dfc → X.t.bs !! bl = some B → B.ns !! n = some rn →
  (dfc = none ∨ (dfc = some n ∧ rn.nv.unbalanced' = true)) →
  {{ wtxW (GF := GF) K tx r m X ∗ wdbW K tx X.v w }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"rebalance")) (Val #()))
  {{ RET #(); ∃ (X' : WX) (fl' : FLPg), wtxW K tx r m X' ∗ wdbW K tx X.v (w.withFl fl') ∗
      ⌜rblX X' fl' bl none ∧ rblRel X w.fl X' fl' X.t.mv.txid' ∧ rblStepX X X' bl n⌝ }}

end spec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem node.rebalance.wp_proof
    (hSize : node.size.spec (GF := GF) (hG := hG))
    (hNum : node.numChildren.spec (GF := GF) (hG := hG))
    (hIdx : node.childIndex.spec (GF := GF) (hG := hG))
    (hNext : node.nextSibling.spec (GF := GF) (hG := hG))
    (hPrev : node.prevSibling.spec (GF := GF) (hG := hG))
    (hDel : node.del.spec (GF := GF) (hG := hG))
    (hRm : node.removeChild.spec (GF := GF) (hG := hG))
    (hFree : node.free.spec (GF := GF) (hG := hG))
    (hNode : Bucket.node.spec (GF := GF) (hG := hG))
    (hInc : TxStats.IncRebalance.spec (GF := GF) (hG := hG))
    (hAssert : internal.common.Assert.spec (GF := GF) (hG := hG)) :
    node.rebalance.spec' (GF := GF) (hG := hG) := by
  sorry

end proof

end bbolt
end EtcdGrove
end Perennial
