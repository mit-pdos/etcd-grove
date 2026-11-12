/-
`Cursor.goToFirstElementOnTheStack` of a writer's cursor (U6z, `notes/bbolt-proof-plan.md`,
"Writer reads at a fraction"): from a stack prefix (`sPrefix`; its top possibly a branch not yet
descended from, possibly stale), down the first children to a leaf; the new references are the
writer's current ones (`pageNode`: a materialized node, registered, or a page of the view or the
inline page), so the leaf, if a page, holds its bounds' entries (`sLeafOK`). Proof:
`Proof/go_etcd_io/bbolt/Cursor__goToFirstElementOnTheStack_w.lean`.
-/
module

public import Proof.go_etcd_io.bbolt.Read.WCur

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

/-- `c.goToFirstElementOnTheStack()` of a writer's cursor in the top-level bucket `n` (handle `bl`,
root `rt`): the stack extended by first indices to a leaf. -/
abbrev Cursor.goToFirstElementOnTheStack_w.specQ : Prop :=
  ∀ (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (q : Qp) (X : WX) (n : GoString) (bl : Loc)
    (rt : Nat) (ipg : List w8) (nl : Loc → Option (Loc × Nat)) (c : Loc) (stk : GoSlice)
    (els : List elemRef) (pids : List Nat),
  wCurCtx X n bl rt → sPrefix nl X.v bl rt els pids →
  (sPathR nl X.v bl rt els pids → sLeafOK X.v ipg (wEs X n) pids els) →
  {{ wtxWQ (GF := GF) K tx r m q X ∗ c ↦ Cursor.mk bl stk ∗ stk ↦* els ∗
      ownSliceCap elemRef stk (DFrac.own 1) ∗ wStkOwn r nl X.v rt ipg els }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"goToFirstElementOnTheStack"))
      (Val #()))
  {{ RET #(); ∃ (stk' : GoSlice) (R : List elemRef) (Q : List Nat) (nl' : Loc → Option (Loc × Nat)),
      wtxWQ K tx r m q X ∗ c ↦ Cursor.mk bl stk' ∗ stk' ↦* (els ++ R) ∗
      ownSliceCap elemRef stk' (DFrac.own 1) ∗ wStkOwn r nl' X.v rt ipg (els ++ R) ∗
      ⌜sPathR nl' X.v bl rt (els ++ R) (pids ++ Q) ∧
        sLeafOK X.v ipg (wEs X n) (pids ++ Q) (els ++ R) ∧ sAllFirst R⌝ }}

end spec

end bbolt
end EtcdGrove
end Perennial
