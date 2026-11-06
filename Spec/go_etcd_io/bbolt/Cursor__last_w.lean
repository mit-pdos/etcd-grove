/-
`Cursor.last` of a writer's cursor (U6z, `notes/bbolt-proof-plan.md`, "Writer reads at a
fraction"): from a stack prefix (its top's index any: `prev` calls it after a decrement), down
the last children to a leaf, at its last index (`-1` in an empty leaf): the new levels at their
last index, and (`Last`'s case) the whole stack if the prefix was (U6aa: the pre no longer asks
`sBrLast`/`sTopLast`, false at `prev`'s call). Proof:
`Proof/go_etcd_io/bbolt/Cursor__last_w.lean`.
-/
module

public import Proof.go_etcd_io.bbolt.Read.WCur

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

/-- `c.last()` of a writer's cursor in the top-level bucket `n` (handle `bl`, root `rt`): the stack
extended by last indices to a leaf. -/
abbrev Cursor.last_w.specQ : Prop :=
  ∀ (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (q : Qp) (X : WX) (n : GoString) (bl : Loc)
    (rt : Nat) (ipg : List w8) (nl : Loc → Option (Loc × Nat)) (c : Loc) (stk : GoSlice)
    (els : List elemRef) (pids : List Nat),
  wCurCtx X n bl rt → sPrefix nl X.v bl rt els pids →
  (sPathR nl X.v bl rt els pids → sLeafOK X.v ipg (wEs X n) pids els) →
  {{ wtxWQ (GF := GF) K tx r m q X ∗ c ↦ Cursor.mk bl stk ∗ stk ↦* els ∗
      ownSliceCap elemRef stk (DFrac.own 1) ∗ wStkOwn r nl X.v rt ipg els }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"last")) (Val #()))
  {{ RET #(); ∃ (stk' : GoSlice) (R : List elemRef) (Q : List Nat) (nl' : Loc → Option (Loc × Nat)),
      wtxWQ K tx r m q X ∗ c ↦ Cursor.mk bl stk' ∗ stk' ↦* (els ++ R) ∗
      ownSliceCap elemRef stk' (DFrac.own 1) ∗ wStkOwn r nl' X.v rt ipg (els ++ R) ∗
      ⌜sPathR nl' X.v bl rt (els ++ R) (pids ++ Q) ∧
        sLeafOK X.v ipg (wEs X n) (pids ++ Q) (els ++ R) ∧
        (∀ j pid e, (pids ++ Q)[j]? = some pid → (els ++ R)[j]? = some e → els.length ≤ j →
          j + 1 < (els ++ R).length → e.index'.toNat + 1 = (pidKeys X.v pid).length) ∧
        (R ≠ [] → sTopLast X.v (wEs X n) (pids ++ Q) (els ++ R)) ∧
        (sBrLast X.v pids els → sTopLast X.v (wEs X n) pids els →
          sBrLast X.v (pids ++ Q) (els ++ R) ∧ sTopLast X.v (wEs X n) (pids ++ Q) (els ++ R))⌝ }}

end spec

end bbolt
end EtcdGrove
end Perennial
