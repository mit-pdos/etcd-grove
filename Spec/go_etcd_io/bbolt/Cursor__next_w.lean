/-
`Cursor.next` of a writer's cursor (U6z, `notes/bbolt-proof-plan.md`, "Writer reads at a
fraction"; U6y's F2): from `boltCurDef`'s stack (stale-tolerant, `wStk`) to the next entry
(`wNextTo`), skipping empty leaves; with none, nil, nil, `0`, the stack unchanged on the last entry
or at the end (`wNextPost`). At the end (`wEndAt`) no level moves (`next_we`). Proof:
`Proof/go_etcd_io/bbolt/Cursor__next_w.lean`.
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

/-- `c.next()` of a writer's cursor in the top-level bucket `n` (handle `bl`, root `rt`), from a
stack between moves: the entry `wNextTo` names, or nil, nil, `0` past the last. -/
abbrev Cursor.next_w.specQ : Prop :=
  ∀ (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (q : Qp) (X : WX) (n : GoString) (bl : Loc)
    (rt : Nat) (ipg : List w8) (nl : Loc → Option (Loc × Nat)) (c : Loc) (stk : GoSlice)
    (els : List elemRef) (pids : List Nat),
  wCurCtx X n bl rt → wStk nl X.v (wEs X n) bl rt ipg els pids →
  {{ wtxWQ (GF := GF) K tx r m q X ∗ c ↦ Cursor.mk bl stk ∗ stk ↦* els ∗
      ownSliceCap elemRef stk (DFrac.own 1) ∗ wStkOwn r nl X.v rt ipg els }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"next")) (Val #()))
  {{ (k vl : GoSlice) (fl : w32), RET (PairV (PairV #k #vl) #fl);
      ∃ (stk' : GoSlice) (els' : List elemRef) (nl' : Loc → Option (Loc × Nat)),
      wtxWQ K tx r m q X ∗ c ↦ Cursor.mk bl stk' ∗ stk' ↦* els' ∗
      ownSliceCap elemRef stk' (DFrac.own 1) ∗ wStkOwn r nl' X.v rt ipg els' ∗
      ⌜wNextPost nl' X.v (wEs X n) bl rt ipg els pids (wNextTo X.v (wEs X n) pids els) els'⌝ ∗
      wEntKV X.v (wEs X n) (wNextTo X.v (wEs X n) pids els) k vl fl }}

/-- `c.next()` of a writer's cursor at the end (`wEndAt`: every branch last, the leaf at its count
or `-1`): no level moves; nil, nil, `0`, the stack unchanged. -/
abbrev Cursor.next_we.specQ : Prop :=
  ∀ (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (q : Qp) (X : WX) (n : GoString) (bl : Loc)
    (rt : Nat) (ipg : List w8) (nl : Loc → Option (Loc × Nat)) (c : Loc) (stk : GoSlice)
    (els : List elemRef) (pids : List Nat),
  wCurCtx X n bl rt → sPathR nl X.v bl rt els pids → sLeafOK X.v ipg (wEs X n) pids els →
  wEndAt X.v (wEs X n) pids els →
  {{ wtxWQ (GF := GF) K tx r m q X ∗ c ↦ Cursor.mk bl stk ∗ stk ↦* els ∗
      wStkOwn r nl X.v rt ipg els }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"next")) (Val #()))
  {{ RET (PairV (PairV #slice.nil #slice.nil) #(W32 0)); wtxWQ K tx r m q X ∗
      c ↦ Cursor.mk bl stk ∗ stk ↦* els ∗ wStkOwn r nl X.v rt ipg els }}

end spec

end bbolt
end EtcdGrove
end Perennial
