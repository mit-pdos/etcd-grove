/-
`Cursor.keyValue` of a writer's cursor, stale-tolerant (U6z, `notes/bbolt-proof-plan.md`, "Writer
reads at a fraction"; U6y's F2): the stack is `boltCurDef`'s (`sPathR` over the base view, its leaf
page, if a page, holding its bounds' entries: possibly stale after a same-value `Put`, whose page
bytes are still the view's or the cursor's inline page's), on an entry, past its leaf's end, or at
`-1` in an empty leaf (U6aa: with any branch indices, as `prev` leaves it). Proof: `Proof/go_etcd_io/bbolt/Cursor__keyValue_ws.lean`.
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

/-- `c.keyValue()` of a writer's cursor in the top-level bucket `n` (handle `bl`, root `rt`): the
entry at the stack's position if its leaf index is on an entry, else nil, nil, `0`. -/
abbrev Cursor.keyValue_ws.specQ : Prop :=
  ∀ (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (q : Qp) (X : WX) (n : GoString) (bl : Loc)
    (rt : Nat) (ipg : List w8) (nl : Loc → Option (Loc × Nat)) (c : Loc) (stk : GoSlice)
    (els : List elemRef) (pids : List Nat),
  wCurCtx X n bl rt → sPathR nl X.v bl rt els pids → sLeafOK X.v ipg (wEs X n) pids els →
  (leafIdx els ≤ leafCnt X.v (wEs X n) pids els ∨ wEndAt X.v (wEs X n) pids els ∨
    (leafCnt X.v (wEs X n) pids els = 0 ∧ ∃ e, els.getLast? = some e ∧ e.index' = W64 (-1))) →
  {{ wtxWQ (GF := GF) K tx r m q X ∗ c ↦ Cursor.mk bl stk ∗ stk ↦* els ∗
      wStkOwn r nl X.v rt ipg els }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"keyValue")) (Val #()))
  {{ (k vl : GoSlice) (fl : w32), RET (PairV (PairV #k #vl) #fl); wtxWQ K tx r m q X ∗
      c ↦ Cursor.mk bl stk ∗ stk ↦* els ∗
      wEntKV X.v (wEs X n) (if leafIdx els < leafCnt X.v (wEs X n) pids els
        then stackPos X.v (wEs X n) pids els else (wEs X n).length) k vl fl }}

end spec

end bbolt
end EtcdGrove
end Perennial
