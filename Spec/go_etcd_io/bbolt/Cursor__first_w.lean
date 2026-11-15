/-
`Cursor.first` of a writer's cursor (U6z, `notes/bbolt-proof-plan.md`, "Writer reads at a
fraction"): from any stack, the root reference and the first children down to a leaf, then past
empty leaves (`next`); the cursor at entry `0` (`wCurAt`: on it, or at the end of an empty bucket),
the first entry or nil. Proof: `Proof/go_etcd_io/bbolt/Cursor__first_w.lean`.
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

/-- `c.first()` of a writer's cursor in the top-level bucket `n` (handle `bl`, root `rt`). -/
abbrev Cursor.first_w.specQ : Prop :=
  ∀ (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (q : Qp) (X : WX) (n : GoString) (bl : Loc)
    (rt : Nat) (c : Loc) (stk : GoSlice) (els : List elemRef),
  wCurCtx X n bl rt →
  {{ wtxWQ (GF := GF) K tx r m q X ∗ c ↦ Cursor.mk bl stk ∗ stk ↦* els ∗
      ownSliceCap elemRef stk (DFrac.own 1) }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"first")) (Val #()))
  {{ (k vl : GoSlice) (fl : w32), RET (PairV (PairV #k #vl) #fl);
      ∃ (stk' : GoSlice) (els' : List elemRef) (nl' : Loc → Option (Loc × Nat)) (ipg : List w8),
      wtxWQ K tx r m q X ∗ c ↦ Cursor.mk bl stk' ∗ stk' ↦* els' ∗
      ownSliceCap elemRef stk' (DFrac.own 1) ∗ wStkOwn r nl' X.v rt ipg els' ∗
      ⌜wCurAt nl' X.v (wEs X n) bl rt ipg els' (some 0)⌝ ∗ wEntKV X.v (wEs X n) 0 k vl fl }}

end spec

end bbolt
end EtcdGrove
end Perennial
