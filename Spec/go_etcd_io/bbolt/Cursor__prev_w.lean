/-
`Cursor.prev` of a writer's cursor in `Last`'s loop (U6z, `notes/bbolt-proof-plan.md`, "Writer
reads at a fraction"; U6y's F4): from a stack below the root on an empty leaf every entry after which
is in it (`wLastInv`), back to the previous leaf's last entry (`last`), or, at the first leaf, the
cursor's `first` (which lands on the bucket's end: every leaf empty); `Last`'s loop invariant is
kept. Its result is unused (`Last` reads `keyValue` after the loop). The all-empty case loops
forever (`issues/bbolt-cursor-last-empty-leaves-hang`), which partial correctness allows. Proof:
`Proof/go_etcd_io/bbolt/Cursor__prev_w.lean`.
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

/-- `c.prev()` of a writer's cursor in `Last`'s loop, in the top-level bucket `n` (handle `bl`,
root `rt`). -/
abbrev Cursor.prev_w.specQ : Prop :=
  ∀ (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (q : Qp) (X : WX) (n : GoString) (bl : Loc)
    (rt : Nat) (ipg : List w8) (nl : Loc → Option (Loc × Nat)) (c : Loc) (stk : GoSlice)
    (els : List elemRef) (pids : List Nat),
  wCurCtx X n bl rt → wLastInv nl X.v (wEs X n) bl rt ipg els pids → 1 < els.length →
  leafCnt X.v (wEs X n) pids els = 0 →
  {{ wtxWQ (GF := GF) K tx r m q X ∗ c ↦ Cursor.mk bl stk ∗ stk ↦* els ∗
      ownSliceCap elemRef stk (DFrac.own 1) ∗ wStkOwn r nl X.v rt ipg els }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"prev")) (Val #()))
  {{ (k vl : GoSlice) (fl : w32), RET (PairV (PairV #k #vl) #fl);
      ∃ (stk' : GoSlice) (els' : List elemRef) (pids' : List Nat)
        (nl' : Loc → Option (Loc × Nat)) (ipg' : List w8),
      wtxWQ K tx r m q X ∗ c ↦ Cursor.mk bl stk' ∗ stk' ↦* els' ∗
      ownSliceCap elemRef stk' (DFrac.own 1) ∗ wStkOwn r nl' X.v rt ipg' els' ∗
      ⌜wLastInv nl' X.v (wEs X n) bl rt ipg' els' pids'⌝ }}

end spec

end bbolt
end EtcdGrove
end Perennial
