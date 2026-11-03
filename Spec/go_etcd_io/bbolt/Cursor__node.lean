/-
`Cursor.node` (bbolt, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U7; used by U7 (`Put`, `Delete`, `CreateBucket*`, `DeleteBucket`), U9 (`Bucket.spill`'s header puts). Proof:
`Proof/go_etcd_io/bbolt/Cursor__node.lean` (a `sorry` until U7).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx

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

/-- `c.node()` of a cursor whose stack is a logical path (`lPath`) of a searchable bucket `bl`:
the leaf node at the path's end, the path's positions materialized from the root down as need be
(`matGrow`: the logical tree and the data unchanged; a well-formed `X` stays so). The stack is
only read. -/
abbrev Cursor.node.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (bl : Loc) (B : BRec) (c : Loc)
    (stk : GoSlice) (els : List elemRef) (pids : List w64) (dq : DFrac),
  X.t.bs !! bl = some B → bktLocalOK X bl → lPath X bl els pids → B.bv.nodes' ≠ null →
  (∀ pid ∈ pids, resolve B pid = none → matReady X B pid) →
  {{ wtxW (GF := GF) K tx r m X ∗ c ↦{dq} Cursor.mk bl stk ∗ stk ↦*{dq} els }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"node")) (Val #()))
  {{ (l : Loc), RET #l; ∃ X' : WX, wtxW K tx r m X' ∗ c ↦{dq} Cursor.mk bl stk ∗
      stk ↦*{dq} els ∗
      ⌜matGrow X X' bl ∧ (wOK X → wOK X') ∧
        ∃ B' pid, X'.t.bs !! bl = some B' ∧ pids.getLast? = some pid ∧ resolve B' pid = some l⌝ }}

end spec

end bbolt
end EtcdGrove
end Perennial
