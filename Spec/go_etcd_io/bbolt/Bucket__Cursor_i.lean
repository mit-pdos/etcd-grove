/-
`Bucket.Cursor_i` (bbolt, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U6; used by U6, U7 (`Put`, `Delete`, `CreateBucket*`, `DeleteBucket`), U9 (`Bucket.spill`), U10 (`tx_check`). Proof:
`Proof/go_etcd_io/bbolt/Bucket__Cursor_i.lean` (a `sorry` until U6).
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

/-- `b.Cursor()` (internal, any transaction): a new cursor of `b` with an empty stack; the
`CursorCount` statistic grows (the statistics' token). -/
abbrev Bucket.Cursor_i.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (q : Qp) (b : Loc) (dq : DFrac),
  {{ K.core (GF := GF) ∗ reg tx K.B r ∗ statsTok r m q ∗ b.[Bucket, go!"tx"] ↦{dq} tx }}
    (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"Cursor")) (Val #()))
  {{ (c : Loc), RET #c; ∃ stk : GoSlice, c ↦ Cursor.mk b stk ∗ stk ↦* ([] : List elemRef) ∗
      ownSliceCap elemRef stk (DFrac.own 1) ∗ statsTok r m q ∗ b.[Bucket, go!"tx"] ↦{dq} tx }}

end spec

end bbolt
end EtcdGrove
end Perennial
