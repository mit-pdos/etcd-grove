/-
The internal spec `Bucket.Cursor_i` (below) and its proof (U6, `notes/bbolt-proof-plan.md`), over `TxStats.IncCursorCount`'s spec.
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx
public import Spec.go_etcd_io.bbolt.TxStats__IncCursorCount
public import Proof.go_etcd_io.bbolt.Read.Base

@[expose] public section

/- The internal spec `Bucket.Cursor_i` (session S6 moved it here from `Spec/`: one
spec per function in `Spec/`; this one is a helper of bbolt's own proofs, not exported).
`Bucket.Cursor_i` (bbolt, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U6; used by U6, U7 (`Put`, `Delete`, `CreateBucket*`, `DeleteBucket`), U9 (`Bucket.spill`), U10 (`tx_check`). Proof:
`Proof/go_etcd_io/bbolt/Bucket__Cursor_i.lean` (a `sorry` until U6).
-/

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


noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem Bucket.Cursor_i.wp_proof (hInc : TxStats.IncCursorCount.spec (GF := GF) (hG := hG)) :
    Bucket.Cursor_i.spec (GF := GF) (hG := hG) := by
  intro K tx r m q b dq
  wp_start as ⟨#Hcore, #Hreg, Hst, Hbtx⟩
  wp_auto
  wp_apply (hInc K tx r m q (W64 1)) $$ [Hst] as %n Hst
  · iframe; iframe #
  try wp_auto
  wp_apply wp_slice_make2 (V := elemRef) (W64 0) $$ [] as %sl ⟨Hsl, Hcap⟩
  · ipureintro; decide
  try wp_auto
  iapply HΦ
  iexists sl
  simp only [List.replicate_zero]
  iframe

end proof

end bbolt
end EtcdGrove
end Perennial
