/-
`Cursor.next` of a reader at the end of an empty stack or of an empty bucket (bbolt, internal to
U6i of `notes/bbolt-proof-plan.md`): an unpositioned cursor (`Bucket.Cursor`'s empty stack) or
the empty root leaf at any index (`Last` leaves it at `-1`, which `Cursor.next_r`'s premise
`rPosAt` excludes): the up-loop finds nothing, nil, nil, `0`, the stack unchanged. Proof:
`Proof/go_etcd_io/bbolt/Cursor__next_r0.lean`.
-/
module

public import Spec.go_etcd_io.bbolt.Cursor__next_r

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

/-- `c.next()` of a reader's cursor in bucket `b` (value `bv`, `rBktOK`) whose stack is empty or
the empty bucket's root leaf. -/
abbrev Cursor.next_r0.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View) (b : Loc) (dq : DFrac)
    (bv : List w8) (ibp pp c : Loc) (stk : GoSlice) (els : List elemRef),
  rBktOK v bv → els = [] ∨ rEmptyAt v bv pp els →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ rdTxK (GF := GF) K tx src q T v ∗
      rBktP v tx b dq bv ibp pp ∗ c ↦ Cursor.mk b stk ∗ stk ↦* els ∗
      ownSliceCap elemRef stk (DFrac.own 1) }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"next")) (Val #()))
  {{ RET (PairV (PairV #slice.nil #slice.nil) #(W32 0)); rdTxK K tx src q T v ∗
      rBktP v tx b dq bv ibp pp ∗ c ↦ Cursor.mk b stk ∗ stk ↦* els ∗
      ownSliceCap elemRef stk (DFrac.own 1) }}

end spec

end bbolt
end EtcdGrove
end Perennial
