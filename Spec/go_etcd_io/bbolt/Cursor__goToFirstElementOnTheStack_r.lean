/-
`Cursor.goToFirstElementOnTheStack` of a reader (bbolt, internal to U6 of
`notes/bbolt-proof-plan.md`): from a stack whose top is about to descend (`rHdF`: a branch at
some index, or a leaf), first children down to a leaf: a stack at the entry the top's index
names (`rPosAt`). Proof: `Proof/go_etcd_io/bbolt/Cursor__goToFirstElementOnTheStack_r.lean`.
-/
module

public import Proof.go_etcd_io.bbolt.Read.Pos
public import Proof.go_etcd_io.bbolt.Read.RCtx

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

/-- `c.goToFirstElementOnTheStack()` of a reader's cursor in bucket `b` (value `bv`): the stack
`pre ++ [e]`, `pre` a prefix from the root down to position `pid` (fuel `m`, `o` entries before
it), `e` at `pid` landing on entry `t` below it; it ends at entry `o + t` of the bucket, landed
on a leaf. -/
abbrev Cursor.goToFirstElementOnTheStack_r.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View) (b : Loc) (dq : DFrac)
    (bv : List w8) (ibp pp c : Loc) (stk : GoSlice) (pre : List elemRef) (e : elemRef)
    (m pid o t : Nat) (pht : Nat → Nat),
  16 ≤ bv.length → pageHts v.pages pht → rTree v bv pid → (inBucketRoot bv = 0 ∨ pht pid < m) →
  rPreF v bv pp (rFuel v bv) (inBucketRoot bv) pre m pid o → 0 < m → rHdF v bv pp m pid e t →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ rdTxK (GF := GF) K tx src q T v ∗
      rBktP v tx b dq bv ibp pp ∗ c ↦ Cursor.mk b stk ∗ stk ↦* (pre ++ [e]) ∗
      ownSliceCap elemRef stk (DFrac.own 1) }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"goToFirstElementOnTheStack")) (Val #()))
  {{ RET #(); ∃ (stk' : GoSlice) (els : List elemRef) (s : Nat), rdTxK K tx src q T v ∗
      rBktP v tx b dq bv ibp pp ∗ c ↦ Cursor.mk b stk' ∗ stk' ↦* els ∗
      ownSliceCap elemRef stk' (DFrac.own 1) ∗ ⌜rPosAt v bv pp els (o + t) s ∧ rLanded v bv pp els⌝ }}

end spec

end bbolt
end EtcdGrove
end Perennial
