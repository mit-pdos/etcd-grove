/-
`Cursor.last` of a reader (bbolt, internal to U6h of `notes/bbolt-proof-plan.md`): from a stack
whose top is about to descend by last children (`rTlF`: a branch at some index, or a leaf on an
entry), last children down to a leaf: a stack on the entry just before the position `s` the top
names (`rPosAt … (s - 1) s`; a reader's leaves below a branch are not empty); from a leaf at any
index (`rLfTop`: `Last` on an empty root leaf, at index `-1`), the stack unchanged.
Proof: `Proof/go_etcd_io/bbolt/Cursor__last_r.lean`.
-/
module

public import Proof.go_etcd_io.bbolt.Read.PubRPos
public import Proof.go_etcd_io.bbolt.Read.RCtx

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

/-- `c.last()` of a reader's cursor in bucket `b` (value `bv`, `rBktOK`): the stack `pre ++ [e]`,
`pre` a prefix from the root down to position `pid` (fuel `m`, `o` entries before it), `e` at
`pid` about to descend by last children to just before `s`, or a leaf. -/
abbrev Cursor.last_r.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View) (b : Loc) (dq : DFrac)
    (bv : List w8) (ibp pp c : Loc) (stk : GoSlice) (pre : List elemRef) (e : elemRef)
    (m pid o s : Nat),
  rBktOK v bv → rPreF v bv pp (rFuel v bv) (inBucketRoot bv) pre m pid o → 0 < m →
  rTlF v bv pp m pid e s ∨ rLfTop v bv pp pid e →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ rdTxK (GF := GF) K tx src q T v ∗
      rBktP v tx b dq bv ibp pp ∗ c ↦ Cursor.mk b stk ∗ stk ↦* (pre ++ [e]) ∗
      ownSliceCap elemRef stk (DFrac.own 1) }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"last")) (Val #()))
  {{ RET #(); ∃ (stk' : GoSlice) (els : List elemRef), rdTxK K tx src q T v ∗
      rBktP v tx b dq bv ibp pp ∗ c ↦ Cursor.mk b stk' ∗ stk' ↦* els ∗
      ownSliceCap elemRef stk' (DFrac.own 1) ∗
      ⌜(rTlF v bv pp m pid e s → ∃ i, i + 1 = o + s ∧ rPosAt v bv pp els i (o + s) ∧
          rLanded v bv pp els) ∧
        (rLfTop v bv pp pid e → els = pre ++ [e])⌝ }}

end spec

end bbolt
end EtcdGrove
end Perennial
