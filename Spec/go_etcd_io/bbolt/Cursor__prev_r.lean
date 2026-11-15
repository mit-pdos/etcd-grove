/-
`Cursor.prev` of a reader (bbolt, internal to U6h of `notes/bbolt-proof-plan.md`): from a reader
cursor's stack at `pos` (`rCurPos`), the up-loop to the deepest element above index `0`, its index
one less, and `last` down to the entry before; at the first entry (every index `0`, or the empty
root leaf's `-1`) `first` and nil; unpositioned (the empty stack) nil.
Proof: `Proof/go_etcd_io/bbolt/Cursor__prev_r.lean`.
-/
module

public import Spec.go_etcd_io.bbolt.Cursor__next_r

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

/-- What `prev` leaves from a cursor at `pos`: unpositioned, nil and the empty stack; at the first
entry, nil and the stack at the first entry (`first`'s); at entry `j + 1`, the move to entry `j`
(`rCurKV`'s entry case). -/
def rPrevPost (v : View) (bv : List w8) (pp : Loc) (els : List elemRef) (k vl : GoSlice)
    (fl : w32) : Option Nat → IProp GF
  | none => iprop(⌜k = slice.nil ∧ vl = slice.nil ∧ fl = W32 0 ∧ els = []⌝)
  | some 0 => iprop(⌜k = slice.nil ∧ vl = slice.nil ∧ fl = W32 0 ∧ rCurPos v bv pp els (some 0)⌝)
  | some (j + 1) => iprop(∃ pg idx, ⌜rPosAt v bv pp els j (j + 1) ∧ rLanded v bv pp els ∧
      (rEnts v bv)[j]? = some (pg, idx)⌝ ∗ rKV v pg idx k vl fl)

/-- `c.prev()` of a reader's cursor in bucket `b` (value `bv`, `rBktOK`) whose stack is at `pos`. -/
abbrev Cursor.prev_r.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View) (b : Loc) (dq : DFrac)
    (bv : List w8) (ibp pp c : Loc) (stk : GoSlice) (els : List elemRef) (pos : Option Nat),
  rBktOK v bv → rCurPos v bv pp els pos →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ rdTxK (GF := GF) K tx src q T v ∗
      rBktP v tx b dq bv ibp pp ∗ c ↦ Cursor.mk b stk ∗ stk ↦* els ∗
      ownSliceCap elemRef stk (DFrac.own 1) }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"prev")) (Val #()))
  {{ (k vl : GoSlice) (fl : w32), RET (PairV (PairV #k #vl) #fl);
      ∃ (stk' : GoSlice) (els' : List elemRef), rdTxK K tx src q T v ∗
      rBktP v tx b dq bv ibp pp ∗ c ↦ Cursor.mk b stk' ∗ stk' ↦* els' ∗
      ownSliceCap elemRef stk' (DFrac.own 1) ∗ rPrevPost v bv pp els' k vl fl pos }}

end spec

end bbolt
end EtcdGrove
end Perennial
