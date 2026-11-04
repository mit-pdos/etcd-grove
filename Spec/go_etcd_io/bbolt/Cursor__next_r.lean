/-
`Cursor.next` of a reader (bbolt, internal to U6 of `notes/bbolt-proof-plan.md`): from a stack at
an entry of the bucket (`rPosAt`, its target `s`), the stack at entry `s` with its key, value and
flags (`rKV`), or nil past the last. Proof: `Proof/go_etcd_io/bbolt/Cursor__next_r.lean`.
-/
module

public import Proof.go_etcd_io.bbolt.Read.Pos
public import Spec.go_etcd_io.bbolt.Cursor__keyValue_r

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

/-- **A reader's cursor after a move to entry `s`**: its stack at `s` with the entry's key, value
and flags, or past the bucket's entries with nil, nil, `0`. -/
def rCurKV (v : View) (bv : List w8) (pp : Loc) (els : List elemRef) (s : Nat) (k vl : GoSlice)
    (fl : w32) : IProp GF :=
  iprop((∃ pg idx, ⌜rPosAt v bv pp els s (s + 1) ∧ rLanded v bv pp els ∧
        (rEnts v bv)[s]? = some (pg, idx)⌝ ∗
      rKV v pg idx k vl fl) ∨
    ⌜s = (rEnts v bv).length ∧ k = slice.nil ∧ vl = slice.nil ∧ fl = W32 0⌝)

/-- `c.next()` of a reader's cursor in bucket `b` (value `bv`) whose stack is at entry `i`,
`next` going to `s` (from a stack past its leaf's entries, it stays so if past the last entry). -/
abbrev Cursor.next_r.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View) (b : Loc) (dq : DFrac)
    (bv : List w8) (ibp pp c : Loc) (stk : GoSlice) (els : List elemRef) (i s : Nat),
  rBktOK v bv → rPosAt v bv pp els i s →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ rdTxK (GF := GF) K tx src q T v ∗
      rBktP v tx b dq bv ibp pp ∗ c ↦ Cursor.mk b stk ∗ stk ↦* els ∗
      ownSliceCap elemRef stk (DFrac.own 1) }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"next")) (Val #()))
  {{ (k vl : GoSlice) (fl : w32), RET (PairV (PairV #k #vl) #fl);
      ∃ (stk' : GoSlice) (els' : List elemRef), rdTxK K tx src q T v ∗
      rBktP v tx b dq bv ibp pp ∗ c ↦ Cursor.mk b stk' ∗ stk' ↦* els' ∗
      ownSliceCap elemRef stk' (DFrac.own 1) ∗ rCurKV v bv pp els' s k vl fl ∗
      ⌜rOffEnt v bv pp els → rOffEnt v bv pp els' ∨ s < (rEnts v bv).length⌝ }}

end spec

end bbolt
end EtcdGrove
end Perennial
