/-
`Cursor.first` of a reader (bbolt, internal to U6 of `notes/bbolt-proof-plan.md`): the stack at the
bucket's first entry, with its key and flags (its value too unless a nested bucket's), or nil if
the bucket is empty. Proof: `Proof/go_etcd_io/bbolt/Cursor__first_r.lean`.
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

/-- `c.first()` of a reader's cursor in bucket `b` (value `bv`), from any stack. -/
abbrev Cursor.first_r.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View) (b : Loc) (dq : DFrac)
    (bv : List w8) (ibp pp c : Loc) (stk : GoSlice) (els : List elemRef),
  rBktOK v bv →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ rdTxK (GF := GF) K tx src q T v ∗
      rBktP v tx b dq bv ibp pp ∗ c ↦ Cursor.mk b stk ∗ stk ↦* els ∗
      ownSliceCap elemRef stk (DFrac.own 1) }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"first")) (Val #()))
  {{ (k vl : GoSlice) (fl : w32), RET (PairV (PairV #k #vl) #fl);
      ∃ (stk' : GoSlice) (els' : List elemRef) (vl' : GoSlice), rdTxK K tx src q T v ∗
      rBktP v tx b dq bv ibp pp ∗ c ↦ Cursor.mk b stk' ∗ stk' ↦* els' ∗
      ownSliceCap elemRef stk' (DFrac.own 1) ∗ rCurKV v bv pp els' 0 k vl' fl ∗
      ⌜fl &&& W32 1 = W32 0 → vl = vl'⌝ }}

end spec

end bbolt
end EtcdGrove
end Perennial
