/-
`Cursor.seek` of a reader (bbolt, internal to U6 of `notes/bbolt-proof-plan.md`): the stack becomes
a route from the bucket's root to the leaf where the key lands (`rRoute`), and the result is that
leaf's entry at the key's search index (`rKV`). Proof: `Proof/go_etcd_io/bbolt/Cursor__seek_r.lean`.
-/
module

public import Spec.go_etcd_io.bbolt.Cursor__search_r
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

/-- `c.seek(key)` of a reader's cursor in bucket `b` (value `bv`, a well-formed tree): the stack a
route to the leaf `pg` (at position `pid`) where `kb` lands, the result its entry at `kb`'s search
index. -/
abbrev Cursor.seek_r.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View) (b : Loc) (dq : DFrac)
    (bv : List w8) (ibp pp c : Loc) (stk : GoSlice) (els : List elemRef)
    (key : GoSlice) (kr : KeyR) (kb : List w8),
  16 ≤ bv.length → rTree v bv (inBucketRoot bv) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ rdTxK (GF := GF) K tx src q T v ∗
      rBktP v tx b dq bv ibp pp ∗ c ↦ Cursor.mk b stk ∗ stk ↦* els ∗
      ownSliceCap elemRef stk (DFrac.own 1) ∗ keyR v key kr kb }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"seek")) (Val #key))
  {{ (k vl : GoSlice) (fl : w32), RET (PairV (PairV #k #vl) #fl);
      ∃ (stk' : GoSlice) (els' : List elemRef) (e : elemRef) (pid : Nat) (pg : List w8),
      rdTxK K tx src q T v ∗ rBktP v tx b dq bv ibp pp ∗ c ↦ Cursor.mk b stk' ∗
      stk' ↦* (els' ++ [e]) ∗ ownSliceCap elemRef stk' (DFrac.own 1) ∗ keyR v key kr kb ∗
      ⌜rRoute v bv pp kb (inBucketRoot bv) (els' ++ [e]) ∧ rPageAt v bv pp pid = some (e.page', pg) ∧
        pageFlags pg = leafPageFlag ∧ e.index' = W64 (pageSeekIdx pg kb : Int)⌝ ∗
      rKV v pg (pageSeekIdx pg kb) k vl fl }}

end spec

end bbolt
end EtcdGrove
end Perennial
