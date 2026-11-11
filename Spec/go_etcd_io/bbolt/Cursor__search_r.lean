/-
`Cursor.search` of a reader (bbolt, internal to U6 of `notes/bbolt-proof-plan.md`): from position
`pid` of a reader bucket, the stack grows by a root-to-leaf path of pages routing the key
(`rRoute`). Proof: `Proof/go_etcd_io/bbolt/Cursor__search_r.lean`.
-/
module

public import Proof.go_etcd_io.bbolt.Read.Src
public import Spec.go_etcd_io.bbolt.Cursor__nsearch_p

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section model
variable [GooseExts]

/-- Index `i` of the branch page `pg` routes `k`: the last element whose key is at most `k`, or
the first. -/
def branchRoute (pg : List w8) (k : List w8) (i : Nat) : Prop :=
  i < pageCount pg ∧ (i = 0 ∨ ¬ go.GoStringLt k (branchKey pg i)) ∧
    (i + 1 < pageCount pg → go.GoStringLt k (branchKey pg (i + 1)))

/-- **A reader's stack routing `k`** from position `pid` of the bucket whose value is `bv` (inline
page at `pp`): page references (no nodes), each branch's index routing `k`, the leaf's index the
search index of `k`. -/
def rRoute (v : View) (bv : List w8) (pp : Loc) (k : List w8) : Nat → List elemRef → Prop
  | _, [] => False
  | pid, [e] => ∃ pg, rPageAt v bv pp pid = some (e.page', pg) ∧ e.node' = null ∧
      pageFlags pg = leafPageFlag ∧ e.index' = W64 (pageSeekIdx pg k : Int)
  | pid, e :: e' :: es => ∃ pg, rPageAt v bv pp pid = some (e.page', pg) ∧ e.node' = null ∧
      pageFlags pg = branchPageFlag ∧ branchRoute pg k e.index'.toNat ∧
      rRoute v bv pp k (branchPgid pg e.index'.toNat) (e' :: es)

/-- Position `pid` of the bucket whose value is `bv` roots a well-formed (sub)tree: its inline
page, or a tree of the view's pages. -/
def rTree (v : View) (bv : List w8) (pid : Nat) : Prop :=
  (inBucketRoot bv = 0 ∧ pid = 0 ∧ pageFlags (inlinePage bv) = leafPageFlag ∧
    leafWF (inlinePage bv) (inlinePage bv).length) ∨
  (inBucketRoot bv ≠ 0 ∧ ∃ hwm, treeWF v.pages hwm pid)

end model

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `c.search(key, pid)` in a reader's bucket `b` (value `bv`, a well-formed (sub)tree at `pid`):
the stack grows by a path routing `kb` (the key the caller's bytes or the view's). -/
abbrev Cursor.search_r.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View) (b : Loc) (dq : DFrac)
    (bv : List w8) (ibp pp c : Loc) (stk : GoSlice) (els : List elemRef) (pid : w64)
    (key : GoSlice) (kr : KeyR) (kb : List w8),
  16 ≤ bv.length → rTree v bv pid.toNat →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ rdTxK (GF := GF) K tx src q T v ∗
      rBktP v tx b dq bv ibp pp ∗ c ↦ Cursor.mk b stk ∗ stk ↦* els ∗
      ownSliceCap elemRef stk (DFrac.own 1) ∗ keyR v key kr kb }}
    (App (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"search")) (Val #key)) (Val #pid))
  {{ RET #(); ∃ (stk' : GoSlice) (path : List elemRef), rdTxK K tx src q T v ∗
      rBktP v tx b dq bv ibp pp ∗ c ↦ Cursor.mk b stk' ∗ stk' ↦* (els ++ path) ∗
      ownSliceCap elemRef stk' (DFrac.own 1) ∗ keyR v key kr kb ∗
      ⌜rRoute v bv pp kb pid.toNat path⌝ }}

end spec

end bbolt
end EtcdGrove
end Perennial
