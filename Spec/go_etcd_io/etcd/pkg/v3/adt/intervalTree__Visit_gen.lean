/-
`intervalTree.Visit` (`interval_tree.go`) over a comparator, for a visitor that may stop (the auth
plan's S2b, 2026-10-23; `Contains`' stops at a gap). Lean-first; see `Model.lean`, `Holes.lean`.
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.adt.Holes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.pkg.v3.adt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.adt.Assumptions]

/-- `t.Visit(ivl, ivv)` over the keys `K`, on the exact tree `T` (`ownIvtT`), for any query (its
values holding its keys at any fractions, kept), at `dq` of the tree: calls the visitor on
(pointers to) the `IntervalValue`s of the entries `T.visitL (b, e)` names (the descent `visit`
makes; for a query that is not empty-and-finite, the overlapping entries in the tree's order:
`visit_stab`), in order, until it stops if it does; the visitor keeps each pointer's `iv`
(recorded in `I`, or in `J` when it stops: `ivVisitorOkK`), told it is called on a prefix of
them. `ps` the pointers, `es` their entries: all of `T.visitL (b, e)` when no visitor stopped
(`r`), a non-empty prefix else. The pointers are lent: the tree is given back by the wand. -/
abbrev adt.intervalTree.Visit_gen.spec : Prop :=
  ∀ (K : adt.KeyRep (GF := GF)), K.CompareOk →
  ∀ (t : Loc) (T : adt.RbT adt.Entry) (vb ve : val) (db de : DFrac) (b e : GoString) (dq : DFrac)
    (ivv : GoFunc) (I J : List (Loc × adt.Entry) → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗ adt.ownIvtT K t T dq ∗
      K.keyAt db vb b ∗ K.keyAt de ve e ∗
      adt.ivVisitorOkK K dq (T.visitL (b, e)) True ivv I J ∗ I [] }}
    (App (App (Val (t @!! go.GoType.PointerType intervalTree.ty @!! go!"Visit"))
      (Val #(K.ivl vb ve))) (Val #ivv))
  {{ RET #(); K.keyAt db vb b ∗ K.keyAt de ve e ∗
      ∃ (ps : List Loc) (es : List adt.Entry) (r : Bool),
      ⌜ps.length = es.length ∧
        if r then es = T.visitL (b, e) else es <+: T.visitL (b, e) ∧ es ≠ []⌝ ∗
      (if r then I else J) (ps.zip es) ∗
      (([∗list] x ∈ ps.zip es, K.ivAt x.1 dq x.2) -∗ adt.ownIvtT K t T dq) }}

end spec

end EtcdGrove
end Perennial
