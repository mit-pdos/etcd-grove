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

/-- `t.Visit(ivl, ivv)` over the keys `K`, for a query (its values holding its keys at any
fractions, kept), at `dq` of the tree: calls the visitor on (pointers to) the `IntervalValue`s
of entries overlapping the query, in the tree's order, until it stops if it does; the visitor
keeps each pointer's `iv` (recorded in `I`, or in `J` when it stops: `ivVisitorOkK`), told it is
called on those entries in order. `ps` the pointers, `es` their entries: a sublist of the
overlapping entries, and, for a query that is not empty-and-finite (`b = ""` or `b < e`), all
of them when no visitor stopped (`r`), a non-empty prefix else (a degenerate query's descent
prunes on the subtrees' `max`, and `Contains` makes such queries). The pointers are lent: the
tree is given back by the wand. -/
abbrev adt.intervalTree.Visit_gen.spec : Prop :=
  ∀ (K : adt.KeyRep (GF := GF)), K.CompareOk →
  ∀ (t : Loc) (L : List adt.Entry) (vb ve : val) (db de : DFrac) (b e : GoString) (dq : DFrac)
    (ivv : GoFunc) (I J : List (Loc × adt.Entry) → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗ adt.ownIvtK K t L dq ∗
      K.keyAt db vb b ∗ K.keyAt de ve e ∗
      adt.ivVisitorOkK K dq (adt.stab (b, e) L) (b = go!"" ∨ adt.affLt b e) ivv I J ∗ I [] }}
    (App (App (Val (t @!! go.GoType.PointerType intervalTree.ty @!! go!"Visit"))
      (Val #(K.ivl vb ve))) (Val #ivv))
  {{ RET #(); K.keyAt db vb b ∗ K.keyAt de ve e ∗
      ∃ (ps : List Loc) (es : List adt.Entry) (r : Bool),
      ⌜List.Sublist es (adt.stab (b, e) L) ∧ ps.length = es.length ∧
        ((b = go!"" ∨ adt.affLt b e) →
          if r then es = adt.stab (b, e) L else es <+: adt.stab (b, e) L ∧ es ≠ [])⌝ ∗
      (if r then I else J) (ps.zip es) ∗
      (([∗list] x ∈ ps.zip es, K.ivAt x.1 dq x.2) -∗ adt.ownIvtK K t L dq) }}

end spec

end EtcdGrove
end Perennial
