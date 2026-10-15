/-
`intervalTree.Len` (`interval_tree.go`). Lean-first (no Rocq counterpart); see `Model.lean`, `Defs.lean`.
Pending: the interval tree's contract, proved in unit 4 (the tree's proof); until then a
hypothesis of every result that reaches it (`?` in `etc/link-lean-first-adt.txt`).
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.adt.Holes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.pkg.v3.adt

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.adt.Assumptions]

/-- `t.Visit(ivl, ivv)` for a query that is not empty-and-finite (`b = ""` or `b < e`), at a
fraction `q` of the tree: calls the visitor on (pointers to) the `IntervalValue`s of exactly the
entries overlapping the query, in the tree's order; the visitor keeps each pointer's points-to
(recorded in `I`) and goes on (`ivVisitorOk`), told it is called on those entries in order. The pointers are lent: the tree is given back by
the wand. -/
abbrev adt.intervalTree.Visit.spec : Prop :=
  ∀ (t : Loc) (L : List adt.Entry) (b e : GoString) (q : Qp) (ivv : GoFunc)
    (I : List (Loc × adt.Entry) → IProp GF),
  (b = go!"" ∨ adt.affLt b e) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗ adt.ownIvt t L q ∗
      adt.ivVisitorOk q (adt.stab (b, e) L) ivv I ∗ I [] }}
    (App (App (Val (t @!! go.GoType.PointerType intervalTree.ty @!! go!"Visit"))
      (Val #(adt.affIvl b e))) (Val #ivv))
  {{ (ps : List Loc), RET #(); ⌜ps.length = (adt.stab (b, e) L).length⌝ ∗
      I (ps.zip (adt.stab (b, e) L)) ∗
      (([∗list] x ∈ ps.zip (adt.stab (b, e) L),
        x.1 ↦{DFrac.own q} ({ Ivl' := adt.affIvl x.2.1.1 x.2.1.2, Val' := x.2.2 } : IntervalValue)) -∗
        adt.ownIvt t L q) }}

end spec

end EtcdGrove
end Perennial
