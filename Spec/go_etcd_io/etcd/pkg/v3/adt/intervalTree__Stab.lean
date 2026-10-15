/-
`intervalTree.Stab` (`interval_tree.go`). Lean-first (no Rocq counterpart); see `Model.lean`, `Defs.lean`.
Pending: the interval tree's contract, proved in unit 4 (the tree's proof); until then a
hypothesis of every result that reaches it (`?` in `etc/link-lean-first-adt.txt`).
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.adt.Defs

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

/-- `t.Stab(ivl)` of a query that is not empty-and-finite (`b = ""`, never overlapping, or
`b < e`: on a query with `e ≤ b ≠ ""`, `visit`'s pruning on the subtrees' `max` misses
entries): a fresh slice of pointers to the nodes' `IntervalValue`s of the entries overlapping
the interval, in the tree's order (`nil` for an empty tree). At any fraction `q` of the tree;
the pointers are lent at that fraction, the tree given back by the wand (a node's `iv` is not
read-only for good: `Delete` copies the successor's into the deleted node). -/
abbrev adt.intervalTree.Stab.spec : Prop :=
  ∀ (t : Loc) (L : List adt.Entry) (b e : GoString) (q : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗ adt.ownIvt t L q ∗
      ⌜b = go!"" ∨ adt.affLt b e⌝ }}
    (App (Val (t @!! go.GoType.PointerType intervalTree.ty @!! go!"Stab"))
      (Val #(adt.affIvl b e)))
  {{ (ivs : GoSlice) (ps : List Loc), RET #ivs; ivs ↦* ps ∗
      ownSliceCap Loc ivs (DFrac.own 1) ∗ ⌜ps.length = (adt.stab (b, e) L).length⌝ ∗
      ([∗list] x ∈ ps.zip (adt.stab (b, e) L), ⌜x.1 ≠ null⌝ ∗
        x.1 ↦{DFrac.own q} ({ Ivl' := adt.affIvl x.2.1.1 x.2.1.2, Val' := x.2.2 } : IntervalValue)) ∗
      (([∗list] x ∈ ps.zip (adt.stab (b, e) L),
        x.1 ↦{DFrac.own q} ({ Ivl' := adt.affIvl x.2.1.1 x.2.1.2, Val' := x.2.2 } : IntervalValue)) -∗
        adt.ownIvt t L q) }}

end spec

end EtcdGrove
end Perennial
