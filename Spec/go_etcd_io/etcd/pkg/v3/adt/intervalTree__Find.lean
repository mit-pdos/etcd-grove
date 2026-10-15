/-
`intervalTree.Find` (`interval_tree.go`). Lean-first (no Rocq counterpart); see `Model.lean`, `Defs.lean`.
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

/-- `t.Find(ivl)`: a pointer to the `IntervalValue` of a node whose entry has the interval, or
`nil` when there is none. With equal intervals (the tree allows them), the entry is one of
them, not necessarily the first in order: `find` stops at the topmost on its path. At any
fraction `q` of the tree; the pointer is lent at that fraction, the tree given back by the wand
(a node's `iv` is not read-only for good: `Delete` copies the successor's `IntervalValue` into
the deleted node, `z.iv = y.iv`). -/
abbrev adt.intervalTree.Find.spec : Prop :=
  ∀ (t : Loc) (L : List adt.Entry) (b e : GoString) (q : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗ adt.ownIvt t L q }}
    (App (Val (t @!! go.GoType.PointerType intervalTree.ty @!! go!"Find"))
      (Val #(adt.affIvl b e)))
  {{ (p : Loc), RET #p;
      (∃ z : adt.Entry, ⌜z ∈ L ∧ z.1 = (b, e)⌝ ∗ ⌜p ≠ null⌝ ∗
        p ↦{DFrac.own q} ({ Ivl' := adt.affIvl b e, Val' := z.2 } : IntervalValue) ∗
        (p ↦{DFrac.own q} ({ Ivl' := adt.affIvl b e, Val' := z.2 } : IntervalValue) -∗
          adt.ownIvt t L q)) ∨
      (⌜p = null ∧ (b, e) ∉ L.map Prod.fst⌝ ∗ adt.ownIvt t L q) }}

end spec

end EtcdGrove
end Perennial
