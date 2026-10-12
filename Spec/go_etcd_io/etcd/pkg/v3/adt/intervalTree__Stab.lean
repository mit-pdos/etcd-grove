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

/-- `t.Stab(ivl)`: a fresh slice of pointers to the nodes' `IntervalValue`s (read-only for good)
of the entries overlapping the interval, in the tree's order (`nil` for an empty tree). At any fraction of the tree. -/
abbrev adt.intervalTree.Stab.spec : Prop :=
  ∀ (t : Loc) (L : List adt.Entry) (b e : GoString) (q : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗ adt.ownIvt t L q }}
    (App (Val (t @!! go.GoType.PointerType intervalTree.ty @!! go!"Stab"))
      (Val #(adt.affIvl b e)))
  {{ (ivs : GoSlice) (ps : List Loc), RET #ivs; adt.ownIvt t L q ∗ ivs ↦* ps ∗
      ownSliceCap Loc ivs (DFrac.own 1) ∗ ⌜ps.length = (adt.stab (b, e) L).length⌝ ∗
      [∗list] x ∈ ps.zip (adt.stab (b, e) L), ⌜x.1 ≠ null⌝ ∗
        x.1 ↦□ ({ Ivl' := adt.affIvl x.2.1.1 x.2.1.2, Val' := x.2.2 } : IntervalValue) }}

end spec

end EtcdGrove
end Perennial
