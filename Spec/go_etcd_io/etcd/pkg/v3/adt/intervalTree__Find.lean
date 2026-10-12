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

/-- `t.Find(ivl)`: a pointer to the node's `IntervalValue` of the entry with the interval
(read-only for good: a node's `iv` is written at its creation only), or `nil`. At any fraction of the tree. -/
abbrev adt.intervalTree.Find.spec : Prop :=
  ∀ (t : Loc) (L : List adt.Entry) (b e : GoString) (q : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗ adt.ownIvt t L q }}
    (App (Val (t @!! go.GoType.PointerType intervalTree.ty @!! go!"Find"))
      (Val #(adt.affIvl b e)))
  {{ (p : Loc), RET #p; adt.ownIvt t L q ∗
      match L.find? (fun z => decide (z.1 = (b, e))) with
      | some z => ⌜p ≠ null⌝ ∗ p ↦□ ({ Ivl' := adt.affIvl b e, Val' := z.2 } : IntervalValue)
      | none => ⌜p = null⌝ }}

end spec

end EtcdGrove
end Perennial
