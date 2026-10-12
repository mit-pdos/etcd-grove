/-
`intervalTree.Delete` (`interval_tree.go`). Lean-first (no Rocq counterpart); see `Model.lean`, `Defs.lean`.
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

/-- `t.Delete(ivl)`: the entry with the interval removed, if any (and whether there was one). The whole tree (fraction `1`). -/
abbrev adt.intervalTree.Delete.spec : Prop :=
  ∀ (t : Loc) (L : List adt.Entry) (b e : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗ adt.ownIvt t L 1 }}
    (App (Val (t @!! go.GoType.PointerType intervalTree.ty @!! go!"Delete"))
      (Val #(adt.affIvl b e)))
  {{ RET #(decide ((b, e) ∈ L.map Prod.fst));
      adt.ownIvt t (L.eraseP fun z => decide (z.1 = (b, e))) 1 }}

end spec

end EtcdGrove
end Perennial
