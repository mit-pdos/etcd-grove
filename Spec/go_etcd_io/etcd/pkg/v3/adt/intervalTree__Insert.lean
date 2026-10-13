/-
`intervalTree.Insert` (`interval_tree.go`). Lean-first (no Rocq counterpart); see `Model.lean`, `Defs.lean`.
Proved in unit 4b (`Proof/.../adt/intervalTree__Insert.lean`).
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

/-- `t.Insert(ivl, v)`, the tree below `2^63 - 1` entries (the count's bound: `ownIvt` keeps
`count` below `2^63`, which `count++` cannot check): the entry inserted in the tree's order,
after the entries with an equal interval if any (the tree allows them: the server inserts the
same interval twice). The whole tree (fraction `1`). -/
abbrev adt.intervalTree.Insert.spec : Prop :=
  ∀ (t : Loc) (L : List adt.Entry) (b e : GoString) (v : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗ adt.ownIvt t L 1 ∗
      ⌜L.length + 1 < 2 ^ 63⌝ }}
    (App (App (Val (t @!! go.GoType.PointerType intervalTree.ty @!! go!"Insert"))
      (Val #(adt.affIvl b e))) (Val #v))
  {{ RET #(); adt.ownIvt t (adt.ivtInsert ((b, e), v) L) 1 }}

end spec

end EtcdGrove
end Perennial
