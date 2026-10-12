/-
`intervalTree.Insert` (`interval_tree.go`) of any interval, present in the tree or not: the
variant of `intervalTree__Insert.lean` without its premise that the interval is new. Added for
the server's request path (2026-10-12, unit 1: `v3rpc.checkIntervals` inserts the same interval
twice when a transaction deletes the same range twice, a legal request), in the contract's style.
The code inserts a second node for an interval the tree has (`Insert` descends right of an equal
interval, so the new entry goes after the equal ones), which is what the model's `ivtInsert`
does; the tree's entries are then not distinct (`ownIvt`'s documentation says distinct: the
tree's proof, unit 4 of the watchable store, must allow equal intervals, as `Union`'s spec does).
Lean-first (no Rocq counterpart); see `Model.lean`, `Defs.lean`. Pending: the interval tree's
contract, proved in unit 4 (the tree's proof); until then a hypothesis of every result that
reaches it (`?` in `etc/link-lean-first-adt.txt`).
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

/-- `t.Insert(ivl, v)` of any interval: the entry inserted in the tree's order, after the equal
ones. -/
abbrev adt.intervalTree.InsertAny.spec : Prop :=
  ∀ (t : Loc) (L : List adt.Entry) (b e : GoString) (v : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗ adt.ownIvt t L }}
    (App (App (Val (t @!! go.GoType.PointerType intervalTree.ty @!! go!"Insert"))
      (Val #(adt.affIvl b e))) (Val #v))
  {{ RET #(); adt.ownIvt t (adt.ivtInsert ((b, e), v) L) }}

end spec

end EtcdGrove
end Perennial
