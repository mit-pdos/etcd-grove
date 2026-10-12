/-
`intervalTree.Len` (`interval_tree.go`). Lean-first (no Rocq counterpart); see `Model.lean`, `Defs.lean`.
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

/-- `t.find(ivl)` (internal, `Find`'s and `Delete`'s), over the tree struct's `root` and
`sentinel` fields and the nodes from the root, at a fraction `q`: the node `n` that `find`'s
descent stops at (as its subtree, given back by a wand), `findE`: a node whose entry has the
interval (the topmost on the path: with equal intervals, not necessarily the first in order),
or the sentinel. -/
abbrev adt.intervalTree.find.spec : Prop :=
  ∀ (t : Loc) (tv : intervalTree) (q : Qp) (T : adt.RbT adt.Entry) (b e : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗
      t.[intervalTree, go!"root"] ↦{DFrac.own q} tv.root' ∗
      t.[intervalTree, go!"sentinel"] ↦{DFrac.own q} tv.sentinel' ∗
      adt.ownNode tv.sentinel' q tv.sentinel' tv.root' T }}
    (App (Val (t @!! go.GoType.PointerType intervalTree.ty @!! go!"find"))
      (Val #(adt.affIvl b e)))
  {{ (n : Loc), RET #n;
      t.[intervalTree, go!"root"] ↦{DFrac.own q} tv.root' ∗
      t.[intervalTree, go!"sentinel"] ↦{DFrac.own q} tv.sentinel' ∗
      ∃ (p : Loc) (Tz : adt.RbT adt.Entry), adt.ownNode tv.sentinel' q p n Tz ∗
        (adt.ownNode tv.sentinel' q p n Tz -∗ adt.ownNode tv.sentinel' q tv.sentinel' tv.root' T) ∗
        ⌜match T.findE (b, e) with
          | none => Tz = .leaf
          | some z => ∃ c l r, Tz = .node c l z r⌝ }}

end spec

end EtcdGrove
end Perennial
