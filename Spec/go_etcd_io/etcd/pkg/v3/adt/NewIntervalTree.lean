/-
`NewIntervalTree` (`interval_tree.go`). Lean-first (no Rocq counterpart); see `Model.lean`, `Defs.lean`.
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

/-- `NewIntervalTree()`: an empty tree, as an `IntervalTree` (the `*intervalTree`). -/
abbrev adt.NewIntervalTree.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt }}
    (App (Val (@! go_etcd_io.etcd.pkg.v3.adt.NewIntervalTree)) (Val #()))
  {{ (t : Loc), RET #(interface.mkOk (go.GoType.PointerType intervalTree.ty) #t);
      adt.ownIvt t [] }}

end spec

end EtcdGrove
end Perennial
