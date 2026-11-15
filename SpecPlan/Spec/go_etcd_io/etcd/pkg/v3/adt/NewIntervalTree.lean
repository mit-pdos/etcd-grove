/-
`NewIntervalTree()` (`interval_tree.go`): an empty tree.

**Users.** `watcherGroup` (`newWatcherGroup`, 3f), `checkIntervals` (`v3rpc/key.go`, 2a),
`getMergedPerms` (`auth/range_perm_cache.go`, 3d). Snippets: every `examples/specreq/adt/` one.

**Proof sketch.** Allocates the sentinel (black, zero fields) and the tree (`root` the sentinel,
`count` 0): `ivt`'s realization with the empty red-black tree, at any key kind.

**Changes** from `specs-ref`'s `NewIntervalTree.lean`: at any key kind `c` (the old spec gave the
string-affine `ownIvt`, and the bytes form came from a separate law `ownIvtB_of_empty`).

**Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.pkg.v3.adt.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Adt

open Iris Iris.BI go_etcd_io.etcd.pkg.v3.adt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.adt.Assumptions]

/-- **`NewIntervalTree()`**: a fresh `*intervalTree` (as an `IntervalTree`), empty, owned whole, for
keys of the caller's kind. -/
def NewIntervalTree.spec : Prop :=
  ∀ (c : Cmp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt }}
    (App (Val (@! go_etcd_io.etcd.pkg.v3.adt.NewIntervalTree)) (Val #()))
  {{ (t : Loc), RET #(interface.mkOk (go.GoType.PointerType intervalTree.ty) #t); ivt c t [] (DFrac.own 1) }}

end spec

end Adt
end EtcdGrove
end Perennial
