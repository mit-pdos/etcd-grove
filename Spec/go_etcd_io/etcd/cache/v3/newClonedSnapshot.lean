/-
`newClonedSnapshot` (`cache/*.go`), an internal helper.
Users: `store.Restore`, `store.applyEventsLocked`.
Proof sketch: `BTree.Clone.spec`, the clone frozen (`BTree.ownBTree_persist`).
Changes: restated over the opaque vocabulary of `Internal.lean` (the old internal handles, ghost names and certificate parameters replaced by predicates over W0's model); the spec mirrors the code.
Margin: none known.
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Cache

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `newClonedSnapshot(rev, t)`: a frozen snapshot of the working tree's items at `rev`. -/
def newClonedSnapshot.spec : Prop :=
  ∀ (rev : w64) (t : Loc) (items : List (GoString × Loc)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ kvTree t (DFrac.own 1) items }}
    (App (App (Val (@! go_etcd_io.etcd.cache.v3.newClonedSnapshot)) (Val #rev)) (Val #t))
  {{ (p : Loc), RET #p; kvTree t (DFrac.own 1) items ∗ snapAt p (sint.Z rev).toNat items }}

end spec

end Cache
end EtcdGrove
end Perennial
