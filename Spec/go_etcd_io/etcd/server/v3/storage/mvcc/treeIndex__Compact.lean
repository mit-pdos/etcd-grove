/-
`(*treeIndex).Compact(rev)` (`index.go:205`): over a clone of the tree (1g's `Clone`), each key index
compacted under the lock and removed once empty (1g's `Delete`; its `lg.Panic` unreachable: the key
is in the tree, under the lock); the floor raised to `rev` by the caller's update (at the clone:
every reader at a revision `≥ rev` is answered as before, `idxAt`); returns a fresh map of the
revisions kept (`idxCompactAvail`). Internal (`scheduleCompaction`). **Changes**: over `idxAt`'s floor.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.InternalIdx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

local notation "pkgInit" => isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc

/-- `ti.Compact(rev)`. -/
def treeIndex.Compact.spec : Prop :=
  ∀ (ti : Loc) (γi : IdxName) (rev : w64) (Q : IndexM → IProp GF),
  {{ pkgInit ∗ isTreeIndex (interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti) γi ∗
      AU <{ ∃∃ (M : IndexM) (c : Int), idxAt γi M c ∗ ⌜c ≤ sint.Z rev⌝ }> @ ⊤ \ ↑idxN, ∅
        <{ idxAt γi M (sint.Z rev), COMM Q M }> }}
    (App (Val (ti @!! go.GoType.PointerType treeIndex.ty @!! go!"Compact")) (Val #rev))
  {{ (m : Loc), RET #m; ∃ M : IndexM, Q M ∗ availAt m (idxCompactAvail M rev) }}

end spec
end Mvcc
end EtcdGrove
end Perennial
