/-
## `(*raftLog).appliedTo(i, size)` (internal)

**Users**: `raft.appliedTo` (`raft.go:740`: the applied index from `MsgStorageApplyResp`, and the
snapshot's in `appliedSnap`), `newRaft` (`c.Applied`). **Proof sketch**: the `Panicf` excluded by
the premise. **Changes**: from `specs-ref/Spec/go_etcd_io/raft/v3/raftLog__appliedTo.lean`: over `LogState` (was over the
acknowledgement-window predicate `ownRaftLogW`; the window is a state of `raftLog` now).
-/
module

public import SpecPlan.Spec.go_etcd_io.raft.v3.ApiLog

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Raft

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- (internal) Record `i` as applied, releasing `size` of the applying budget. -/
def raftLog.appliedTo.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (i size : w64),
  ls.applied ≤ uint.nat i → uint.nat i ≤ ls.committed →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftLog l ls }}
    (App (App (Val (l @!! go.GoType.PointerType go_etcd_io.raft.v3.raftLog.ty @!! go!"appliedTo")) (Val #i)) (Val #size))
  {{ RET #(); raftLog l (ls.appliedTo (uint.nat i) size) }}

end spec
end Raft
end EtcdGrove
end Perennial
