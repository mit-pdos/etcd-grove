/-
## `(*raftLog).stableSnapTo(i)` (internal)

**Users**: `appliedSnap` (`raft.go:768`), from `MsgStorageAppendResp` with the snapshot the storage
installed. **Proof sketch**: `unstable.stableSnapTo`; with `SnapAckOk`, the storage (holding the
snapshot and `stored`) is now read for the stable part. **Changes**: from
`specs-ref/Spec/go_etcd_io/raft/v3/raftLog__stableSnapTo.lean`: on `raftLog` (was `ownRaftLogW`).
-/
module

public import Spec.go_etcd_io.raft.v3.ApiLog

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

/-- (internal) Drop the pending snapshot if it is at `i` (it is stored). -/
def raftLog.stableSnapTo.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (i : w64),
  ls.SnapAckOk (uint.nat i) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftLog l ls }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.raft.v3.raftLog.ty @!! go!"stableSnapTo")) (Val #i))
  {{ RET #(); raftLog l (ls.stableSnapTo (uint.nat i)) }}

end spec
end Raft
end EtcdGrove
end Perennial
