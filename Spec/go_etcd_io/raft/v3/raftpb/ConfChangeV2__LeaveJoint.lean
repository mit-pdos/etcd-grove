/-
`(*ConfChangeV2).LeaveJoint` (`raftpb/confchange.go:114`).

Users: raft's `applyConfChange` (`raft.go:1947`), `stepLeader`'s `wantsLeaveJoint` (`raft.go:1346`
reads `len(cc.AsV2().Changes) == 0` directly). Snippet: `examples/specreq/raftpb/confchange.go`
(`ReqEnterLeave`).

Proof sketch: `GetTransition()`, `GetChanges()` (lent and given back), compare.
Changes: from `specs-ref/.../raftpb/ConfChangeV2__LeaveJoint.lean`: over the model.
Margin: none.
-/
module

public import Spec.go_etcd_io.raft.v3.raftpb.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace RaftPb

open Iris Iris.BI
open go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.raftpb.Assumptions]

/-- `p.LeaveJoint()`: transition `Auto` and no change. -/
def ConfChangeV2.LeaveJoint.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (c : ConfChangeV2),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ confChangeV2Pts p dq c }}
    (App (Val (p @!! go.GoType.PointerType raftpb.ConfChangeV2.ty @!! go!"LeaveJoint")) (Val #()))
  {{ RET #c.leaveJoint; confChangeV2Pts p dq c }}

end spec

end RaftPb
end EtcdGrove
end Perennial
