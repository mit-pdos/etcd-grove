/-
`(*ConfChangeV2).LeaveJoint` (`raftpb/confchange.go:111`). Port of the old spec to raft v3.7 (the
getters instead of gogoproto's `proto.Equal` with the zero change; stage R1).
-/
module

public import Proof.go_etcd_io.raft.v3.InvPb

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `c.LeaveJoint()` of a `*ConfChangeV2` holding `m`: `true` iff the `Auto` transition and no
changes (the change is zero but for its `Context`). -/
abbrev raftpb.ConfChangeV2.LeaveJoint.spec : Prop :=
  ∀ (c : Loc) (dq : DFrac) (m : ConfChangeV2M),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ ownConfChangeV2 c dq m }}
    (App (Val (c @!! go.GoType.PointerType raftpb.ConfChangeV2.ty @!! go!"LeaveJoint")) (Val #()))
  {{ RET #(decide (m.transition = W32 0 ∧ m.changes = [])); ownConfChangeV2 c dq m }}

end spec

end EtcdGrove
end Perennial
