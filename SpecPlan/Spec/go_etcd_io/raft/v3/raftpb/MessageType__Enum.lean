/-
`MessageType.Enum()` (`raftpb/raft.pb.go`, generated): a pointer to a fresh copy of the value.

Users: raft's core (every message it builds: `pb.MsgApp.Enum()`), the examples' transports.
Proof sketch: the body allocates a cell and stores the value.
Changes: from `specs-ref/Spec/go_etcd_io/raft/v3/raftpb/MessageType__Enum.lean`: unchanged.
Margin: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.raft.v3.raftpb.Api

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

/-- `x.Enum()` returns a fresh cell holding `x`. -/
def MessageType.Enum.spec : Prop :=
  ∀ (x : w32),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb }}
    (App (Val (x @!! raftpb.MessageType.ty @!! go!"Enum")) (Val #()))
  {{ (p : Loc), RET #p; p ↦ x }}

end spec

end RaftPb
end EtcdGrove
end Perennial
