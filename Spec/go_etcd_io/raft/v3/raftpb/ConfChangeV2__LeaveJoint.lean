/-
`raftpb.ConfChangeV2.LeaveJoint` (`raftpb/confchange.go:109`): whether the change leaves
a joint configuration. Lean-first (no Rocq counterpart); see `InvConfChangeMsg.lean`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvConfChangeMsg

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `c.LeaveJoint()` with `c.Changes` holding `ccs`: `true` iff the change is zero but for its
`Context` (`proto.Equal` with the zero `ConfChangeV2`), i.e. the `Auto` transition and no
changes. -/
abbrev raftpb.ConfChangeV2.LeaveJoint.spec : Prop :=
  ∀ (c : raftpb.ConfChangeV2) (ccs : List raftpb.ConfChangeSingle) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ c.Changes' ↦*{dq} ccs }}
    (App (Val (c @!! raftpb.ConfChangeV2.ty @!! go!"LeaveJoint")) (Val #()))
  {{ RET #(decide (c.Transition' = W32 0 ∧ ccs = [])); c.Changes' ↦*{dq} ccs }}

end spec

end EtcdGrove
end Perennial
