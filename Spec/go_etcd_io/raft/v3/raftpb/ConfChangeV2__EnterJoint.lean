/-
`raftpb.ConfChangeV2.EnterJoint` (`raftpb/confchange.go:82`): whether the change uses
joint consensus, and whether it leaves the joint state automatically. Lean-first (no Rocq counterpart); see `InvConfChangeMsg.lean`.
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

/-- `c.EnterJoint()` with `c.Changes` holding the list `ccs` (the list `InvConfchange.lean`'s
`enterJointM` and `simpleM` take): `enterJointOf c.Transition ccs.length`, the pair
`(autoLeave, ok)`, or a panic (`panic(fmt.Sprintf("unknown transition: %+v", c))`) when joint
consensus is asked for with a transition other than `Auto`, `JointImplicit`, `JointExplicit`:
the issue `raft-unknown-transition-panic`. -/
abbrev raftpb.ConfChangeV2.EnterJoint.spec : Prop :=
  ∀ (c : raftpb.ConfChangeV2) (ccs : List raftpb.ConfChangeSingle) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ c.Changes' ↦*{dq} ccs }}
    (App (Val (c @!! raftpb.ConfChangeV2.ty @!! go!"EnterJoint")) (Val #()))
  {{ (r : val), RET r; c.Changes' ↦*{dq} ccs ∗
      match enterJointOf c.Transition' ccs.length with
      | some (autoLeave, ok) => ⌜r = PairV #autoLeave #ok⌝
      | none => ⌜∃ p, r = PanicV p⌝ }}

end spec

end EtcdGrove
end Perennial
