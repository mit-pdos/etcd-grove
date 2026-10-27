/-
`(*ConfChangeV2).EnterJoint` (`raftpb/confchange.go:84`). Port of the old spec to raft v3.7
(pointer receiver, `GetTransition()`; stage R1).
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

/-- `c.EnterJoint()` of a `*ConfChangeV2` holding `m`: `enterJointOf m.transition
m.changes.length`, the pair `(autoLeave, ok)`. Its panic (`panic(fmt.Sprintf("unknown transition:
%+v", c))`), when joint consensus is asked for with a transition other than `Auto`,
`JointImplicit`, `JointExplicit` (the issue `raft-unknown-transition-panic`), is excluded by the
premise, as in the old spec: the panic formats `c`, which Perennial's `fmt.wp_Sprintf` does not
admit, and the one caller (`raft.applyConfChange`) excludes it anyway. -/
abbrev raftpb.ConfChangeV2.EnterJoint.spec : Prop :=
  ∀ (c : Loc) (dq : DFrac) (m : CCV2M),
  enterJointOf m.transition m.changes.length ≠ none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ ownCCV2 c dq m }}
    (App (Val (c @!! go.GoType.PointerType raftpb.ConfChangeV2.ty @!! go!"EnterJoint")) (Val #()))
  {{ (r : val), RET r; ownCCV2 c dq m ∗
      match enterJointOf m.transition m.changes.length with
      | some (autoLeave, ok) => ⌜r = PairV #autoLeave #ok⌝
      | none => ⌜∃ p, r = PanicV p⌝ }}

end spec

end EtcdGrove
end Perennial
