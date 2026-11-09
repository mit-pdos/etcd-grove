/-
`(*ConfChangeV2).EnterJoint` (`raftpb/confchange.go:86`).

Users: raft's `applyConfChange` (`raft.go:1949`, R2: the dispatch R4's `changeV2` models), the
examples' pre-check (`examples/specreq/raftconf/confchange.go`, `validConf`). Snippet:
`examples/specreq/raftpb/confchange.go` (`ReqEnterLeave`).

Proof sketch: `confChangeV2Pts_unfold`: `GetTransition()` and `len(c.Changes)` (the slice's
length, `ccsPts`); the switch; the `default` branch panics (`fmt.Sprintf` of the change), which
the premise excludes (`enterJoint = none` exactly there).

Changes: from `specs-ref/.../raftpb/ConfChangeV2__EnterJoint.lean`: over the pure
`ConfChangeV2.enterJoint` (R4's `changeV2` reads the same dispatch).
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

/-- `p.EnterJoint()` of a change whose transition is known (or `Auto` with at most one change):
`c.enterJoint`'s pair. -/
def ConfChangeV2.EnterJoint.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (c : ConfChangeV2) (al ok : Bool),
  c.enterJoint = some (al, ok) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ confChangeV2Pts p dq c }}
    (App (Val (p @!! go.GoType.PointerType raftpb.ConfChangeV2.ty @!! go!"EnterJoint")) (Val #()))
  {{ RET (PairV #al #ok); confChangeV2Pts p dq c }}

end spec

end RaftPb
end EtcdGrove
end Perennial
