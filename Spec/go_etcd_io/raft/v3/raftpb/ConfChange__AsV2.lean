/-
`(*ConfChange).AsV2` (`raftpb/confchange.go:58`).

Users: raft's `RawNode.ApplyConfChange`/`node.ApplyConfChange` (through `ConfChangeI.AsV2`, R1),
`RawNode.Bootstrap` (`bootstrap.go:79`), `DescribeConfChange` (R3), etcd's `applyConfChange`.
Snippet: `examples/specreq/raftpb/confchange.go` (`ReqAsV2`).

Proof sketch: `confChangeV1Pts_unfold`; `GetType().Enum()` and `new(GetNodeId())` allocate fresh
cells (made read-only), the `[]*ConfChangeSingle` literal a fresh slice of one fresh single
(`pbRest_zero`, `singlePts_unfold`), the context slice is shared (read-only for good);
`confChangeV2Pts_unfold` folds the result, `Transition` unset (reads `Auto`).

Changes: from `specs-ref/.../raftpb/ConfChange__AsV2.lean`: over raftpb's predicates and model.
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

/-- `p.AsV2()` of a `ConfChange` `c`: a fresh, owned `ConfChangeV2` holding `c.asV2` (one change,
transition `Auto`, the same context). -/
def ConfChange.AsV2.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (c : ConfChangeV1),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ confChangeV1Pts p dq c }}
    (App (Val (p @!! go.GoType.PointerType raftpb.ConfChange.ty @!! go!"AsV2")) (Val #()))
  {{ (r : Loc), RET #r; confChangeV1Pts p dq c ∗ confChangeV2Pts r (DFrac.own 1) c.asV2 }}

end spec

end RaftPb
end EtcdGrove
end Perennial
