/-
## `(*raftLog).hasNextOrInProgressSnapshot()` (internal)

**Users**: `nextCommittedEnts`, `hasNextCommittedEnts`, `raft.promotable` (`raft.go:1949`).
Mirrors the code. **Changes**: from `specs-ref/Spec/go_etcd_io/raft/v3/raftLog__hasNextOrInProgressSnapshot.lean`.
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

/-- (internal) Whether a snapshot is pending. -/
def raftLog.hasNextOrInProgressSnapshot.spec : Prop :=
  ∀ (l : Loc) (ls : LogState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftLog l ls }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.raft.v3.raftLog.ty @!! go!"hasNextOrInProgressSnapshot")) (Val #()))
  {{ RET #(ls.us.snap.isSome); raftLog l ls }}

end spec
end Raft
end EtcdGrove
end Perennial
