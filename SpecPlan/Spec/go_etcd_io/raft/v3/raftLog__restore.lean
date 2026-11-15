/-
## `(*raftLog).restore(s)` (internal)

**Users**: `raft.restore` (`raft.go:1937`), after its check `s.index > committed` and outside the
fast-forward. Snippet `raftlog/snapshot.go` (`ReqRestore`).

**Proof sketch**: `committed := s.index`, `unstable.restore` (a clone, read-only for good). The
invariant's relation is suspended while the snapshot is pending unstored (`snapStored = false`); the
snapshot is valid (`V s`) for the hand-out; it is past `committed`, hence past every floor and the
stored snapshot (so its install will not be refused as out of date).

**Changes**: from `specs-ref/Spec/go_etcd_io/raft/v3/raftLog__restore.lean`: validity through `V` (was the ghost list `ksn`).

**Margin**: none.
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

/-- (internal) Restart the log at snapshot `s` (pending, to be stored). -/
def raftLog.restore.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (sp : Loc) (dq : DFrac) (s : Snapshot)
    (S : StorState → IProp GF) (V : Snapshot → IProp GF) (N : Namespace),
  ls.committed < uint.nat s.index → uint.nat s.index + 1 < 2 ^ 64 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftLog l ls ∗ logStorage l S V N ∗ snapshotPts sp dq s ∗ V s }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.raft.v3.raftLog.ty @!! go!"restore")) (Val #sp))
  {{ RET #(); raftLog l (ls.restore s) ∗ snapshotPts sp dq s }}

end spec
end Raft
end EtcdGrove
end Perennial
