/-
Port of `election_proof/spec_raft__appliedTo.v` (857d09190).
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `r.appliedTo(index, size)` (`raft.go:735`):

    oldApplied := r.raftLog.applied
    newApplied := max(index, oldApplied)
    r.raftLog.appliedTo(newApplied, size)
    if r.trk.Config.AutoLeave && newApplied >= r.pendingConfIndex && r.state == StateLeader {
        ... propose leaving the joint configuration (r.Step) ...
    }

The log's `applied` moves to `max(index, applied)` (`logAppliedTo`,
`InvReadylog.lean`). The auto-leave branch is dead: no joint configuration in scope
(`ownTracker`'s `AutoLeave = false`), so its `r.Step` is never reached and is not a
callee of this proof. The premise is `raftLog.appliedTo`'s `Panicf` guard on the new
`applied` (`applied <= committed` already holds). -/
abbrev raft.appliedTo.spec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (index size : w64),
  uint.Z index ≤ uint.Z s.logst.committed →
  -- (2026-10-14, stage B7: at any configuration) the auto-leave branch is not taken: no
  -- `AutoLeave` at a leader. Its `r.Step` would make this function and `raft.Step` mutually
  -- recursive, which the link (one proof per function, callees' specs as hypotheses) does
  -- not express; a joint configuration entered with an explicit transition is in scope.
  (c.autoLeave = true → s.role ≠ .leader) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s }}
    (App (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"appliedTo")) (Val #index))
      (Val #size))
  {{ RET #();
      ownRaftPhysCV c c.voters r id { s with logst := logAppliedTo s.logst index size } }}

end spec

end EtcdGrove
end Perennial
