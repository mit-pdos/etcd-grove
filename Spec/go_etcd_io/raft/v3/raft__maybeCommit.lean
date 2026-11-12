/- Port of election_proof/spec_raft__maybeCommit.v (feb5c73d4).

Lean notes: Rocq's `commit_ok` (a Prop-valued definition) is `CommitOkC` (at a configuration; until 2026-10-24 also `CommitOk`, at a simple one).
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section commit_ok
variable [GooseExts]

/-- `CommitOkC c ps n`: a leader in protocol state `ps` may advance its commit index to `n` at
the configuration `c` -- exactly the premises of `StepC.commit` other than the role: `n` is past
the current commit index and inside the log, the entry there is of the leader's own term, and a
joint quorum (`JQuorum`) has acknowledged `n` (`ackedBy`, over `matched`). (Until 2026-10-24
also `CommitOk`, at a simple configuration's voters.) -/
def CommitOkC (c : CfgM) (ps : PState) (n : w64) : Prop :=
  uint.Z ps.commit < uint.Z n ∧
  uint.Z n ≤ plogLastIndexZ ps.base ps.log ∧
  plogTermAt ps.base ps.log n = some ps.term ∧
  JQuorum c (ackedBy ps n)

end commit_ok

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `r.maybeCommit()` (`raft.maybeCommit.impl`, `Code/go_etcd_io/raft/v3.lean`;
`raft.go:773`):

    defer traceCommit(r)
    return r.raftLog.maybeCommit(entryID{term: r.Term, index: r.trk.Committed()})

`Committed()` is the quorum index of the voters' `Match` values
(`Spec/ProgressTracker__Committed.lean`); `raftLog.maybeCommit` moves `committed` there
when it is ahead, the term is non-zero and the log has `r.Term` at that index
(`Spec/raftLog__maybeCommit.lean`). The deferred `traceCommit` is a no-op.

On `true` the new commit index `N` satisfies `CommitOk` at the protocol reading of `s`:
that is `Step.commit`. The quorum is stated over `toPState s`'s `matched`, which is the
`Progress` `Match` values only for a leader -- hence `s.role = .leader`; the go code
says "This can only be called in StateLeader". `id ∈ cfg` makes the voter set
non-empty, which is what makes `Committed()` a quorum index (for an empty configuration
it is `MaxUint64`). On `false` nothing changes.

At any configuration since 2026-10-13 (reconfiguration stage A2): `CommitOkC`, a joint quorum
of the two voter halves, with no premise on the voters (an empty half has committed
everything, `MajQ`). The old statement (`id ∈ cfg`, `CommitOk cfg`) was
`raft.maybeCommit.specS`; it had no caller and is gone (2026-10-17). -/
abbrev raft.maybeCommit.spec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState),
  s.role = .leader →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"maybeCommit")) (Val #()))
  {{ (b : Bool) (N : w64), RET #b;
      ownRaftPhysCV c c.voters r id
        (if b then { s with logst := { s.logst with committed := N } } else s) ∗
      ⌜b = true → CommitOkC c (toPState s) N⌝ }}

end spec

end EtcdGrove
end Perennial
