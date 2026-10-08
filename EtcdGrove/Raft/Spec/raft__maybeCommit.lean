/- Port of election_proof/spec_raft__maybeCommit.v (feb5c73d4).

Lean notes: Rocq's `commit_ok` (a Prop-valued definition) is `CommitOk`.
-/
import EtcdGrove.Raft.InvRaftPhys

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section commit_ok
variable [FfiSyntax]

/-- `CommitOk cfg ps n`: a leader in protocol state `ps` may advance its commit index to
`n` -- exactly the premises of the model's `Step.commit` other than the role: `n` is
past the current commit index and inside the log, the entry there is of the leader's
own term, and a quorum of voters has acknowledged `n` (`ackedBy`, over `matched`).
Shared with `Spec/stepLeader.lean`. -/
def CommitOk (cfg : GSet w64) (ps : PState) (n : w64) : Prop :=
  uint.Z ps.commit < uint.Z n ∧
  uint.Z n ≤ plogLastIndexZ ps.base ps.log ∧
  plogTermAt ps.base ps.log n = some ps.term ∧
  IsQuorum cfg (ackedBy ps n)

end commit_ok

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `r.maybeCommit()` (`raft.maybeCommit.impl`, `EtcdRaft/Code/go_etcd_io/raft/v3.lean`;
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
it is `MaxUint64`). On `false` nothing changes. -/
abbrev raft.maybeCommit.spec : Prop :=
  ∀ (cfg : GSet w64) (r : Loc) (id : w64) (s : NState),
  s.role = .leader →
  id ∈ cfg →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhys cfg r id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"maybeCommit")) (Val #()))
  {{ (b : Bool) (N : w64), RET #b;
      ownRaftPhys cfg r id
        (if b then { s with logst := { s.logst with committed := N } } else s) ∗
      ⌜b = true → CommitOk cfg (toPState s) N⌝ }}

end spec

end EtcdGrove
end Perennial
