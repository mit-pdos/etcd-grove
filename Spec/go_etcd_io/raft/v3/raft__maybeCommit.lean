/- Port of election_proof/spec_raft__maybeCommit.v (feb5c73d4).

Lean notes: Rocq's `commit_ok` (a Prop-valued definition) is `CommitOk`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys

@[expose] public section

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

/-- `CommitOk` at a joint configuration (2026-10-13, reconfiguration stage A2): the premises
of `StepC.commit` other than the role, a joint quorum (`JQuorum`) acknowledging `n`. -/
def CommitOkC (c : CfgM) (ps : PState) (n : w64) : Prop :=
  uint.Z ps.commit < uint.Z n ∧
  uint.Z n ≤ plogLastIndexZ ps.base ps.log ∧
  plogTermAt ps.base ps.log n = some ps.term ∧
  JQuorum c (ackedBy ps n)

/-- At a simple configuration with voters, `CommitOkC` is `CommitOk`. -/
theorem CommitOkC.simple {cfg lrn : GSet w64} {ps : PState} {n : w64} (hne : cfg ≠ ∅)
    (h : CommitOkC (CfgM.simple cfg lrn) ps n) : CommitOk cfg ps n :=
  ⟨h.1, h.2.1, h.2.2.1, (JQuorum_of_out (c := CfgM.simple cfg lrn) hne rfl _).1 h.2.2.2⟩

end commit_ok

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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
everything, `MajQ`). The old statement (`id ∈ cfg`, `CommitOk cfg`) is
`raft.maybeCommit.specS`. -/
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

/-- The statement on `ownRaftPhys` (the simple configuration `cfg`) until 2026-10-13,
derived from `raft.maybeCommit.spec` by `raft.maybeCommit.spec_simple`. -/
abbrev raft.maybeCommit.specS : Prop :=
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

open Iris.ProofMode in
theorem raft.maybeCommit.spec_simple
    (H : raft.maybeCommit.spec (GF := GF) (hG := hG)) :
    raft.maybeCommit.specS (GF := GF) (hG := hG) := by
  intro cfg r id s Hlead Hid
  have Hne : cfg ≠ ∅ := by
    intro h; rw [h] at Hid; exact GMap.not_elem_of_empty _ Hid
  iintro %Φ ⟨#Hpkg, Hphys⟩ HΦ
  ihave Hphys := ownRaftPhys_toC' $$ Hphys
  iapply H _ r id s Hlead $$ [$Hpkg $Hphys]
  inext
  iintro %b %N ⟨Hphys, %Hok⟩
  ihave Hphys := ownRaftPhysC_toS $$ Hphys
  iapply HΦ
  iframe Hphys
  ipureintro
  exact fun hb => (Hok hb).simple Hne

end spec

end EtcdGrove
end Perennial
