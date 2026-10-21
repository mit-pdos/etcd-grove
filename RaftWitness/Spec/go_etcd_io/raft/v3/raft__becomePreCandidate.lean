/-
Port of election_proof/spec_raft__becomePreCandidate.v (feb5c73d4).

Lean notes:
* `become_precandidate` is `becomePrecandidate` (`Defs.lean`); `prole.Leader` is
  `PRole.leader`.
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvRaftPhys

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

/-- `becomePreCandidate` (raft.go:912, 2026-10-04): `r.step := stepCandidate`,
`r.trk.ResetVotes()`, `r.tick`, `r.lead := None`, `r.state := StatePreCandidate`, and a
log line. Term and vote are untouched and there is no `reset`, so the `Progress` values
stay (`becomePrecandidate`, `Defs.lean`). The panic branch (`state = StateLeader`) is
discharged from the role premise. -/
abbrev raft.becomePreCandidate.spec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState),
  s.role ≠ .leader →
  -- (2026-10-13) only a voter campaigns (`ownRaftPhys`'s `Hvoter`)
  id ∈ c.voters →
  -- (2026-10-14, reconfiguration stage B7 part 2) only with pre-vote on (`campaign`'s premise
  -- for a pre-election): `ownRaftPhys` keeps that a pre-candidate has pre-vote on
  s.prevote = true →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhysCV c c.voters r id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"becomePreCandidate"))
      (Val #()))
  {{ RET #(); ownRaftPhysCV c c.voters r id (becomePrecandidate s) }}

end spec

end EtcdGrove
end Perennial
