/-
Port of election_proof/spec_raft__hup.v (feb5c73d4).

raft v3.7 (2026-10-15, stage R1/R4): the `section results` (`HupOk`, `HupGuard`, `HupOkC`,
`HupOkC.simple`) moved verbatim to `Proof/.../SpecResults.lean` in R1.
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvRaftPhys
public import RaftWitness.Proof.go_etcd_io.raft.v3.StepLemmasC
public import RaftWitness.Proof.go_etcd_io.raft.v3.SpecResults

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

/-- `hup` checks the node is a promotable voter with no unapplied configuration change,
then campaigns. Genuinely disjunctive — it either campaigns or returns having done
nothing (already a leader, unpromotable, or, since 2026-10-13, a conf-change entry
committed but not applied: `hasUnappliedConfChanges`) — so unlike `campaign` its
postcondition names the model's relation rather than a specific state; the do-nothing
case is `Step.refl`. Since 2026-10-04 `t` is any campaign
type, `campaignPreElection` included: a pre-election is `Step.abandon` and free sends
(`step_campaignState`, `StepLemmas.lean`).

Ghost-free: the `Step` witness is a pure fact handed to the caller, which is where it is
turned into an update of `ownRaftGhost`.

At any configuration since 2026-10-13 (reconfiguration stage A2): the post is `HupOkC`, a
`StepC c` step (a campaign by a voter of either half, asking every other one), and nothing
at a node that is not a voter. The old statement, `raft.hup.specS`, had no caller and is gone (2026-10-17). -/
abbrev raft.hup.spec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (t : CampaignType),
  -- `hup` may reach `campaign`, which increments the term -- see the note on
  -- `raft.campaign.spec`.
  uint.Z s.term + 1 < 2 ^ 64 →
  -- a pre-election only with pre-vote on (2026-10-10; see `raft.campaign.spec`)
  -- (2026-10-17) and its next term within the ceiling (`NGhost.tc`)
  (t = campaignPreElection → s.prevote = true ∧ uint.Z s.term + 1 ≤ uint.Z s.gh.tc) →
  -- `r.step` matches the role; kept by the call
  NStateWf s →
  -- (D19i part 1) the floor at most `applied` (`hasUnappliedConfChanges`')
  uint.Z s.logst.fl ≤ uint.Z s.logst.applied →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhysCV c c.voters r id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"hup")) (Val #t))
  {{ (s' : NState), RET #();
      ownRaftPhysCV c c.voters r id s' ∗ ⌜HupOkC c id s s'⌝ ∗
      -- (2026-10-17) only a pre-election makes a pre-candidate
      ⌜s'.role = .preCandidate → s'.role = s.role ∨ t = campaignPreElection⌝ }}

end spec

end EtcdGrove
end Perennial
