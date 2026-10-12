/-
Port of election_proof/spec_raft__hup.v (feb5c73d4).
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

/-- `hup` checks the node is a promotable voter with no unapplied configuration change,
then campaigns. Genuinely disjunctive — it either campaigns or returns having done
nothing — so unlike `campaign` its postcondition names the model's relation rather than
a specific state; the do-nothing case is `Step.refl`. Since 2026-10-04 `t` is any campaign
type, `campaignPreElection` included: a pre-election is `Step.abandon` and free sends
(`step_campaignState`, `StepLemmas.lean`).

Ghost-free: the `Step` witness is a pure fact handed to the caller, which is where it is
turned into an update of `ownRaftGhost`. -/
abbrev raft.hup.spec : Prop :=
  ∀ (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (t : CampaignType),
  -- `hup` may reach `campaign`, which increments the term -- see the note on
  -- `raft.campaign.spec`.
  uint.Z s.term + 1 < 2 ^ 64 →
  -- a pre-election only with pre-vote on (2026-10-10; see `raft.campaign.spec`)
  (t = campaignPreElection → s.prevote = true) →
  -- not a leader transfer's (2026-10-12; see `raft.campaign.spec`)
  t ≠ campaignTransfer →
  -- `r.step` matches the role; kept by the call
  NStateWf s →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhys cfg r id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"hup")) (Val #t))
  {{ (s' : NState), RET #();
      ownRaftPhys cfg r id s' ∗ ⌜NStateWf s'⌝ ∗
      ⌜Step cfg id (toPState s) [] (toPState s')⌝ ∗
      -- the log is untouched and the term moves up by at most one (2026-10-09); and
      -- `r.preVote` is kept (2026-10-10)
      ⌜s'.logst = s.logst ∧ uint.Z s.term ≤ uint.Z s'.term ∧
       uint.Z s'.term ≤ uint.Z s.term + 1 ∧ s'.prevote = s.prevote ∧ s'.gh = s.gh⌝ }}

end spec

end EtcdGrove
end Perennial
