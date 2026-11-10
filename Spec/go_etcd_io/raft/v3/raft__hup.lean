/-
Port of election_proof/spec_raft__hup.v (feb5c73d4).

raft v3.7 (2026-10-15, stage R1/R4): the `section results` (`HupOk`, `HupGuard`, `HupOkC`,
`HupOkC.simple`) moved verbatim to `Proof/.../SpecResults.lean` in R1.
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys
public import Proof.go_etcd_io.raft.v3.StepLemmasC
public import Proof.go_etcd_io.raft.v3.SpecResults
public import Proof.go_etcd_io.raft.v3.TracedMsg
public import Proof.go_etcd_io.raft.v3.TracedSend
public import Proof.go_etcd_io.raft.v3.LemmasCampaign

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
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
at a node that is not a voter. The old statement, `raft.hup.specS`, had no caller and is gone (2026-10-17).

**One spec for both trace modes** (2026-11-10, trace-check Q8 stage 1 slice 7): `campaign`'s gates
(`raft.campaign.spec`), at `s`, used only if `hup` campaigns; the caller's resource comes back as
`G0` with the state unchanged (no campaign: nothing is traced) or as `G` (a campaign). Until slice 7
the premise `s.gh.tr = none` (stage 0), now `raft.hup.untraced`'s (`TracedUntracedStep.lean`). -/
abbrev raft.hup.spec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (t : CampaignType) (G0 : IProp GF)
    (G : List Msg → IProp GF),
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
  -- (2026-11-10, slice 14) `campaign`'s resource indexed by the outbox up to order
  PermInv G →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhysCV c c.voters r id s ∗
      -- (2026-11-10, Q8 stage 1 slice 7; until then, stage 0, the premise `s.gh.tr = none`)
      -- `campaign`'s gates, the caller's resource through them
      "HG" ∷ G0 ∗
      "Hgbc" ∷ (G0 -∗ if t = campaignPreElection then iprop(|={⊤}=> G s.outbox)
        else HookGate s.gh.tr r (NodeEvOf (W64 1) id (becomeCandidate id s) c) (G s.outbox)) ∗
      "#Hgsend" ∷ □ (∀ (pvs : GMap w64 Progress) (y : w64) (o : List Msg), ⌜y ∈ c.voters⌝ -∗ G o -∗
        HookGateOpt s.gh.tr r
          (sendOutGate id { campRoleState id s (decide (t = campaignPreElection)) with prvals := pvs } c
            (if y = id then vrespW32 (decide (t = campaignPreElection))
             else vreqW32 (decide (t = campaignPreElection)))
            [campMsg (decide (t = campaignPreElection)) id (s.term + W64 1)
              (plogLast s.logst.prev (s.logst.sents ++ s.logst.uents)) (transferCtx t) y])
          (G (o ++ [campMsg (decide (t = campaignPreElection)) id (s.term + W64 1)
              (plogLast s.logst.prev (s.logst.sents ++ s.logst.uents)) (transferCtx t) y]))) }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"hup")) (Val #t))
  {{ (s' : NState), RET #();
      ownRaftPhysCV c c.voters r id s' ∗
      -- (Q8 stage 1, slice 7) no campaign, nothing traced: `G0`, at `s`; a campaign: `G`
      ((⌜s' = s⌝ ∗ G0) ∨ G s'.outbox) ∗ ⌜HupOkC c id s s'⌝ ∗
      -- (2026-10-17) only a pre-election makes a pre-candidate
      ⌜s'.role = .preCandidate → s'.role = s.role ∨ t = campaignPreElection⌝ }}

end spec

end EtcdGrove
end Perennial
