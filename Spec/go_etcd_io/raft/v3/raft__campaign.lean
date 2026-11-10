/-
Port of `election_proof/spec_raft__campaign.v` (feb5c73d4).

Lean notes: the type of Rocq's untyped binder `pvs` is written out
(`GMap w64 Progress`, as `NState.prvals` forces it); `bool_decide` is `decide`;
`campaign_state` is `campaignState` (`Defs.lean`), `step_campaign_state` is
`StepLemmas.lean`'s.
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys
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

/-- `campaign(t)` becomes a candidate -- or, for `t = campaignPreElection` (since
2026-10-04), a pre-candidate -- and broadcasts a vote request to every other voter, plus
the self-addressed response. Stated as a pure fact about the resulting state,
`campaignState` (`Defs.lean`), with no ghost state involved: the messages it sends are
the growth of the outbox, and whether that growth is protocol-legal is `Step`'s problem
(`step_campaign_state`, `StepLemmas.lean`).

`peers` is existential because the Go code iterates the voter set in whatever order
`IDs` yields; `Step.campaign` accepts any permutation of `elements (cfg \ {[id]})`. At any
configuration (2026-10-13, reconfiguration stage A2) the voters are those of either half,
`c.voters` (`JointConfig.IDs`, `StepC.campaign`); the old statement, `raft.campaign.specS`, had no caller and is gone (2026-10-17).

`promotable` is checked first and only logged; until 2026-10-04 the spec assumed no
pending snapshot so that the warning was dead, but `stepCandidate`'s pre-vote win calls
`campaign` with no such fact at hand, so the warning arm is now covered.

**One spec for both trace modes** (2026-11-10, trace-check Q8 stage 1 slice 7): the caller's
resource `G0` goes through the `BecomeCandidate` line's gate (`becomeCandidate`'s, an election only;
a pre-election traces nothing there and `G0` becomes `G` by an update) and `G` through each vote
message's send gate, persistent (`□`, one per voter in `IDs`' order, as `bcastHeartbeat`'s): the
self-addressed response and every request, `campMsg` of the voter, at the state after the role
change (`campRoleState`; the event's header reads nothing the earlier sends change), and comes
back. Until slice 7 the premise `s.gh.tr = none` (stage 0), now `raft.campaign.untraced`'s
(`TracedUntracedStep.lean`). -/
abbrev raft.campaign.spec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (t : CampaignType) (G0 : IProp GF)
    (G : List Msg → IProp GF),
  s.role ≠ .leader →
  id ∈ c.voters →
  -- Every request and the self-addressed response carry `Term + 1`: for an election
  -- `becomeCandidate` has raised `r.Term` to it, for a pre-election it is computed.
  -- `send` *panics* on a vote message whose `Term` is zero (`Panicf "term should be set
  -- when sending %s"` in `raft.send.impl`), which is why `raft.wp_send` requires
  -- `Term ≠ 0`. Without this premise the triple is **false** at `s.term = 2^64 - 1`:
  -- the term wraps to zero and the real code panics. Added 2026-09-16; see
  -- notes/STATUS.md.
  uint.Z s.term + 1 < 2 ^ 64 →
  -- a pre-election only with pre-vote on (2026-10-10): its pre-vote messages are of the
  -- next term, which `ownRaftPhys` allows only then (`OutTermOk`); `hup` is called with
  -- `campaignPreElection` exactly when `r.preVote`
  -- (2026-10-17) and the next term within the ceiling (`NGhost.tc`), which the `RawNode` raises
  -- before a `MsgHup`
  (t = campaignPreElection → s.prevote = true ∧ uint.Z s.term + 1 ≤ uint.Z s.gh.tc) →
  -- (2026-11-10, slice 14) the caller's resource after the role change indexed by the outbox, up to
  -- order: the result names the messages in another order than they are sent (`PermInv`)
  PermInv G →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhysCV c c.voters r id s ∗
      -- (2026-11-10, Q8 stage 1 slice 7; until then, stage 0, the premise `s.gh.tr = none`) the
      -- caller's resource, through the role change's gate ...
      "HG" ∷ G0 ∗
      "Hgbc" ∷ (G0 -∗ if t = campaignPreElection then iprop(|={⊤}=> G s.outbox)
        else HookGate s.gh.tr r (NodeEvOf (W64 1) id (becomeCandidate id s) c) (G s.outbox)) ∗
      -- ... and each vote message's send gate (voter `y`'s, at the state after the role change), from
      -- `G` at the outbox `o` before it to `G` with the message queued
      "#Hgsend" ∷ □ (∀ (pvs : GMap w64 Progress) (y : w64) (o : List Msg), ⌜y ∈ c.voters⌝ -∗ G o -∗
        HookGateOpt s.gh.tr r
          (sendOutGate id { campRoleState id s (decide (t = campaignPreElection)) with prvals := pvs } c
            (if y = id then vrespW32 (decide (t = campaignPreElection))
             else vreqW32 (decide (t = campaignPreElection)))
            [campMsg (decide (t = campaignPreElection)) id (s.term + W64 1)
              (plogLast s.logst.prev (s.logst.sents ++ s.logst.uents)) (transferCtx t) y])
          (G (o ++ [campMsg (decide (t = campaignPreElection)) id (s.term + W64 1)
              (plogLast s.logst.prev (s.logst.sents ++ s.logst.uents)) (transferCtx t) y]))) }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"campaign")) (Val #t))
  {{ (peers : List w64) (pvs : GMap w64 Progress), RET #();
      ⌜peers ≡ₚ elements (c.voters \ {[id]})⌝ ∗
      -- each request carries the `lastEntryID()` read just before it was built
      -- (`Index: last.index, LogTerm: last.term`) -- the log's last entry id, the same
      -- for every peer: nothing in the loop changes the log -- and (2026-10-13) for a
      -- leader transfer's campaign the marker as its `Context` (`transferCtx`)
      ownRaftPhysCV c c.voters r id
        { campaignState id s (decide (t = campaignPreElection)) peers (transferCtx t)
            with prvals := pvs } ∗
      G ({ campaignState id s (decide (t = campaignPreElection)) peers (transferCtx t)
            with prvals := pvs } : NState).outbox }}

end spec

end EtcdGrove
end Perennial
