/-
Port of `election_proof/spec_raft__campaign.v` (feb5c73d4).

Lean notes: the type of Rocq's untyped binder `pvs` is written out
(`GMap w64 Progress`, as `NState.prvals` forces it); `bool_decide` is `decide`;
`campaign_state` is `campaignState` (`Defs.lean`), `step_campaign_state` is
`StepLemmas.lean`'s.
-/
import EtcdGrove.Raft.InvRaftPhys

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

/-- `campaign(t)` becomes a candidate -- or, for `t = campaignPreElection` (since
2026-10-04), a pre-candidate -- and broadcasts a vote request to every other voter, plus
the self-addressed response. Stated as a pure fact about the resulting state,
`campaignState` (`Defs.lean`), with no ghost state involved: the messages it sends are
the growth of the outbox, and whether that growth is protocol-legal is `Step`'s problem
(`step_campaign_state`, `StepLemmas.lean`).

`peers` is existential because the Go code iterates the voter set in whatever order
`IDs` yields; `Step.campaign` accepts any permutation of `elements (cfg \ {[id]})`.

`promotable` is checked first and only logged; until 2026-10-04 the spec assumed no
pending snapshot so that the warning was dead, but `stepCandidate`'s pre-vote win calls
`campaign` with no such fact at hand, so the warning arm is now covered. -/
abbrev raft.campaign.spec : Prop :=
  ∀ (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (t : CampaignType),
  s.role ≠ .leader →
  id ∈ cfg →
  -- Every request and the self-addressed response carry `Term + 1`: for an election
  -- `becomeCandidate` has raised `r.Term` to it, for a pre-election it is computed.
  -- `send` *panics* on a vote message whose `Term` is zero (`Panicf "term should be set
  -- when sending %s"` in `raft.send.impl`), which is why `raft.wp_send` requires
  -- `Term ≠ 0`. Without this premise the triple is **false** at `s.term = 2^64 - 1`:
  -- the term wraps to zero and the real code panics. Added 2026-09-16; see
  -- notes/STATUS.md.
  uint.Z s.term + 1 < 2 ^ 64 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhys cfg r id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"campaign")) (Val #t))
  {{ (peers : List w64) (pvs : GMap w64 Progress), RET #();
      ⌜peers ≡ₚ elements (cfg \ {[id]})⌝ ∗
      -- each request carries the `lastEntryID()` read just before it was built
      -- (`Index: last.index, LogTerm: last.term`) -- the log's last entry id, the same
      -- for every peer: nothing in the loop changes the log
      ownRaftPhys cfg r id
        { campaignState id s (decide (t = campaignPreElection)) peers with prvals := pvs } }}

end spec

end EtcdGrove
end Perennial
