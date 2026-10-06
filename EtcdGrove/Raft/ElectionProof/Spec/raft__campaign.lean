/-
Port of `election_proof/spec_raft__campaign.v`.
-/
import EtcdGrove.Raft.ElectionProof.InvRaftPhys

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `campaign` becomes a candidate and broadcasts a vote request to every other voter.
Several protocol steps, refining one `Step.campaign` -- but stated here as a pure fact
about the resulting state, with no ghost state involved: the messages it sends are the
growth of the outbox, and whether that growth is protocol-legal is `Step`'s problem.

`peers` is existential because the Go code iterates the voter set in whatever order
`IDs` yields; `Step.campaign` accepts any permutation of `elements (cfg \ {[id]})`. -/
abbrev raft.campaign.spec : Prop :=
  ∀ (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (t : CampaignType),
  t ≠ campaignPreElection →
  s.role ≠ .leader →
  id ∈ cfg →
  -- `becomeCandidate` sets `r.Term := r.Term + 1` and `campaign` then sends at that
  -- term. `send` *panics* on a vote message whose `Term` is zero (`Panicf "term should
  -- be set when sending %s"` in `raft.send.impl`), which is why `raft.wp_send`
  -- requires `Term ≠ 0`. Without this premise the triple is **false** at
  -- `s.term = 2^64 - 1`: the term wraps to zero and the real code panics. Added
  -- 2026-09-16; see notes/STATUS.md.
  uint.Z s.term + 1 < 2 ^ 64 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhys cfg r id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"campaign")) (Val #t))
  {{ (peers : List w64) (pvs : GMap w64 (tracker.Progress × tracker.Inflights)), RET #();
      ⌜peers ≡ₚ elements (cfg \ {[id]})⌝ ∗
      let s' := becomeCandidate id s
      ownRaftPhys cfg r id
        { sendMsgs s'
            ([Msg.mk .voteResp id id s'.term false] ++
             ((fun to => Msg.mk .vote id to s'.term false) <$> peers))
          with prvals := pvs } }}

end spec

end EtcdGrove
end Perennial
