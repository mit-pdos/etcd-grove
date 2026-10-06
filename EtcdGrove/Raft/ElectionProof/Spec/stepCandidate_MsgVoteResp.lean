/-
Port of `election_proof/spec_stepCandidate_MsgVoteResp.v`.
-/
import EtcdGrove.Raft.ElectionProof.InvRaftPhys
import EtcdGrove.Raft.ElectionProof.StepLemmas

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

/-- `stepCandidate` on a `MsgVoteResp`: record the vote, then win, lose or keep
waiting.

Ghost-free. It used to take `ownRaftGhost` and `isMessage` for the incoming message,
but that was only ever feeding `ownRaftGhost_step`; `isMessage` is what justifies *the
model transition*, not the code, so it belongs at the one place the transition is
taken — `Step`. -/
abbrev stepCandidate_MsgVoteResp.spec : Prop :=
  ∀ (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (m : raftpb.Message),
  m.Type' = MsgVoteResp →
  m.To' = id →
  m.Term' = s.term →
  s.role = .candidate →
  -- A candidate that can win an election is a voter. `poll` needs `cfg` in scope and
  -- `becomeLeader` needs this premise outright; neither is available from
  -- `ownRaftPhys`, so it is threaded in from the caller.
  id ∈ cfg →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhys cfg r id s }}
    (App (App (Val #(functions stepCandidate [])) (Val #r)) (Val #m))
  {{ (err : GoInterface) (s' : NState), RET #err;
      ownRaftPhys cfg r id s' ∗
      -- `ms` is what `bcastAppend` broadcast on a win: some list of `App`s from `id`
      -- at the current term, possibly empty. `recordVote` does not touch the term, so
      -- this is `s`'s term.
      --
      -- The quorum facts are **part of the spec**, not incidental. Without them this
      -- triple is true but useless to its caller: `Step`'s `MsgVoteResp` branch has to
      -- justify the resulting `.leader` by `Step.win`, whose premise is
      -- `IsQuorum cfg (granted …)`, and no other `Step` rule produces a leader. `poll`
      -- establishes both facts and `Proof/stepCandidate_MsgVoteResp.lean` receives
      -- them as `%Hwon`/`%Hlost`; before 2026-09-16 it dropped them on the floor and
      -- `won`/`lost` escaped here as unconstrained booleans.
      --
      -- `recordVote` does not touch the term, so `s1`'s term is `s`'s.
      ⌜∃ (won lost : Bool) (ms : List Msg) (pvs : GMap w64 (tracker.Progress × tracker.Inflights)),
          let votes' := recordVote s.votes m.From' (!m.Reject')
          AppSends id s.term ms ∧
          (won = true → IsQuorum cfg (granted votes')) ∧
          (lost = true → ¬ IsQuorum cfg (cfg \ rejected votes')) ∧
          s' = { voteRespResult id s m.From' m.Reject' won lost ms with prvals := pvs }⌝ ∗
      -- The `MsgVoteResp` arm of `stepCandidate`'s type switch ends in `return nil`.
      -- `Step` needs this written down: its own postcondition claims a `nil` error,
      -- and the code propagates a non-nil one out of `r.step(m)` unchanged.
      ⌜err = interface.nil⌝ }}

end spec

end EtcdGrove
end Perennial
