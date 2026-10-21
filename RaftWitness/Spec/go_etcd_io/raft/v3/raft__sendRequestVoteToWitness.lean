/-
`(*raft).sendRequestVoteToWitness` (raft#168, `raft.go`; 2026-10-20, witness support).
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

/-- The vote request `sendRequestVoteToWitness` queues, at the log `b`/`es` and the vote tally
`votes`: from `id` to `wid`, of type `vt` (`MsgVote`, `MsgPreVote`) and term `term`, with the log's
last entry and the reported subterm `ls`, the tally (its keys are the responders), no context and
no replication set. -/
def wVoteM [FfiSyntax] (id wid : w64) (vt : raftpb.MessageType) (term : w64) (b : entryID)
    (es : List EntryM) (ls : w64) (votes : GMap w64 Bool) : WMsg :=
  ⟨vt, id, wid, term, (plogLast b es).term', ls, (plogLast b es).index', [], [], votes, []⟩

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `r.sendRequestVoteToWitness(nil, wid, vt, term)`:

    last := r.raftLog.lastEntryID()
    _, subterm, ok := r.raftLog.subterm(last.index)
    if !ok { subterm = 0 }
    v := a copy of r.trk.Votes
    r.witnessMsgs = append(r.witnessMsgs, WitnessMessage{From: r.id, To: wid, Type: vt,
      Term: term, LastLogTerm: last.term, LastLogSubterm: subterm, LastLogIndex: last.index,
      Votes: v})
    r.logger.Infof(...)

At a configuration with a witness (`r.witnessMsgs` holds the configuration's requests): the
request `wVoteM` is queued, on the node's outbox (`sendMsgs`), its subterm the last entry's or
`0` (the entry compacted out of the storage, or none past the boundary). -/
abbrev raft.sendRequestVoteToWitness.spec : Prop :=
  ∀ (c : CfgM) (V : GSet w64) (r : Loc) (id : w64) (s : NState) (wid : w64)
    (vt : raftpb.MessageType) (term : w64),
  c.wit ≠ W64 0 →
  -- (2026-10-20, W4) to the configuration's witness, a vote request of the node's term (what the
  -- queue records, `WqOk`; a pre-vote's is the next one)
  wid = c.wit → (vt ≠ MsgPreVote → uint.Z term ≤ uint.Z s.term) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhysCV c V r id s }}
    (App (App (App (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"sendRequestVoteToWitness"))
      (Val #slice.nil)) (Val #wid)) (Val #vt)) (Val #term))
  {{ (ls : w64), RET #();
      ownRaftPhysCV c V r id (sendMsgs s [wAbs (wVoteM id wid vt term s.logst.prev
        (s.logst.sents ++ s.logst.uents) ls s.votes)]) ∗
      ⌜ls = W64 0 ∨ ls = plogLastSub (s.logst.sents ++ s.logst.uents)⌝ }}

end spec

end EtcdGrove
end Perennial
