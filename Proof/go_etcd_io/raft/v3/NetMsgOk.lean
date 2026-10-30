/-
# Messages from the network, as `RawNode.Step` takes them (raft-final, 2026-10-29)

`NetMsgOk` and its vocabulary, moved from `ApiVocab.lean` (the design's A7: internal, since the node
API's `stepIn_intro` no longer mentions it, so no client proves it; until then clients proved it to
call `stepIn_intro`). Its transfer clause admits a stamped `MsgTransferLeader` to the node (a
follower's forward to its leader), whose witness `raft.Step` takes (`isRaftMsg`).
-/
module

public import Proof.go_etcd_io.raft.v3.ApiVocab

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI OFE CMRA Iris.ProofMode go_etcd_io.raft.v3

section
variable [GooseExts]

/-- The message types `RawNode.Step` is specified for: replication, leader election,
(2026-10-13) read-index, leader transfer and the local reports, (2026-10-17) pre-vote and
(2026-10-20, D22 S-c) a leader's snapshot. -/
def netStepTypes : List w32 :=
  [MsgApp, MsgAppResp, MsgVote, MsgVoteResp, MsgHeartbeat, MsgHeartbeatResp,
   MsgReadIndex, MsgReadIndexResp, MsgTimeoutNow, MsgTransferLeader, MsgForgetLeader,
   MsgUnreachable, MsgSnapStatus,
   -- (2026-10-17) pre-vote
   MsgPreVote, MsgPreVoteResp,
   -- (2026-10-20, D22 S-c) a snapshot
   MsgSnap]

/-- (2026-10-13) The types of `netStepTypes` that come unstamped (`Term = 0`): a read-index
request (forwarded or local), `TransferLeadership`'s request, and the local reports. (raft-final,
2026-10-29, U7) A transfer request may also come stamped, forwarded by a follower to its leader
(`NetMsgOk`'s transfer clause). -/
def UnstampedType (t : w32) : Prop :=
  t = MsgReadIndex ∨ t = MsgTransferLeader ∨ t = MsgForgetLeader ∨ t = MsgUnreachable ∨
    t = MsgSnapStatus

/-- A message from the network, as the transport and the peers deliver it to node `id`
(see `RawNode__Step.lean`'s header): but for the unstamped types (`Term = 0`, 2026-10-13),
addressed to `id`, of a nonzero term, from a nonzero sender; a transfer request with no
entries and no context, unstamped or (raft-final, 2026-10-29, U7: the design's §2.5) stamped and
addressed to `id` (a follower's forward to its leader, `stepFollower`; `raft.Step` takes its witness,
`isRaftMsg`'s transfer clause). (2026-10-16, stage R5: on the message's state, the last clause over its
entries and context, `st.ents = [] ∧ st.ctx = []`; until then over the Goose value, `Entries' =
slice.nil ∧ Context' = slice.nil`.) (2026-10-20, D22 S-c) A `MsgSnap`, a leader's, from another
node, like its `MsgApp`. -/
def NetMsgOk (id : w64) (st : MsgSt) : Prop :=
  st.msg.Type' ∈ netStepTypes ∧
  (¬ UnstampedType st.msg.Type' → st.msg.To' = id ∧ st.msg.Term' ≠ W64 0 ∧ st.msg.From' ≠ W64 0) ∧
  (UnstampedType st.msg.Type' → st.msg.Type' ≠ MsgTransferLeader → st.msg.Term' = W64 0) ∧
  -- (raft-final, 2026-10-29, U7) a transfer request unstamped, or stamped to `id`
  (st.msg.Type' = MsgTransferLeader → st.msg.Term' = W64 0 ∨ st.msg.To' = id) ∧
  (st.msg.Type' = MsgApp ∨ st.msg.Type' = MsgHeartbeat ∨ st.msg.Type' = MsgHeartbeatResp ∨
     st.msg.Type' = MsgReadIndexResp ∨ st.msg.Type' = MsgSnap → st.msg.From' ≠ id) ∧
  (st.msg.Type' = MsgAppResp → st.msg.Reject' = true → st.msg.From' ≠ id) ∧
  (st.msg.Type' = MsgTransferLeader → st.ents = [] ∧ st.ctx = []) ∧
  -- (2026-10-17) a pre-vote request from another node
  (st.msg.Type' = MsgPreVote → st.msg.From' ≠ id) ∧
  -- (2026-10-22, D38a) no responses (what raft forwards must have none, `raft.Step`'s `Hnors`)
  st.resps = []

/-- (2026-10-22, D38a) A network message has no responses. -/
theorem NetMsgOk.resps {id : w64} {st : MsgSt} (h : NetMsgOk id st) : st.resps = [] := by
  unfold NetMsgOk at h; exact h.2.2.2.2.2.2.2.2

theorem SentMsgOk.ne_timeoutNow {st : MsgSt} (H : SentMsgOk st) :
    st.msg.Type' ≠ MsgTimeoutNow := by
  intro h; have := H.1; rw [h] at this
  simp [sentTypes, MsgSnap, MsgProp, MsgApp, MsgAppResp, MsgVote, MsgVoteResp, MsgHeartbeat,
    MsgHeartbeatResp, MsgReadIndex, MsgReadIndexResp, MsgPreVote, MsgPreVoteResp, MsgTimeoutNow,
    MsgTransferLeader] at this

theorem SentMsgOk.ne_transferLeader {st : MsgSt} (H : SentMsgOk st) :
    st.msg.Type' ≠ MsgTransferLeader := by
  intro h; have := H.1; rw [h] at this
  simp [sentTypes, MsgSnap, MsgProp, MsgApp, MsgAppResp, MsgVote, MsgVoteResp, MsgHeartbeat,
    MsgHeartbeatResp, MsgReadIndex, MsgReadIndexResp, MsgPreVote, MsgPreVoteResp, MsgTimeoutNow,
    MsgTransferLeader] at this

/-- (raft-final, 2026-10-29, U7: the design's §2.5) **`NetMsgOk` of a sent message at its
destination**: what `node.Step`'s `netP` takes of a message from the network, from the sender's
`SentMsgShape` (`sentMsg_shape`) and the transport's delivery to the node it is addressed to; but for
a forwarded proposal (`fwdP`). (Until then `NetMsgOk.of_sent`, from the no-transfer mode's
`SentMsgOk`, D21g (A).) -/
theorem NetMsgOk.of_shape {dst : w64} {st : MsgSt} (H : SentMsgShape st) (Hto : st.msg.To' = dst)
    (Hnp : st.msg.Type' ≠ MsgProp) : NetMsgOk dst st := by
  obtain ⟨Hty, Hf0, Ht0, Ht1, Hft, -, Hxe, Hrs⟩ := H
  subst Hto
  unfold NetMsgOk UnstampedType
  simp only [sentShapeTypes, sentTypes, List.mem_append, List.mem_cons, List.not_mem_nil,
    _root_.or_false] at Hty
  rcases Hty with (h | h | h | h | h | h | h | h | h | h | h | h) | h | h <;>
    rw [h] at Ht0 Ht1 Hft Hnp Hxe ⊢ <;>
    simp only [netStepTypes, MsgProp, MsgApp, MsgAppResp, MsgVote, MsgVoteResp, MsgHeartbeat,
      MsgHeartbeatResp, MsgReadIndex, MsgReadIndexResp, MsgPreVote, MsgPreVoteResp, MsgTimeoutNow,
      MsgTransferLeader, MsgForgetLeader, MsgUnreachable, MsgSnapStatus, MsgSnap]
      at Ht0 Ht1 Hft Hnp Hxe ⊢ <;>
    simp_all

end

end EtcdGrove
end Perennial
