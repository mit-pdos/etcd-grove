/-
Lean-first (no Rocq counterpart). Q9 of `notes/trace-validation-plan.md` (2026-11-09): the name
`MessageType.String` gives a traced message's type (`raftpb.msgTypeString`, its exact spec's result,
`Spec/go_etcd_io/raft/v3/raftpb/MessageType__String.lean`) is the trace vocabulary's `msgTypeStr`
(`TracedCap.lean`), for the six types the send and receive hooks trace (`sendEvt`, `recvEvt`):
what `makeTracingMessage`'s `m.GetType().String()` writes in a traced event's message (`MsgEvOf`).
-/
module

public import Proof.go_etcd_io.raft.v3.TracedCap
public import Proof.go_etcd_io.raft.v3.raftpb.MsgTypeName

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- **The traced types' names**: a message of type `t` (abstracted as `ty`) that the send hook
traces (`sendEvt ty ≠ none`: `MsgApp`, `MsgAppResp`, `MsgVote`, `MsgVoteResp`, `MsgHeartbeat`,
`MsgHeartbeatResp`) has `t.String() = msgTypeStr ty`. -/
theorem msgTypeString_traced (t : w32) (ty : MsgType) (h : mtypeOf t = some ty)
    (hs : sendEvt ty ≠ none) : raftpb.msgTypeString t = msgTypeStr ty := by
  unfold mtypeOf at h
  split at h <;> rename_i hz <;> cases h <;> simp only [sendEvt, ne_eq, not_true_eq_false] at hs <;>
    first
    | (rw [show t = W32 3 from uint_Z_inj.1 (by rw [hz]; rfl)]; exact raftpb.msgTypeString_MsgApp)
    | (rw [show t = W32 4 from uint_Z_inj.1 (by rw [hz]; rfl)]; exact raftpb.msgTypeString_MsgAppResp)
    | (rw [show t = W32 5 from uint_Z_inj.1 (by rw [hz]; rfl)]; exact raftpb.msgTypeString_MsgVote)
    | (rw [show t = W32 6 from uint_Z_inj.1 (by rw [hz]; rfl)]; exact raftpb.msgTypeString_MsgVoteResp)
    | (rw [show t = W32 8 from uint_Z_inj.1 (by rw [hz]; rfl)]; exact raftpb.msgTypeString_MsgHeartbeat)
    | (rw [show t = W32 9 from uint_Z_inj.1 (by rw [hz]; rfl)]
       exact raftpb.msgTypeString_MsgHeartbeatResp)

/-- The same, for the receive hook's types (`recvEvt ty ≠ none`: the same six). -/
theorem msgTypeString_traced_recv (t : w32) (ty : MsgType) (h : mtypeOf t = some ty)
    (hs : recvEvt ty ≠ none) : raftpb.msgTypeString t = msgTypeStr ty := by
  refine msgTypeString_traced t ty h ?_
  cases ty <;> simp_all [sendEvt, recvEvt]

end pure

end EtcdGrove
end Perennial
