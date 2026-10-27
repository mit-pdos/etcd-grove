/-
Lean-first (no Rocq counterpart).

# The cluster driver's predicates (2026-10-11)

`examples/kv/cluster.go`: `StartCluster` builds a cluster of three replicas of the store over
raft's `Node`, connected in process by `deliver`, each node driven by a `tick` goroutine;
`Main` (`check.go`) runs the randomized linearizability test on it (`ModelDefs.lean`).

* **The logger** (`qLogger`): the `quietLogger{}` the nodes' `Config`s carry. Its formatting
  methods return (`quietLogger.{Debugf,Errorf,Infof,Warningf}`), which is raft's
  `isLogger` (`qLogger_isLogger`).
* **The transport** (`deliverable`, `deliver`): `Ready` says of each of its messages only
  that it was legitimately sent (`isRaftMsg`) and of a term within the budget (`termLB`);
  `Node.Step` takes more (`stepP`: the type, the target, a nonzero term and sender but for a
  forwarded read-index request (unstamped), its entries owned, a `MsgReadIndex`'s read
  credit and (2026-10-13) a `MsgTimeoutNow`'s tick credit). The transport checks in Go what
  it can (`Deliverable`: the type, a sender other than the target, a term (none on a
  forwarded read-index request), a nil context but on a heartbeat, its response or a vote
  request, and (2026-10-13) no entries on a `MsgTimeoutNow`), routes by `To` (so the target
  is the receiver), copies the entries and passes each message's read credit on
  (2026-10-13); raft sends nothing it drops but a follower's forwarded transfer request
  (stamped, which `Node.Step` does not take). Since 2026-10-13 a vote request's context
  may be the leader-transfer marker (a transfer's campaign; `Node.Step` takes it).
  Raft v3.7 (2026-10-16, stage R6b): the messages are `*pb.Message`s a `Ready` hands out owned
  (D8, `readyDq`: whole, but a response at half), and `Node.Step` takes the pointer for good
  (Q3, `msgIn`): `Deliverable` is over the message's state `st : MsgSt`, `stepP_deliverable`
  takes the message at `1` with its entries slice fresh (`deliver`'s copy). A response
  (`MsgAppResp`, `MsgVoteResp`) comes at half, so the in-process transport cannot write its
  `Entries` nor hand it to `Step`: `deliver` steps the wire's copy of every message instead.
* **The transfer budget** (`isTransfers`, 2026-10-13): a `MsgTimeoutNow` makes its target
  campaign at once, one term past its own or the message's, so `Node.Step` takes it with a
  tick credit of the term budget (`netP`). The transport holds `timeouts` of them in a
  mutex-protected counter (`transfers`, `transfersInv`: one credit per count) and passes a
  `MsgTimeoutNow` on only while one is left (`transfers.take`), as `tick` bounds a node's
  ticks; `Main` allocates them with the budget.
* **The peers** (`kvPeerOk`): the node a peer table maps an id to is that id's, of the
  cluster's raft ghost state and term budget (persistent).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.Lemmas

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-- The store's `quietLogger` type. -/
abbrev qLoggerTy [GooseExts] [GoGlobalContext] : go.GoType :=
  github_com.mit_pdos.etcd_grove.examples.kv.quietLogger.ty

/-- `quietLogger{}`. -/
abbrev qLoggerV [GooseExts] : github_com.mit_pdos.etcd_grove.examples.kv.quietLogger :=
  github_com.mit_pdos.etcd_grove.examples.kv.quietLogger.mk

/-- `quietLogger{}` as a `raft.Logger`. -/
def qLogger [GooseExts] [GoGlobalContext] : GoInterfaceOk := interface.mk qLoggerTy #qLoggerV

/-- The message types `deliverable` delivers, of a term, besides the forwarded proposals and
read-index requests and (2026-10-13) `MsgTimeoutNow`: replication, leader election and the
read-index responses (`RawNode.Step`'s `netStepTypes` but `MsgReadIndex` and the leader
transfer and local types). -/
def kvNetTypes : List w32 :=
  [MsgApp, MsgAppResp, MsgVote, MsgVoteResp, MsgHeartbeat, MsgHeartbeatResp, MsgReadIndexResp]

/-- What `deliverable` checks of a message holding `st` (see the file header; raft v3.7, stage
R6b: over the message's state, `m.Entries != nil` and `m.Context == nil` read as its entries and
context bytes being empty, `msgPtsC_fields_acc`). -/
def Deliverable [GooseExts] (st : MsgSt) : Prop :=
  (st.msg.Type' = MsgProp ∨ (st.msg.Type' = MsgReadIndex ∧ st.msg.Term' = W64 0) ∨
    (st.msg.Type' ∈ kvNetTypes ∧ st.msg.Term' ≠ W64 0) ∨
    (st.msg.Type' = MsgTimeoutNow ∧ st.msg.Term' ≠ W64 0 ∧ st.ents = []) ∨
    -- (D22 S-r, 2026-10-21) a leader's snapshot, of an index below `maxIndex`
    (st.msg.Type' = MsgSnap ∧ st.msg.Term' ≠ W64 0 ∧
      ∃ sv, st.snap = some sv ∧ uint.Z sv.Metadata'.Index' < 2 ^ 61)) ∧
  st.msg.From' ≠ W64 0 ∧ st.msg.From' ≠ st.msg.To' ∧
  (st.ctx = [] ∨ st.msg.Type' = MsgHeartbeat ∨ st.msg.Type' = MsgHeartbeatResp ∨
    st.msg.Type' = MsgVote)

/-- A node's ticks (`ticks`). -/
def ticksN : Nat := 2 ^ 20

/-- The store's `transfers` struct. -/
abbrev RTransfers [GooseExts] := github_com.mit_pdos.etcd_grove.examples.kv.transfers

abbrev rTransfersTy [GooseExts] [GoGlobalContext] : go.GoType :=
  github_com.mit_pdos.etcd_grove.examples.kv.transfers.ty

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]
variable [StorageModel GF]

/-- The node `nd` is node `id` of the store's cluster `γ` (persistent). -/
def kvPeerOk (γ : Draft.Cluster) (id : w64) (nd : GoInterface) : IProp GF :=
  iprop(∃ (n : Loc), ⌜nd = interface.mkOk (go.GoType.PointerType node.ty) #n⌝ ∗
    Draft.isNode n γ kvRaftN id)

instance kvPeerOk_persistent (γ : Draft.Cluster) (id : w64) (nd : GoInterface) :
    Persistent (kvPeerOk (GF := GF) γ id nd) := by
  unfold kvPeerOk; infer_instance

/-- The transfer budget's lock invariant (see the file header): the number of `MsgTimeoutNow`s
the transport may still pass on (D19b, 2026-10-18: until then with one tick credit each; `take`
takes the credit, a time receipt, from a Go step of its own). -/
def transfersInv (_γ : Draft.Cluster) (tr : Loc) : IProp GF :=
  iprop(∃ n : w64, tr.[RTransfers, go!"left"] ↦ n)

/-- The transport's transfer budget `tr` (persistent). -/
def isTransfers (γ : Draft.Cluster) (tr : Loc) : IProp GF :=
  sync.isMutex (tr.[RTransfers, go!"mu"]) (transfersInv γ tr)

instance isTransfers_persistent (γ : Draft.Cluster) (tr : Loc) :
    Persistent (isTransfers (GF := GF) γ tr) := by
  unfold isTransfers; infer_instance

omit [StorageModel GF] in
/-- (D22 S-r) A message's `Snapshot` field, out of `msgPtsC` and back (`deliverable` compares it
to `nil`, `deliver` clones it). -/
theorem msgPtsC_snap_acc (l : Loc) (dq dqe : DFrac) (cap : Bool) (ms : MsgSt) :
    msgPtsC (GF := GF) l dq dqe cap ms ⊢
      ∃ ps, l.[raftpb.Message, go!"Snapshot"] ↦{dq} ps ∗ snapOpt ps dq ms.snap ∗
        (l.[raftpb.Message, go!"Snapshot"] ↦{dq} ps -∗ snapOpt ps dq ms.snap -∗
          msgPtsC l dq dqe cap ms) := by
  iintro H
  iNamed H
  iexists ps
  iframe HSn Hsn
  iintro HSn Hsn
  unfold msgPtsC
  iexists pty, pto, pfr, pte, plt, pix, pco, pvo, prj, prh, es, els, ps, cs, rs, uf
  simp only [named]
  isplitr; · ipureintro; exact Hnn
  iframe
  iframe #

/-- (2026-10-17) No pre-vote request is delivered (`kvNetTypes`). -/
theorem deliverable_not_prevote (st : MsgSt) (Hd : Deliverable st) : st.msg.Type' ≠ MsgPreVote := by
  obtain ⟨Hty, -⟩ := Hd
  rcases Hty with h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · rw [h]; simp [MsgProp, MsgPreVote]
  · rw [h]; simp [MsgReadIndex, MsgPreVote]
  · simp only [kvNetTypes, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h <;> rw [h] <;>
      simp [MsgPreVote, MsgApp, MsgAppResp, MsgVote, MsgVoteResp, MsgHeartbeat,
        MsgHeartbeatResp, MsgReadIndexResp]
  · rw [h]; simp [MsgTimeoutNow, MsgPreVote]
  · rw [h]; simp [MsgSnap, MsgPreVote]

/-- A deliverable message other than a proposal, addressed to `id`, is what `RawNode.Step`
takes from the network (`NetMsgOk`). -/
theorem deliverable_netMsgOk (id : w64) (st : MsgSt) (Hd : Deliverable st)
    (Hnp : st.msg.Type' ≠ MsgProp) (Hto : st.msg.To' = id) (Hr : st.resps = []) :
    NetMsgOk id st := by
  obtain ⟨Hty, HF, HFT, -⟩ := Hd
  have HF' : st.msg.From' ≠ id := Hto ▸ HFT
  have Hntl : st.msg.Type' ≠ MsgTransferLeader := by
    rcases Hty with h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact absurd h Hnp
    · rw [h]; simp [MsgReadIndex, MsgTransferLeader]
    · simp only [kvNetTypes, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h | h | h | h | h <;> rw [h] <;>
        simp [MsgTransferLeader, MsgApp, MsgAppResp, MsgVote, MsgVoteResp, MsgHeartbeat,
          MsgHeartbeatResp, MsgReadIndexResp]
    · rw [h]; simp [MsgTimeoutNow, MsgTransferLeader]
    · rw [h]; simp [MsgSnap, MsgTransferLeader]
  show st.msg.Type' ∈ netStepTypes ∧
    (¬ UnstampedType st.msg.Type' → st.msg.To' = id ∧ st.msg.Term' ≠ W64 0 ∧ st.msg.From' ≠ W64 0) ∧
    (UnstampedType st.msg.Type' → st.msg.Term' = W64 0) ∧
    (st.msg.Type' = MsgApp ∨ st.msg.Type' = MsgHeartbeat ∨ st.msg.Type' = MsgHeartbeatResp ∨
       st.msg.Type' = MsgReadIndexResp ∨ st.msg.Type' = MsgSnap → st.msg.From' ≠ id) ∧
    (st.msg.Type' = MsgAppResp → st.msg.Reject' = true → st.msg.From' ≠ id) ∧
    (st.msg.Type' = MsgTransferLeader → st.ents = [] ∧ st.ctx = []) ∧
    (st.msg.Type' = MsgPreVote → st.msg.From' ≠ id) ∧ st.resps = []
  rcases Hty with h | ⟨Hri, Ht0⟩ | ⟨Hn, Ht⟩ | ⟨Htn, Ht, -⟩ | ⟨Hsn, Ht, -⟩
  · exact absurd h Hnp
  · refine ⟨by rw [Hri]; simp [netStepTypes], fun h => absurd (.inl Hri) h, fun _ => Ht0,
      fun _ => HF', fun _ _ => HF', fun h => absurd h Hntl, fun _ => HF', Hr⟩
  · have Hun : ¬ UnstampedType st.msg.Type' := by
      simp only [kvNetTypes, List.mem_cons, List.not_mem_nil, or_false] at Hn
      rcases Hn with h | h | h | h | h | h | h <;> rw [h] <;>
        simp [UnstampedType, MsgApp, MsgAppResp, MsgVote, MsgVoteResp, MsgHeartbeat,
          MsgHeartbeatResp, MsgReadIndexResp, MsgReadIndex, MsgTransferLeader, MsgForgetLeader,
          MsgUnreachable, MsgSnapStatus]
    have Hnet : st.msg.Type' ∈ netStepTypes := by
      simp only [kvNetTypes, List.mem_cons, List.not_mem_nil, or_false] at Hn
      simp only [netStepTypes, List.mem_cons, List.not_mem_nil, or_false]
      rcases Hn with h | h | h | h | h | h | h <;> simp [h]
    exact ⟨Hnet, fun _ => ⟨Hto, Ht, HF⟩, fun h => absurd h Hun, fun _ => HF', fun _ _ => HF',
      fun h => absurd h Hntl, fun _ => HF', Hr⟩
  · have Hun : ¬ UnstampedType st.msg.Type' := by
      rw [Htn]
      simp [UnstampedType, MsgTimeoutNow, MsgReadIndex, MsgTransferLeader, MsgForgetLeader,
        MsgUnreachable, MsgSnapStatus]
    exact ⟨by rw [Htn]; simp [netStepTypes], fun _ => ⟨Hto, Ht, HF⟩, fun h => absurd h Hun,
      fun _ => HF', fun _ _ => HF', fun h => absurd h Hntl, fun _ => HF', Hr⟩
  · have Hun : ¬ UnstampedType st.msg.Type' := by
      rw [Hsn]
      simp [UnstampedType, MsgSnap, MsgReadIndex, MsgTransferLeader, MsgForgetLeader,
        MsgUnreachable, MsgSnapStatus]
    exact ⟨by rw [Hsn]; simp [netStepTypes], fun _ => ⟨Hto, Ht, HF⟩, fun h => absurd h Hun,
      fun _ => HF', fun _ _ => HF', fun h => absurd h Hntl, fun _ => HF', Hr⟩

/-- A deliverable message, addressed to `id`, as `Draft.stepIn_intro` asks of a message a node
steps: a forwarded proposal with no context, or what a node takes from the network (`NetMsgOk`, of
its copy with no responses; no pre-vote, no leader transfer), a snapshot below `2^61`. -/
theorem deliverable_step (id : w64) (st : MsgSt) (Hd : Deliverable st) (Hto : st.msg.To' = id) :
    (st.msg.Type' = MsgProp → st.ctx = []) ∧
    (st.msg.Type' ≠ MsgProp → NetMsgOk id ⟨st.msg, st.ents, st.snap, st.ctx, []⟩ ∧
      st.msg.Type' ≠ MsgPreVote ∧ st.msg.Type' ≠ MsgTransferLeader) ∧
    (st.msg.Type' = MsgSnap → ∃ sv, st.snap = some sv ∧ uint.Z sv.Metadata'.Index' < 2 ^ 61) := by
  refine ⟨fun Hp => ?_, fun Hnp => ⟨deliverable_netMsgOk id ⟨st.msg, st.ents, st.snap, st.ctx, []⟩
    Hd Hnp Hto rfl, deliverable_not_prevote st Hd, ?_⟩, fun Hsn => ?_⟩
  · rcases Hd.2.2.2 with h | h | h | h
    · exact h
    all_goals (rw [Hp] at h; simp [MsgProp, MsgHeartbeat, MsgHeartbeatResp, MsgVote] at h)
  · obtain ⟨Hty, -⟩ := Hd
    rcases Hty with h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact absurd h Hnp
    · rw [h]; simp [MsgReadIndex, MsgTransferLeader]
    · simp only [kvNetTypes, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h | h | h | h | h <;> rw [h] <;>
        simp [MsgTransferLeader, MsgApp, MsgAppResp, MsgVote, MsgVoteResp, MsgHeartbeat,
          MsgHeartbeatResp, MsgReadIndexResp]
    · rw [h]; simp [MsgTimeoutNow, MsgTransferLeader]
    · rw [h]; simp [MsgSnap, MsgTransferLeader]
  · obtain ⟨Hty0, -⟩ := Hd
    rcases Hty0 with h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, sv', Hs', Hi'⟩
    · rw [Hsn] at h; revert h; simp [MsgSnap, MsgProp]
    · rw [Hsn] at h; revert h; simp [MsgSnap, MsgReadIndex]
    · unfold kvNetTypes at h; rw [Hsn] at h; revert h
      simp [MsgSnap, MsgApp, MsgAppResp, MsgVote, MsgVoteResp, MsgHeartbeat, MsgHeartbeatResp,
        MsgReadIndexResp]
    · rw [Hsn] at h; revert h; simp [MsgSnap, MsgTimeoutNow]
    · exact ⟨sv', Hs', Hi'⟩

end defs


end EtcdGrove
end Perennial
