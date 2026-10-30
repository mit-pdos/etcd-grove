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
  that it was sent (`sentMsg`), with its credits (`msgCredits`); `Node.Step` takes it with its
  wire state and its credits, routed to its target (`stepIn`, `stepIn_intro`: since 2026-10-30,
  stage F of the client repair, no premise on the type, the term, the transfer, a snapshot or a
  tick credit). The transport still checks in Go what it did (`Deliverable`: the type, a sender
  other than the target, a term (none on a forwarded read-index request), a nil context but on a
  heartbeat, its response or a vote request, no entries on a `MsgTimeoutNow`), routes by `To` (so
  the target is the receiver), copies the entries and passes each message's credits on. Raft
  v3.7 (2026-10-16, stage R6b): the messages are `*pb.Message`s a `Ready` hands out owned (D8,
  `readyDq`: whole, but a response at half), and `Node.Step` takes the pointer for good (Q3,
  `msgIn`). A response (`MsgAppResp`, `MsgVoteResp`) comes at half, so the in-process transport
  cannot write its `Entries` nor hand it to `Step`: `deliver` steps the wire's copy of every
  message instead. (Until 2026-10-30 `Deliverable` was what `NetMsgOk` asked,
  `deliverable_netMsgOk`, `deliverable_step`.)
* **The transfer budget** (`isTransfers`, 2026-10-13): the transport holds `timeouts`
  `MsgTimeoutNow`s in a mutex-protected counter (`transfers`) and passes one on only while one is
  left (`transfers.take`). Since 2026-10-30 nothing rides on it (until then a tick credit each,
  what `Node.Step` took with a `MsgTimeoutNow`).
* **The peers** (`kvPeerOk`): the node a peer table maps an id to is that id's, of the
  cluster (persistent).
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
def kvPeerOk (γ : Cluster) (id : w64) (nd : GoInterface) : IProp GF :=
  iprop(∃ (n : Loc), ⌜nd = interface.mkOk (go.GoType.PointerType node.ty) #n⌝ ∗
    isNode n γ kvRaftN id)

instance kvPeerOk_persistent (γ : Cluster) (id : w64) (nd : GoInterface) :
    Persistent (kvPeerOk (GF := GF) γ id nd) := by
  unfold kvPeerOk; infer_instance

/-- The transfer budget's lock invariant (see the file header): the number of `MsgTimeoutNow`s
the transport may still pass on (D19b, 2026-10-18: until then with one tick credit each; `take`
takes the credit, a time receipt, from a Go step of its own). -/
def transfersInv (_γ : Cluster) (tr : Loc) : IProp GF :=
  iprop(∃ n : w64, tr.[RTransfers, go!"left"] ↦ n)

/-- The transport's transfer budget `tr` (persistent). -/
def isTransfers (γ : Cluster) (tr : Loc) : IProp GF :=
  sync.isMutex (tr.[RTransfers, go!"mu"]) (transfersInv γ tr)

instance isTransfers_persistent (γ : Cluster) (tr : Loc) :
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

end defs


end EtcdGrove
end Perennial
