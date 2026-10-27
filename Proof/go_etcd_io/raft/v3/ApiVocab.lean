/-
The vocabulary of raft's node API (2026-10-26, raft's signature, stage 1;
`notes/decisions.md`, "Package signatures"): the records and predicates the public node specs
(`Spec/go_etcd_io/raft/v3/Api.lean`) and their laws are stated in, moved here from the modules the
signature seals (`InvRaftPhys`, `InvRawnode`, `InvRawnodeReady`, `InvBoot`) and from the
`RawNode`-level specs (`NewRawNode`, `newRaft`, `Config.validate`, `RawNode.ProposeConfChange`),
so that a client can name them without reaching raft's internals (`etc/api-check.py
etc/api/raft.txt`). Nothing here mentions the raft struct or `NState`: it is what a client of
`node` sends, receives and proves, and the `RawNode`'s client-facing state (`RNState`, which
`InvNode`'s run-loop protocol is stated over). Transparent for now; a later stage seals what
clients need not see inside (`RNState.steps : List Pending` and `readyDq`'s fractions are
internals in the open: `notes/raft-spec-review.md`, "Modularity review").
-/
module

public import Proof.go_etcd_io.raft.v3.CCApply
public import Proof.go_etcd_io.raft.v3.InvConfChangeMsg
public import Proof.go_etcd_io.raft.v3.InvLogger
public import Proof.go_etcd_io.raft.v3.InvMisc
public import Proof.go_etcd_io.raft.v3.InvRaftlog
public import Proof.go_etcd_io.raft.v3.InvReadylog
public import Proof.go_etcd_io.raft.v3.InvTrackerC
public import Proof.go_etcd_io.raft.v3.InvPbSnapSet
public import Proof.go_etcd_io.raft.v3.SnapConf
public import Proof.go_etcd_io.raft.v3.StepGhostMode
public import Proof.go_etcd_io.raft.v3.Protocol.CommitWit
public import Proof.go_etcd_io.raft.v3.Protocol.Facts
public import Proof.go_etcd_io.raft.v3.Protocol.Refinement
public import Proof.go_etcd_io.raft.v3.Protocol.ResultsDyn
public import Spec.google_golang_org.protobuf.proto.MarshalConfChange

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI OFE CMRA Iris.ProofMode go_etcd_io.raft.v3

-- from Proof/go_etcd_io/raft/v3/InvRaftPhys.lean
section
open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A queued message: its pointer and the state it holds (stage R4). -/
structure QMsg [GooseExts] where
  loc : Loc
  st : MsgSt

/-- What a queued message holding `st` contributes to the abstract outbox (see above; stage R4:
pure, over the message's state). -/
def msgAbs (st : MsgSt) (a : Option Msg) : Prop :=
  (mtypeOf st.msg.Type' = none ∧ a = none) ∨
  (∃ ty, mtypeOf st.msg.Type' = some ty ∧ ty ≠ .snap ∧
    a = some (absMsg ty st.msg st.ents st.ctx)) ∨
  (∃ sv : SnapshotM, mtypeOf st.msg.Type' = some .snap ∧ st.snap = some sv ∧
    a = some (absSnap st.msg sv sv.Metadata'.ConfState'.lists))

/-- (2026-10-19, D21 M2r) The types a node in the no-transfer mode sends (`SentMsgOk`; from D22 S-a
to S-c: in both the no-snapshot and the no-transfer modes): replication, election, pre-vote,
read-index, a forwarded proposal, and (2026-10-20, D22 S-c) a leader's `MsgSnap`; no
`MsgTimeoutNow` and no `MsgTransferLeader` (leader transfer off, `NGhost.xf`). -/
def sentTypes : List w32 :=
  [MsgProp, MsgApp, MsgAppResp, MsgVote, MsgVoteResp, MsgHeartbeat, MsgHeartbeatResp,
   MsgReadIndex, MsgReadIndexResp, MsgPreVote, MsgPreVoteResp, MsgSnap]

/-- (2026-10-22, D38a) **The shape of a `MsgApp` raft sends**: no vote, not a rejection, no
hint, no snapshot, no context, no responses -- the fields the msgappv2 codec's short frame does not
carry (its decoder sets them to their defaults). Raft's one `MsgApp` (`maybeSendAppend`) sets only
`To`, `Type`, `Index`, `LogTerm`, `Entries`, `Commit` (and `send`, `From` and `Term`). -/
def AppShape (st : MsgSt) : Prop :=
  st.msg.Vote' = W64 0 ∧ st.msg.Reject' = false ∧ st.msg.RejectHint' = W64 0 ∧
  st.snap = none ∧ st.ctx = [] ∧ st.resps = []

/-- (2026-10-19, D21 M2r, D21g (A)) **What a sender in the no-transfer mode promises of a message
it queues** (from D22 S-a to S-c: in both modes), beyond its protocol abstraction (`isRaftMsg`
carries it to the receiver): a type of
`sentTypes`, a nonzero sender, unstamped (`Term = 0`) exactly when a forwarded proposal or
read-index request, and from a node other than its destination unless it is a read-index request
(forwarded, it keeps its requester), a vote or pre-vote response, or an accepting `MsgAppResp`
(the self-addressed responses `acceptReady` steps). What a receiver's `NetMsgOk` needs of a
message addressed to it (`NetMsgOk.of_sent`, `InvRawnode.lean`). (2026-10-22, D38a) And a `MsgApp`
of raft's shape (`AppShape`), what rafthttp's msgappv2 codec needs to carry it whole; and no
message with responses (raft sets them only on its local storage messages), what both of rafthttp's
codecs need to marshal it (`MsgMarshals`). -/
def SentMsgOk (st : MsgSt) : Prop :=
  st.msg.Type' ∈ sentTypes ∧ st.msg.From' ≠ W64 0 ∧
  (st.msg.Type' = MsgProp ∨ st.msg.Type' = MsgReadIndex → st.msg.Term' = W64 0) ∧
  (¬ (st.msg.Type' = MsgProp ∨ st.msg.Type' = MsgReadIndex) → st.msg.Term' ≠ W64 0) ∧
  (st.msg.Type' ≠ MsgReadIndex → st.msg.Type' ≠ MsgVoteResp → st.msg.Type' ≠ MsgPreVoteResp →
     (st.msg.Type' = MsgAppResp → st.msg.Reject' = true) → st.msg.From' ≠ st.msg.To') ∧
  (st.msg.Type' = MsgApp → AppShape st) ∧
  st.resps = []

/-- (2026-10-22, D38a) `SentMsgOk` carries over to a message with the same scalars and no
responses, if it is not a `MsgApp` (whose shape reads the rest): e.g. a `MsgSnap` with its
snapshot replaced. -/
theorem SentMsgOk.of_msg {st st' : MsgSt} (H : SentMsgOk st) (hm : st'.msg = st.msg)
    (hr : st'.resps = []) (hna : st.msg.Type' ≠ MsgApp) : SentMsgOk st' := by
  obtain ⟨a, b, c, d, e, -, -⟩ := H
  unfold SentMsgOk; rw [hm]
  exact ⟨a, b, c, d, e, fun h => absurd h hna, hr⟩

/-- (2026-10-22, D38a) **A `MsgApp` is from its sender** `id`: `send` stamps `From = r.id` into every
message but a forwarded read-index or transfer request, and raft's one `MsgApp` (`maybeSendAppend`)
is the node's own. What rafthttp's msgappv2 codec needs: its frames carry no sender, the decoder
sets the stream's remote peer (`XfOk`, `isRaftMsg`). -/
def AppFrom (id : w64) (st : MsgSt) : Prop := st.msg.Type' = MsgApp → st.msg.From' = id

/-- (D21 M3) The no-snapshot mode's cap of the storage (`ownRaftPhys`'s `Hnscap`, at the mode `ns`
and the log's storage `st`): the storage is never compacted past index `1`. -/
def NsCap (ns : Bool) (st : Storage) : IProp GF :=
  iprop(□ (⌜ns = true⌝ -∗ storCap st 1))

instance NsCap_persistent (ns : Bool) (st : Storage) : Persistent (NsCap (GF := GF) ns st) := by
  unfold NsCap; infer_instance

end

-- from Proof/go_etcd_io/raft/v3/InvRawnode.lean
section
open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-- A local message `acceptReady` queued for `Advance` to step:

- `self pv t`: a self-addressed response from `msgsAfterAppend` (a candidate's own vote,
  a pre-candidate's own pre-vote -- `pv` -- or a leader's own `MsgAppResp`) of term `t`
  (2026-10-10; until then `self a`, with the message's abstraction `a`);
- `appendAck t b last sn`: `MsgStorageAppendResp` at term `t` acknowledging the log up to
  `last` (queued when there were unstable entries; D22 S-d3a, 2026-10-21: `none`, with `Index`
  `0`, when there were none) and the snapshot `sn` the `Ready` handed out (D22 S-d3a: queued for a
  snapshot too, `needStorageAppendRespMsg`); (D22 S-d3b, 2026-10-21) `b` is the log's boundary at
  the `Ready`, which what the storage will hold follows (`LogState.stored`) -- a restore between
  the `Ready` and the `Advance` moves the boundary, not `stored`;
- `applyAck ents`: `MsgStorageApplyResp` carrying the committed entries handed out for
  applying. -/
inductive Pending [GooseExts] where
  | self (pv : Bool) (t : w64)
  | appendAck (term : w64) (base : entryID) (last : Option entryID) (sn : Option SnapshotM)
  | applyAck (ents : List EntryM)

/-- The mode of a `RawNode`'s ghost state (2026-10-14, reconfiguration stage B7 part 2): static
(the voters fixed at `γ.reCfg`, conf-change entries data) or dynamic (the configuration changes
by applied conf entries: a decoder `dec` and an initial configuration `c0`; B5's
`ownRaftGhostR`). -/
inductive RNMode [GooseExts] where
  | static
  | dyn (dec : CCDec) (c0 : CCState) (h0 : CfgOk c0) (h1 : CCGood c0)

/-- (D22 S-d3a, 2026-10-21) **A snapshot `Ready`'s loan**: the `Ready` handed out the snapshot `snap`
at `ptr` (`rd.Snapshot`, half of it: the queued acknowledgement shares the pointer,
`newStorageAppendRespMsg`) and the node's storage itself (`ownRaftLog_lend`, at the floor `fl`), and
the committed log up to the snapshot (`dlv`, `isCommitted`); the application gives both back with
`Advance` (`snapReceipt`), which steps the acknowledgement and hands the committed log over
(`RNState.delivered := dlv`). -/
structure SnapLoan [GooseExts] where
  ptr : Loc
  snap : SnapshotM
  fl : w64
  dlv : List EntryM

/-- What the application sees of a `RawNode` (2026-10-09). -/
structure RNState [GooseExts] where
  /-- The committed log handed out so far, from the start (as `isCommitted` takes it):
  every `Ready`'s `CommittedEntries`, in order, after the entries applied before the
  node was built. -/
  delivered : List EntryM
  /-- The entries `Ready` handed out (`Ready.Entries`) that the application must still
  append to the `Storage` (and give the receipt back: `ownRawNode_appended`). -/
  unpersisted : List EntryM
  /-- `rn.stepsOnAdvance`: what `Advance` will step. Opaque to clients, which only
  learn that it is empty (after `Advance`), as `Ready` requires. (Until 2026-10-10 a
  flag `advanceable` said whether `Advance` was proved for it: not for a queue with a
  self-addressed response, which no client could rule out.) -/
  steps : List Pending
  /-- The node's current term (2026-10-09). A client sees it (`Status`, `Ready`'s
  `HardState`); the specs need it because Go panics when a campaign wraps it
  (`Campaign`, `Tick`, `Advance`), and say how a step moves it. -/
  term : w64
  /-- The `Storage` the node reads (`Config.Storage`), constant (2026-10-10): the right
  to append `Ready` hands out (`appendRight`) and the receipt `ownRawNode_appended` takes
  back are for this storage. -/
  storage : Storage
  /-- Lower bounds for `node.go` (2026-10-10): at most this many messages are queued
  (`NGhost.outlb`), ... -/
  outlb : Nat := 0
  /-- ... some unstable entry is still to be handed out (`NGhost.unst`), ... -/
  unst : Bool := false
  /-- ... and the commit index is at least this. A step keeps all three; `acceptReady`
  resets the first two. `node.go`'s `run` raises them when it abandons a computed `Ready`
  (`ownRawNodeReady_abandon`), so that, should `HasReady` later report nothing new, the
  abandoned `Ready` is known to hold nothing (`ownRawNodeIdle`). -/
  clb : w64 := W64 0
  /-- (2026-10-17, pre-vote on) the term ceiling (`NGhost.tc`): every message the node queues,
  and its term, are at most this. The node's budget covers it (`termLB`); the client raises it
  (`ownRawNode_raise_tc`) before a step that may send at a later term. -/
  tc : w64 := W64 0
  /-- The ghost state's mode (2026-10-14, reconfiguration stage B7 part 2), constant. -/
  mode : RNMode := .static
  /-- In the dynamic mode, the configuration in use (with the learner flags; `confchange`'s
  state) and its *configuration index*: the configuration is that of the committed log's
  first `capplied` entries -- every conf entry below has been applied with `ApplyConfChange`.
  Only `ApplyConfChange` (to the entry it applies, plus one) and `Advance` (to at most the
  committed log handed out, `delivered`, past no conf entry: A1) move them. Unconstrained in
  the static mode. -/
  cfg : CCState := ⟨CfgM.simple ∅ ∅, ∅⟩
  capplied : Nat := 0
  /-- (D19i part 1) The floor is raised past `applied` (`ownRawNode_raise_floor`): `node.go`
  raises it to `applying` when the application's `Advance` is handed over, and `Advance`, which
  follows at once, moves `applied` up to it and clears the flag. While it is set the node is not
  to campaign (`Campaign`, `Tick`, `Step` take it clear: `hasUnappliedConfChanges` reads from
  `applied + 1`). -/
  flw : Bool := false
  /-- (2026-10-20, D22 S-c) A snapshot may be pending: a `MsgSnap` was stepped (`RawNode.Step`),
  whose restore leaves the snapshot in the log (`unstable.snapshot`, `LogState.snap`) for a later
  `Ready` to hand out. Only `RawNode.Step` sets it; (D22 S-d3a, 2026-10-21) the next `Ready` clears
  it (`acceptReady`: it hands the snapshot out, `slent`). So: "a `MsgSnap` stepped since the last
  `Ready`" (a stale one sets it too). (Until S-d3a, `HasReady`, `readyWithoutAccept`, `Ready`,
  `Advance` and the floor's raise took it `false`, and nothing cleared it; S-d3a to S-d3b it gated
  the records of what the storage will hold, now `ackInv`'s.) -/
  psnap : Bool := false
  /-- (D22 S-d3a, 2026-10-21) The loan of the last `Ready`, if it handed out a snapshot
  (`SnapLoan`): from `acceptReady` to the `Advance` that takes the application's receipt back. -/
  slent : Option SnapLoan := none
  /-- (D22l, 2026-10-20) `prevHardSt`'s record: the hard state of the last accepted `Ready` that
  had a non-empty one (`phsNext`), the zero record until then (`NewRawNode` on an empty storage,
  whose `hardState()` is zero). Only `acceptReady` moves it. A `Ready` with a `nil` `HardState`
  is one at which the node's hard state is this one, so its witness (`readyWithoutAccept`'s
  `hsWit` of `phsNext rs.phs h`) is this one's: what `node.go`'s driver needs to read every
  batch's commit witness off the hard state it last recorded. -/
  phs : HardStateM := HardStateM.mk (W64 0) (W64 0) (W64 0)

end

section
open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3
variable [GooseExts]

def RNMode.isDyn : RNMode → Bool
  | .static => false
  | .dyn .. => true

/-- The entry `Propose` builds, `&pb.Entry{Data: data}`, as the model reads it (2026-10-16,
stage R5; D6: the data is its bytes; until then `propEntry data_sl`, the Goose value). -/
def propEntryM (d : List w8) : EntryM := ⟨W64 0, W64 0, W32 0, d⟩

/-- No conf entry in a range of a prefix is none in the longer log. -/
theorem NoConfIn_prefix {D F : List EntryM} {lo hi : Nat} (hp : D <+: F)
    (hhi : hi ≤ D.length) (h : NoConfIn D lo hi) : NoConfIn F lo hi := by
  intro k e hk1 hk2 he
  apply h k e hk1 hk2
  obtain ⟨t, rfl⟩ := hp
  rw [List.getElem?_append_left (by omega)] at he
  exact he

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
request (forwarded or local), `TransferLeadership`'s request, and the local reports. -/
def UnstampedType (t : w32) : Prop :=
  t = MsgReadIndex ∨ t = MsgTransferLeader ∨ t = MsgForgetLeader ∨ t = MsgUnreachable ∨
    t = MsgSnapStatus

/-- A message from the network, as the transport and the peers deliver it to node `id`
(see `RawNode__Step.lean`'s header): but for the unstamped types (`Term = 0`, 2026-10-13),
addressed to `id`, of a nonzero term, from a nonzero sender; a transfer request with no
entries and no context. (2026-10-16, stage R5: on the message's state, the last clause over its
entries and context, `st.ents = [] ∧ st.ctx = []`; until then over the Goose value, `Entries' =
slice.nil ∧ Context' = slice.nil`.) (2026-10-20, D22 S-c) A `MsgSnap`, a leader's, from another
node, like its `MsgApp`. -/
def NetMsgOk (id : w64) (st : MsgSt) : Prop :=
  st.msg.Type' ∈ netStepTypes ∧
  (¬ UnstampedType st.msg.Type' → st.msg.To' = id ∧ st.msg.Term' ≠ W64 0 ∧ st.msg.From' ≠ W64 0) ∧
  (UnstampedType st.msg.Type' → st.msg.Term' = W64 0) ∧
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
  unfold NetMsgOk at h; exact h.2.2.2.2.2.2.2

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

/-- **`NetMsgOk` of a sent message at its destination** (D21g (A)): what `node.Step`'s `netP`
takes of a message from the network, from the sender's `SentMsgOk` and the transport's delivery to
the node it is addressed to; but for a forwarded proposal (`fwdP`). -/
theorem NetMsgOk.of_sent {dst : w64} {st : MsgSt} (H : SentMsgOk st) (Hto : st.msg.To' = dst)
    (Hnp : st.msg.Type' ≠ MsgProp) : NetMsgOk dst st := by
  obtain ⟨Hty, Hf0, Ht0, Ht1, Hft, -, Hrs⟩ := H
  subst Hto
  unfold NetMsgOk UnstampedType
  simp only [sentTypes, List.mem_cons, List.not_mem_nil, _root_.or_false] at Hty
  rcases Hty with h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] at Ht0 Ht1 Hft Hnp ⊢ <;>
    simp only [netStepTypes, MsgProp, MsgApp, MsgAppResp, MsgVote, MsgVoteResp, MsgHeartbeat,
      MsgHeartbeatResp, MsgReadIndex, MsgReadIndexResp, MsgPreVote, MsgPreVoteResp, MsgTimeoutNow,
      MsgTransferLeader, MsgForgetLeader, MsgUnreachable, MsgSnapStatus, MsgSnap] at Ht0 Ht1 Hft Hnp ⊢ <;>
    simp_all

/-- `DynCCPre` (below) on its components (2026-10-15, stage N): the committed log handed out
`D`, the configuration index `ca` and configuration `cfg`, and the change as `AsV2` makes it
(`op`); what `node.go`'s `confc` arm checks against the run loop's `RawNode` from what the
driver knows. (D43 M3, 2026-10-25) The change `op` applied need not be the decoder's `op'`, only
have its effect on `cfg` (`ccStepB`): the ghost step folds `op'`, the code applies `op`, both
giving `cs'` (etcd hands raft a failed validation's change with `NodeId` `0`, a no-op, in place
of the entry's `AddNode` of a member, also a no-op). -/
def DynCCPreOp (dec : CCDec) (D : List EntryM) (ca : Nat) (cfg : CCState) (op : CCOp)
    (k : Nat) (e : EntryM) (cs' : CCState) : Prop :=
  ca ≤ k ∧ k < D.length ∧ D[k]? = some e ∧ IsConfEnt e ∧
  NoConfIn D ca k ∧ (∃ op', dec (D.take k) e = some op' ∧ ccStepB op' cfg = some cs') ∧
  ccStepB op cfg = some cs' ∧ cs'.cfg.autoLeave = false

end

section
open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- (2026-10-21, D22 S-r) **A `MsgSnap`'s data certificate**: the snapshot it carries has the data
the cluster admits at its index (`snapDataOk`). Vacuous for every other message. What a `Ready`
says of the messages it hands out (`isRaftMsg`), and what `node.Step` takes of one from the
network (`netP`). -/
def msgDat (γ : RaftNames) (st : MsgSt) : IProp GF :=
  iprop(□ (∀ sv : SnapshotM, ⌜st.msg.Type' = MsgSnap ∧ st.snap = some sv⌝ -∗
    snapDataOk γ sv.Metadata'.Index' sv.Data'))

instance msgDat_pers (γ : RaftNames) (st : MsgSt) : Persistent (msgDat (GF := GF) γ st) := by
  unfold msgDat; infer_instance

/-- A message `Ready` hands to the application to send: what it contributes to the
protocol's messages (`msgAbs`: nothing, for a type the protocol does not describe) was
legitimately sent (`isMessage`). (2026-10-16, stage R5: on the message's state; `msgAbs` is
pure.) (2026-10-19, D21 M3) In the cluster's no-snapshot mode no `MsgSnap`; (D21 M2r, D21g (A))
and what the receiver's `NetMsgOk` needs of it (`SentMsgOk`, `NetMsgOk.of_sent`): its type, a
nonzero sender other than its destination, its term stamped (no `MsgTimeoutNow`, no
`MsgTransferLeader`: leader transfer is off). (2026-10-19, D22 S-a) The latter in the no-transfer
mode (`RaftNames.reNoXfer`) and the no-snapshot one, which until then were one; (2026-10-20, D22
S-c) in the no-transfer mode alone: its types exclude the transfer messages (admitting a leader's
`MsgSnap`), and its stamped terms are past `0`, which the mode's bootstrap log gives
(`NGhost.bt`, `XfOk`; until S-c the no-snapshot mode's). (2026-10-20, D22 S-b′3) Certified
(`isMessageC`): a `MsgSnap` carries its snapshot's configuration certificate (`raftSnapCert`),
which the `Ready` took from the storage's registry (`qSrc`, `certLink`). (2026-10-21, D22 S-r)
And its snapshot's data certificate (`msgDat`), from the same registry. (2026-10-22, D38a) In every
mode, no responses, and a `MsgApp` from the node `id` that sent it (`AppFrom`; `XfOk`), so that a
transport can marshal it (`MsgMarshals`) and the msgappv2 codec carry it. -/
def isRaftMsg (γ : RaftNames) (id : w64) (st : MsgSt) : IProp GF :=
  iprop(⌜γ.reNoSnap = true → st.msg.Type' ≠ MsgSnap⌝ ∗
    ⌜γ.reNoXfer = true → SentMsgOk st⌝ ∗
    (∃ a, ⌜msgAbs st a⌝ ∗ [∗list] x ∈ a.toList, isMessageC γ x) ∗
    msgDat γ st ∗ ⌜st.resps = [] ∧ AppFrom id st⌝)

instance isRaftMsg_pers (γ : RaftNames) (id : w64) (st : MsgSt) :
    Persistent (isRaftMsg (GF := GF) γ id st) := by
  unfold isRaftMsg; infer_instance

/-- (D22 S-r) A message's data certificate, out of `isRaftMsg`. -/
theorem isRaftMsg_dat (γ : RaftNames) (id : w64) (st : MsgSt) :
    isRaftMsg (GF := GF) γ id st ⊢ msgDat γ st := by
  unfold isRaftMsg
  iintro ⟨-, -, -, #H, -⟩
  iexact H

end

-- from Proof/go_etcd_io/raft/v3/InvRawnodeReady.lean
section
open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3
variable [GooseExts]

/-- A response type: what `send` queues in `msgsAfterAppend` (`AAMsgOk`). -/
def RespType (t : w32) : Prop := t = MsgAppResp ∨ t = MsgVoteResp ∨ t = MsgPreVoteResp

instance (t : w32) : Decidable (RespType t) := by unfold RespType; infer_instance

/-- The fraction at which a `Ready` hands a message out (see the file header): half of a
response (`acceptReady` reads the other half's `To`), the whole of any other. -/
def readyDq (st : MsgSt) : DFrac :=
  if RespType st.msg.Type' then DFrac.own (1 : Qp).half else DFrac.own 1

end

section
open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

omit [GooseInterp] [GooseSemantics] go_gctx in
theorem mtypeOf_MsgReadIndex : mtypeOf MsgReadIndex = some .readIndex := rfl

/-- A message's tickets: a proposal's entries'. -/
def stTks (γ : RaftNames) (st : MsgSt) : IProp GF :=
  if st.msg.Type' = MsgProp then iprop([∗list] e ∈ st.ents, entTk γ e) else iprop(emp)

/-- A `Ready`'s `SoftState` as the application reads it (2026-10-16, stage R7a, D10): `nil`, or a
`*SoftState` whose `Lead` and `RaftState` are read-only (raft never writes a `SoftState` after
`r.softState()` allocates it: `readyWithoutAccept` hands it out and `acceptReady` keeps it as
`prevSoftSt`). The server's `softStateAt` has this form, so it can be defined over it. -/
def softStateRO (p : Loc) : IProp GF :=
  iprop(⌜p = null⌝ ∨ ∃ (lead : w64) (rs : StateType),
    structFieldRef SoftState go!"Lead" p ↦□ lead ∗ structFieldRef SoftState go!"RaftState" p ↦□ rs)

instance softStateRO_persistent (p : Loc) : Persistent (softStateRO (GF := GF) p) := by
  unfold softStateRO; infer_instance

/-- (D22 S-d3a) What a `Ready` hands the application for the storage: the right to append the batch
(`appendRight`), or with a snapshot the storage itself, at a state with nothing pending and the
loan's floor (`ownRaftLog_lend`); (D22 S-d4, 2026-10-21) and the snapshot's certificate in the
storage's registry (`storCert`, the log's `Hkcert`), which the application's `ApplySnapshot` takes
(`MemoryStorage.ApplySnapshot`'s `memStorCert`). -/
def readyOut (st : Storage) (es : List EntryM) (L : Option SnapLoan) : IProp GF :=
  match L with
  | none => appendRight st es
  | some l => iprop((∃ σ, ownStorage st σ ∗ ⌜σ.pend = [] ∧ σ.fl = l.fl⌝) ∗
      storCert st (snapTrip l.snap l.snap.Metadata'.ConfState'.lists))

/-- (D22 S-d3a) **The application's receipt of a snapshot `Ready`'s loan**, which `Advance` takes:
the half of the snapshot it was handed, and the storage at the snapshot -- its boundary and its
own snapshot the loan's, its lists and `AutoLeave` the snapshot's, holding the entries `es` the
`Ready` handed out after it, nothing pending, the floor it was lent at. What a `MemoryStorage`'s
`ApplySnapshot` then `Append` give (stage S-r). -/
def snapReceipt (st : Storage) (l : SnapLoan) (es : List EntryM) : IProp GF :=
  iprop(ownSnapM l.ptr (DFrac.own (1 : Qp).half) l.snap ∗
    ∃ σr, ownStorage st σr ∗ ⌜σr.prev = snapId l.snap ∧ σr.ss = snapId l.snap ∧ σr.ents = es ∧
      σr.pend = [] ∧ σr.fl = l.fl ∧ σr.scs = l.snap.Metadata'.ConfState'.lists ∧
      σr.sal = l.snap.Metadata'.ConfState'.AutoLeave' ∧ σr.sdat = l.snap.Data'⌝)

/-- The indices a `Ready` hands out are within the node's log at hand-out time (2026-10-18, D19b
stage 5): its last index `L` has a record (`lastRec`, whose time receipt bounds it,
`lastRec_receipt`), the entries to append end at most at `L`, the committed log handed out is
at most `L` long. -/
def readyIdx (γr : RaftNames) (d ce es : List EntryM) : IProp GF :=
  iprop(∃ L : Int, lastRec γr L ∗ ⌜L < 2 ^ 64 ∧
    (∀ e0, es.head? = some e0 → uint.Z e0.Index' + (es.length : Int) ≤ L + 1) ∧
    ((d ++ ce).length : Int) ≤ L⌝)

instance readyIdx_persistent (γr : RaftNames) (d ce es : List EntryM) :
    Persistent (readyIdx (GF := GF) γr d ce es) := by
  unfold readyIdx; infer_instance

end

-- from Proof/go_etcd_io/raft/v3/InvBoot.lean
section
open Iris Iris.BI go_etcd_io.raft.v3
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The `Context` bytes of the peers `pv`, read-only: `ctxs[k]` behind `pv[k].Context`. -/
def peersCtx (pv : List Peer) (ctxs : List (List w8)) : IProp GF :=
  iprop([∗list] p;ctx ∈ pv;ctxs, p.Context' ↦*□ ctx)

instance peersCtx_persistent (pv : List Peer) (ctxs : List (List w8)) :
    Persistent (peersCtx (GF := GF) pv ctxs) := by
  unfold peersCtx; infer_instance

/-- `proto.Marshal` of the `k`-th peer's conf change returns the bytes of the `k`-th boot entry
(see the file header): for a `*pb.ConfChange` at `p` holding `m` with `m.nodeId = ps[k]`,
`m.context = ctxs[k]`, `Type = AddNode` and `Id` unset, the call returns a fresh slice holding
`e.Data'` for `bootLog[k] = e`, with a `nil` error, and gives the message back. Persistent (one
call per peer). -/
def bootMarshal (ps : List w64) (ctxs : List (List w8)) (bootLog : List EntryM) : IProp GF :=
  iprop(□ ∀ (k : Nat) (p : Loc) (dq : DFrac) (m : ConfChangeM) (e : EntryM)
    (_ : ps[k]? = some m.nodeId ∧ ctxs[k]? = some m.context ∧ bootLog[k]? = some e ∧
      m.type = W32 0 ∧ m.id = W64 0) (Φ : val → IProp GF),
    ownConfChange p dq m -∗
    (∀ (d : GoSlice), ownConfChange p dq m -∗ d ↦* e.Data' -∗ Φ (PairV #d #interface.nil)) -∗
    WP (App (Val (@! google_golang_org.protobuf.proto.Marshal))
          (Val #(interface.mkOk (go.GoType.PointerType raftpb.ConfChange.ty) #p))) {{ Φ }})

instance bootMarshal_persistent (ps : List w64) (ctxs : List (List w8)) (bootLog : List EntryM) :
    Persistent (bootMarshal (GF := GF) ps ctxs bootLog) := by
  unfold bootMarshal; infer_instance

/-- (2026-10-25, T-M M2a) The ghost state a member of a new cluster starts `Bootstrap` with, in the
mode `md` (as `rnInit` for `RestartNode`): statically the bootstrap state `bootPState bootLog`
(`ownRaftGhost_alloc_boot`); dynamically the dynamic model's `rboot c0 bootLog`
(`raft_dyn_alloc_boot`: configuration index `0`), the initial configuration `c0` the peers' `V`,
with no learner. -/
def bootInit (γ : RaftNames) (md : RNMode) (id : w64) (V : GSet w64) (bootLog : List EntryM) :
    IProp GF :=
  match md with
  | .static => ownRaftGhost γ id (bootPState bootLog)
  | .dyn dec c0 h0 _ => iprop(⌜γ.dyn = some (DynCfg.ofFold dec c0 h0) ∧ c0 = cfgState V ∅⌝ ∗
      ownRaftGhostR γ dec c0 id (rboot c0 bootLog))

end

-- from Spec/go_etcd_io/raft/v3/newRaft.lean
section
open Iris Iris.BI go_etcd_io.raft.v3
variable [GooseExts]

def HsEmpty (hs : HardStateM) : Prop :=
  hs.Term' = W64 0 ∧ hs.Vote' = W64 0 ∧ hs.Commit' = W64 0

end

-- from Spec/go_etcd_io/raft/v3/Config__validate.lean
section
open Iris Iris.BI go_etcd_io.raft.v3
variable [GooseExts]

/-- What `Config.validate` checks, as a proposition over the `Config`. Each conjunct is
exactly the condition Go tests before one of its `return errors.New(...)`s, except
`Logger ≠ nil`: Go substitutes the package default logger (`getLogger`) for a nil one,
and taking the logger as given keeps the default logger out of the trust base. -/
def ConfigValid (cv : Config) : Prop :=
  cv.ID' ≠ W64 0 ∧
  cv.ID' ≠ W64 18446744073709551615 ∧
  cv.ID' ≠ W64 18446744073709551614 ∧
  (0 < sint.Z cv.HeartbeatTick' ∧ sint.Z cv.HeartbeatTick' < sint.Z cv.ElectionTick') ∧
  cv.Storage' ≠ interface.nil ∧
  0 < sint.Z cv.MaxInflightMsgs' ∧
  (cv.MaxInflightBytes' = W64 0 ∨ uint.Z cv.MaxSizePerMsg' ≤ uint.Z cv.MaxInflightBytes') ∧
  cv.Logger' ≠ interface.nil ∧
  (cv.ReadOnlyOption' = W64 0 ∨ cv.CheckQuorum' = true)

end

-- from Spec/go_etcd_io/raft/v3/NewRawNode.lean
section
open Iris Iris.BI go_etcd_io.raft.v3
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The ghost state a fresh node starts from, in the mode `md` (2026-10-14, reconfiguration stage
B7 part 2): statically the protocol's initial state (`ownRaftGhost_alloc`); dynamically the
dynamic model's (`raft_dyn_alloc`, at `rinit c0`), the initial configuration `c0` the voters `V`
of the persisted `ConfState`, with no learner. -/
def rnInit (γ : RaftNames) (md : RNMode) (id : w64) (V : GSet w64) : IProp GF :=
  match md with
  | .static => ownRaftGhost γ id initPState
  | .dyn dec c0 h0 _ => iprop(⌜γ.dyn = some (DynCfg.ofFold dec c0 h0) ∧ c0 = cfgState V ∅⌝ ∗
      ownRaftGhostR γ dec c0 id (rinit c0))

end

-- from Spec/go_etcd_io/raft/v3/RawNode__ProposeConfChange.lean
section
open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The conf change `o` is one the cluster admits (2026-10-15, stage N): the bytes it is
marshaled to satisfy `γ.reCCOk` (`RaftNames.reCCOk`; always, for a cluster that admits every
change). -/
def CCAllowed (γ : RaftNames) (o : ConfChangeIM) : Prop :=
  ∀ bs, MarshalsConfChange (some o) bs → γ.reCCOk (confChangeEntryType (some o)) bs

end

end EtcdGrove
end Perennial
