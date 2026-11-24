/-
Lean-first (no Rocq counterpart).

# The Antithesis harness's invariant and node state (#33 S4, specs first, part 2)

`notes/antithesis-s4-design.md` §3 is the design; this file is its statement, the vocabulary of the
specs of `Cluster.deliver`, `send`, `reportCause`, `drain` and `run`
(`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/Cluster__<fn>.lean`):

- **Ghost names** `AntNames`: raft's cluster, the stream `strm` (the recorder's ghost variable, half
  here, half in the recorder's lock), each node's view `view j` (a ghost variable of
  `AntSim.NodeView`: half here, half the node goroutine's), each node goroutine's right to report
  `live j`, every message sent `sent` (a monotone list, `sentW` its persistent membership), the
  network's join `net`, the nodes' input channels `inCh j` and the stop channel `stopCh`.
- **The invariant** `antInv γ` (namespace `antN`): open, the stream, the views and the sent list
  with the checker's prefix, the refinement relation and raft's global facts (`AntRun`,
  `raftFactsOwn`); or, once the run is over (`RunCluster` after `nodesWg.Wait()`), the three
  nodes' `live` tokens, so that no report is possible any more.
- **The cluster** `antCluster c γ` (persistent): its read-only fields, the recorder, the nodes'
  read-only records `nodeRO` (id, name, input channel: a bag of `inputOk` inputs), the stop channel
  (a broadcast channel), the network's join, the invariant.
- **The network**: an in-flight message `netMsg γ ml st m` (owned, at the protocol message `m`,
  with what its receiver's `RawNode.Step` takes: `NetFacts`, `isMessage`, the term bound
  `rnTermLB`, and `sentW`); an input `inputOk γ j inp` (a message to node `j`, or a proposal's data
  with raft's proposal resources).
- **A node goroutine's state** `nodeOwn c γ j n v ph`: the `RawNode` (`rawNode`), its per-node
  raft ghost state (`nodeRaft`), the Go fields agreeing with the view `v` (the last `ready`
  report's term, vote, commit and role), the cause cell (`causeOwn`), the view fragment and the
  `live` token, at one of three phases (`Phase`): between inputs (`idle`), at a drain's loop head
  (`loop`: `Reach` from the view, the in-progress boundary at the common prefix), after a drain
  (`drained`: as `idle`, the cause cell not yet reset).

What the specs are written in, with the laws the reports' proofs share (the invariant's
timelessness, `nodeLive_over`: no report once the run is over, `view_update`: a view moved). The bodies of `nodeRaft`, `NetFacts`, `AntRun`
and `raftFactsOwn` are what the proofs need as far as the specs' statements are concerned; the
harness's proof (P-harness) may strengthen them (more conjuncts), which leaves every spec's text
unchanged.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Stmts
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.join.NetJoin
public import Proof.go_etcd_io.raft.v3.RawNodeApi
public import Proof.go_etcd_io.raft.v3.InvRtk
public import Perennial.Golang.Theory.Chan.Idioms.Bag
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast
public import Perennial.Proof.sync.WaitGroupJoin
public import Perennial.Ghost.MonoList
public import Perennial.Ghost.DGhostVar

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-! ## Countability (the views and the sent list are ghost values) -/

section countable
variable [GooseExts]

instance role_countable : Pos.Countable Role :=
  countableOfLeftInverse
    (fun r : Role => match r with | .follower => (0 : Nat) | .candidate => 1 | .leader => 2)
    (fun k => match k with | 1 => .candidate | 2 => .leader | _ => .follower)
    (fun r => by cases r <;> rfl)

instance msgType_countable : Pos.Countable MsgType :=
  countableOfLeftInverse
    (fun t : MsgType => match t with
      | .vote => (0 : Nat) | .voteResp => 1 | .app => 2 | .appResp => 3 | .heartbeat => 4
      | .heartbeatResp => 5 | .propose => 6 | .snap => 7 | .preVote => 8 | .preVoteResp => 9
      | .readIndex => 10 | .readIndexResp => 11)
    (fun k => match k with
      | 1 => .voteResp | 2 => .app | 3 => .appResp | 4 => .heartbeat | 5 => .heartbeatResp
      | 6 => .propose | 7 => .snap | 8 => .preVote | 9 => .preVoteResp | 10 => .readIndex
      | 11 => .readIndexResp | _ => .vote)
    (fun t => by cases t <;> rfl)

instance csLists_countable : Pos.Countable CSLists :=
  countableOfLeftInverse (fun c : CSLists => (c.voters, c.learners, c.outgoing, c.learnersNext))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩) (fun _ => rfl)

instance pmsg_countable : Pos.Countable Msg :=
  countableOfLeftInverse
    (fun m : Msg => ((m.ty, m.src, m.dst, m.term, m.reject, m.index),
      (m.logterm, m.commit, m.rejecthint, m.entries, m.cl, m.al, m.ctx)))
    (fun p => ⟨p.1.1, p.1.2.1, p.1.2.2.1, p.1.2.2.2.1, p.1.2.2.2.2.1, p.1.2.2.2.2.2,
      p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2⟩)
    (fun _ => rfl)

instance readStateM_countable : Pos.Countable ReadStateM :=
  countableOfLeftInverse (fun r : ReadStateM => (r.Index', r.RequestCtx')) (fun p => ⟨p.1, p.2⟩)
    (fun _ => rfl)

instance readReq_countable : Pos.Countable ReadReq :=
  countableOfLeftInverse (fun r : ReadReq => (r.index, r.src, r.ents)) (fun p => ⟨p.1, p.2.1, p.2.2⟩)
    (fun _ => rfl)

instance readOnly_countable : Pos.Countable ReadOnly :=
  countableOfLeftInverse (fun r : ReadOnly => (r.pending, r.acks, r.confirmed))
    (fun p => ⟨p.1, p.2.1, p.2.2⟩) (fun _ => rfl)

instance rdState_countable : Pos.Countable RdState :=
  countableOfLeftInverse (fun r : RdState => (r.states, r.ro, r.pend)) (fun p => ⟨p.1, p.2.1, p.2.2⟩)
    (fun _ => rfl)

instance pstate_countable : Pos.Countable PState :=
  countableOfLeftInverse
    (fun s : PState => ((s.term, s.vote, s.lead, s.role, s.votes, s.outbox),
      (s.base, s.log, s.commit, s.matched, s.rd)))
    (fun p => ⟨p.1.1, p.1.2.1, p.1.2.2.1, p.1.2.2.2.1, p.1.2.2.2.2.1, p.1.2.2.2.2.2,
      p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2⟩)
    (fun _ => rfl)

instance nodeView_countable : Pos.Countable AntSim.NodeView :=
  countableOfLeftInverse
    (fun v : AntSim.NodeView => (v.ps, v.delivered, v.qs, v.pend, v.ce, v.byE, v.cause, v.told))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2⟩)
    (fun _ => rfl)

instance input_countable :
    Pos.Countable github_com.mit_pdos.etcd_grove.examples.raft.antithesis.input :=
  countableOfLeftInverse
    (fun i : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.input =>
      (i.kind', i.msg', i.data'))
    (fun p => ⟨p.1, p.2.1, p.2.2⟩) (fun _ => rfl)

end countable

/-! ## Names and pure parts -/

section pure
variable [GooseExts]

/-- The harness's input type, by its short name. -/
abbrev H.input := github_com.mit_pdos.etcd_grove.examples.raft.antithesis.input

/-- **The ghost names of a run** (see the file header). -/
structure AntNames where
  raft : Cluster
  strm : GName
  view : Fin 3 → GName
  live : Fin 3 → GName
  sent : GName
  net : NetJoinNames
  inCh : Fin 3 → ChanNames
  stopCh : ChanNames

/-- The harness's invariant's namespace. -/
def antN : Namespace := nroot.@"antithesis"

/-- The network join's namespace. -/
def antNetN : Namespace := nroot.@"antithesis_net"

/-- **What the run's invariant knows of the stream so far** (pure): the checker took it, rejected
nothing, and is at `S` (`Prefix`); `S` is related to the views and the sent messages (`AntSim`);
the stream is within the Go `int`'s budget and has no configuration change (`check.Run`'s
premises, `Stream.Bounded`, `Stream.ConfBounded`; no report carries an entry that changes a name,
`Event.ChgOk 0`, so that the next stream's `ConfBounded` holds at `E = 0`). -/
def AntRun (evs : List AntCheck.Event) (S : AntCheck.State) (V : Fin 3 → AntSim.NodeView)
    (net : List Msg) : Prop :=
  AntSim.Prefix AntSim.cfg3 evs S ∧ AntSim.AntSim S V net ∧ AntCheck.Stream.Bounded evs ∧
    AntCheck.Stream.ConfBounded AntSim.cfg3 evs ∧ ∀ ev ∈ evs, ev.ChgOk 0

/-- **What an in-flight message's receiver needs of it** (pure): `RawNode.Step`'s premises at its
destination (`NetMsgOk`, the harness's types, a heartbeat response with no context), the entries
`entryOf` takes (normal), its protocol reading `m`, and every number below `2 ^ 61` (so that
`msgOf`'s `int(x)` readings are `AntSim.msgOf`'s). -/
def NetFacts (st : MsgSt) (m : Msg) : Prop :=
  NetMsgOk st.msg.To' st ∧ st.msg.Type' ∈ antStepTypes ∧
  (st.msg.Type' = MsgHeartbeatResp → st.ctx = []) ∧ AllNormal st.ents ∧ absMsgOf st = some m ∧
  (∃ j : Fin 3, m.dst = AntSim.nodeId j) ∧ (∃ i : Fin 3, m.src = AntSim.nodeId i) ∧
  uint.Z st.msg.Term' < 2 ^ 61 ∧ uint.Z st.msg.Index' < 2 ^ 61 ∧ uint.Z st.msg.LogTerm' < 2 ^ 61 ∧
  uint.Z st.msg.Commit' < 2 ^ 61 ∧ (∀ e ∈ st.ents, uint.Z e.Term' < 2 ^ 61)

/-- The phases of a node goroutine (see the file header): between inputs; at a drain's loop head,
the node at `ps₁`, reached from the view by an input, by `Advance`, or by nothing (the boot drain),
over the sent messages `net₀` (a lower bound of the invariant's); after the drain. -/
inductive Phase where
  | idle
  | loop (net₀ : List Msg) (ps₁ : PState)
  | drained

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]

/-! ## Ghost pieces -/

/-- **Node `j`'s view, the goroutine's half.** -/
def viewFrag (γ : AntNames) (j : Fin 3) (v : AntSim.NodeView) : IProp GF :=
  ghostVar (γ.view j) (1 : Qp).half v

/-- **Node `j`'s goroutine may report** (exclusive; the invariant holds all three once the run is
over). -/
def nodeLive (γ : AntNames) (j : Fin 3) : IProp GF := dghostVar (γ.live j) (DFrac.own 1) ()

/-- **`m` was sent** (persistent): it is in the sent list. -/
def sentW (γ : AntNames) (m : Msg) : IProp GF := iprop(∃ i : Nat, monoListIdxOwn γ.sent i m)

/-- **At least `net` was sent** (persistent). -/
def sentLb (γ : AntNames) (net : List Msg) : IProp GF := monoListLbOwn γ.sent net

instance sentW_persistent (γ : AntNames) (m : Msg) : Persistent (sentW (GF := GF) γ m) := by
  unfold sentW; infer_instance

instance sentLb_persistent (γ : AntNames) (net : List Msg) :
    Persistent (sentLb (GF := GF) γ net) := by
  unfold sentLb; infer_instance

/-- **Raft's global facts `G`, as persistent ghost facts** (`AntSim.RaftFacts`' reading,
`notes/antithesis-rawnode-design.md` §3.4): each leader's witness, each vote, each log's records
(its indices its positions), each campaign log with its leader's witness, the committed log, each
commit recorded in a term (the log it was recorded at, with its records: `commitIn_camp`'s
premises). -/
def raftFactsOwn (γ : RaftNames) (G : AntSim.RaftFacts) : IProp GF :=
  iprop(([∗list] p ∈ G.leaders, isLeader γ p.1 p.2) ∗
    ([∗list] v ∈ G.votes, isVote γ v.1 v.2.1 v.2.2) ∗
    ([∗list] l ∈ G.logs, logRecs γ base0 l ∗ ⌜AntSim.LogIdx l⌝) ∗
    ([∗list] p ∈ G.camps, ∃ c : w64, isLeader γ c p.1 ∗ isCamp γ c p.1 p.2) ∗
    isCommitted γ G.committed ∗
    ([∗list] x ∈ G.commits, ∃ F : List EntryM,
      commitIn γ F (W64 (x.2 : Int)) x.1 ∗ logRecs γ base0 F ∗
      ⌜PlogWf base0 F ∧ x.2 ≤ F.length ∧ (x.2 : Int) < 2 ^ 64 ∧ F.take x.2 <+: G.committed⌝))

instance raftFactsOwn_persistent (γ : RaftNames) (G : AntSim.RaftFacts) :
    Persistent (raftFactsOwn (GF := GF) γ G) := by
  unfold raftFactsOwn; infer_instance

instance raftFactsOwn_timeless (γ : RaftNames) (G : AntSim.RaftFacts) :
    Timeless (raftFactsOwn (GF := GF) γ G) := by
  unfold raftFactsOwn; infer_instance

/-! ## The invariant -/

/-- **The run's invariant, open**: the stream (the invariant's half of `rec`), the views (their
invariant halves), the sent list (its authority), the run's pure facts, and raft's facts behind
`GlobalOk`, which also certify each view's log (`entOf` forgets an entry's index, so `GlobalOk`'s
`S.log[n] = logOf l` does not name the view's log; a `Ready`'s first-conflict fact compares the
view's log with the node's by log matching). -/
def antOpen (γ : AntNames) : IProp GF :=
  iprop(∃ (evs : List AntCheck.Event) (S : AntCheck.State) (V : Fin 3 → AntSim.NodeView)
      (net : List Msg) (G : AntSim.RaftFacts),
    ghostVar γ.strm (1 : Qp).half evs ∗
    ghostVar (γ.view 0) (1 : Qp).half (V 0) ∗ ghostVar (γ.view 1) (1 : Qp).half (V 1) ∗
    ghostVar (γ.view 2) (1 : Qp).half (V 2) ∗
    monoListAuthOwn γ.sent 1 net ∗
    ⌜AntRun evs S V net ∧ AntSim.RaftLaws G ∧ AntSim.GlobalOk S net G ∧
      ∀ j : Fin 3, (V j).ps.log ∈ G.logs⌝ ∗
    raftFactsOwn γ.raft.raftNames G)

instance antOpen_timeless (γ : AntNames) : Timeless (antOpen (GF := GF) γ) := by
  unfold antOpen; infer_instance

/-- **The run's invariant** (`antN`; `notes/antithesis-s4-design.md` §3): open, or over (the three
nodes' `live` tokens given up: `RunCluster` took the stream out). -/
def antInv (γ : AntNames) : IProp GF :=
  iprop(antOpen γ ∨ (nodeLive γ 0 ∗ nodeLive γ 1 ∗ nodeLive γ 2))

instance antInv_timeless (γ : AntNames) : Timeless (antInv (GF := GF) γ) := by
  unfold antInv nodeLive; infer_instance

/-! ## The network -/

/-- **An in-flight message** `ml` at the state `st`, the protocol message `m`: owned (what
`RawNode.Step` takes: `msgPtsCC` at own `1`), with its receiver's premises (`NetFacts`), raft's
certificate (`isMessage`), its term within the budget (`rnTermLB`), and sent. -/
def netMsg (γ : AntNames) (ml : Loc) (st : MsgSt) (m : Msg) : IProp GF :=
  iprop((∃ c : MsgC, msgPtsCC ml (DFrac.own 1) DFrac.discard (needsCap st.msg) c ∗
      ⌜c.model = st ∧ c.csUfNil⌝) ∗
    ⌜NetFacts st m⌝ ∗ □ isMessage γ.raft.raftNames m ∗ rnTermLB γ.raft st.msg.Term' ∗ sentW γ m)

/-- **A message `Cluster.send` takes** (`drain` hands it every message of a `Ready`, cloned): a
forwarded proposal, which `send` drops (`notes/antithesis-s4-design.md` §7; `csUfNil`, as an
in-flight message's, so that `send` reads its type through the getters' `msgPtsC`), or an in-flight
message. -/
def sendMsg (γ : AntNames) (ml : Loc) (st : MsgSt) : IProp GF :=
  iprop((⌜st.msg.Type' = MsgProp⌝ ∗ ∃ c : MsgC, msgPtsCC ml (DFrac.own 1) DFrac.discard
      (needsCap st.msg) c ∗ ⌜c.model = st ∧ c.csUfNil⌝) ∨
    (∃ m : Msg, netMsg γ ml st m))

/-- **A proposal's raft resources** (`RawNode.Propose`'s premises): the data's certificate and its
ticket, within raft's data bound. -/
def propOk (γ : AntNames) (data : List w8) : IProp GF :=
  iprop(propData γ.raft.raftNames (propEntryM data) ∗ entTk γ.raft.raftNames (propEntryM data) ∗
    ⌜∀ b, γ.raft.raftNames.maxData = some b → data.length ≤ b⌝)

/-- **An input to node `j`** (what `n.in` holds): a message to it (`inMsg`, `0`) in flight, or a
proposal's data (`inProp`, `1`) with its resources. -/
def inputOk (γ : AntNames) (j : Fin 3) (inp : H.input) : IProp GF :=
  iprop((⌜inp.kind' = W64 0⌝ ∗ ∃ (st : MsgSt) (m : Msg), netMsg γ inp.msg' st m ∗
      ⌜m.dst = AntSim.nodeId j⌝) ∨
    (⌜inp.kind' = W64 1⌝ ∗ ∃ data : List w8, inp.data' ↦*□ data ∗ propOk γ data))

/-! ## The cluster -/

/-- **Node `j`'s read-only record** (persistent): `n` is the node of id `j + 1`, its name, and its
input channel (a bag of `inputOk` inputs). -/
def nodeRO (γ : AntNames) (n : Loc) (j : Fin 3) : IProp GF :=
  iprop(∃ ch : Loc, n.[H.node, go!"id"] ↦□ AntSim.nodeId j ∗
    n.[H.node, go!"name"] ↦□ AntSim.nameOf (AntSim.nodeId j) ∗ n.[H.node, go!"in"] ↦□ ch ∗
    isChanBag (γ.inCh j) ch (inputOk γ j))

instance nodeRO_persistent (γ : AntNames) (n : Loc) (j : Fin 3) :
    Persistent (nodeRO (GF := GF) γ n j) := by
  unfold nodeRO; infer_instance

/-- **The cluster `c` of the run `γ`** (persistent): its configuration (`CfgOk`), its recorder,
its three nodes (`clusterRO`, each `nodeRO`), its stop channel (broadcast, nothing carried), the
network's join, the run's invariant, and the receipts' fit (`antRunFits`: with `Stream.Fits`, a
report's new stream within `Stream.Bounded`'s size bound). (Raft's term budget, `rnBudget`, is sealed and its
persistence a law, `rnBudget_persistent.law`; each node carries it, `nodeRaft`.) -/
def antCluster (c : Loc) (γ : AntNames) : IProp GF :=
  iprop(∃ (cfg : H.Config) (r : Loc) (ns : List Loc) (stop : Loc),
    c.[H.Cluster, go!"cfg"] ↦□ cfg ∗ ⌜CfgOk cfg⌝ ∗
    c.[H.Cluster, go!"rec"] ↦□ r ∗ isRecorder γ.strm r ∗
    clusterRO c ns (W64 3) ∗ ⌜ns.length = 3⌝ ∗
    nodeRO γ ns[0]! 0 ∗ nodeRO γ ns[1]! 1 ∗ nodeRO γ ns[2]! 2 ∗
    c.[H.Cluster, go!"stop"] ↦□ stop ∗ ownBroadcastChan stop γ.stopCh iprop(True) .Unknown ∗
    isNetJoin antNetN (c.[H.Cluster, go!"netWg"]) γ.net ∗
    inv antN (antInv γ) ∗ ⌜antRunFits GF⌝)

instance antCluster_persistent (c : Loc) (γ : AntNames) :
    Persistent (antCluster (GF := GF) c γ) := by
  unfold antCluster
  have : ∀ (stop : Loc) (γc : ChanNames), Persistent (ownBroadcastChan (GF := GF) stop γc iprop(True) .Unknown) := fun _ _ => inferInstance
  have : ∀ (r : Loc), Persistent (isRecorder (GF := GF) γ.strm r) := fun _ => inferInstance
  have : ∀ ns, Persistent (clusterRO (GF := GF) c ns (W64 3)) := fun _ => inferInstance
  have : Persistent (isNetJoin (GF := GF) antNetN (c.[H.Cluster, go!"netWg"]) γ.net) := inferInstance
  have : Persistent (inv (GF := GF) antN (antInv γ)) := inferInstance
  have : ∀ (cfg : H.Config), Persistent (c.[H.Cluster, go!"cfg"] ↦□ cfg : IProp GF) := fun _ => inferInstance
  have : ∀ (r : Loc), Persistent (c.[H.Cluster, go!"rec"] ↦□ r : IProp GF) := fun _ => inferInstance
  have : ∀ (ns : List Loc), Persistent (nodeRO (GF := GF) γ ns[0]! 0) := fun _ => inferInstance
  have : ∀ (ns : List Loc), Persistent (nodeRO (GF := GF) γ ns[1]! 1) := fun _ => inferInstance
  have : ∀ (stop : Loc), Persistent (c.[H.Cluster, go!"stop"] ↦□ stop : IProp GF) := fun _ => inferInstance
  have : ∀ (cfg : H.Config), Persistent (iprop(⌜CfgOk cfg⌝) : IProp GF) := fun _ => inferInstance
  have : ∀ (stop : Loc), Persistent (iprop(c.[H.Cluster, go!"stop"] ↦□ stop ∗ ownBroadcastChan stop γ.stopCh iprop(True) .Unknown ∗
    isNetJoin antNetN (c.[H.Cluster, go!"netWg"]) γ.net ∗ inv antN (antInv γ) ∗ ⌜antRunFits GF⌝) : IProp GF) := fun _ => inferInstance
  infer_instance

/-- **A share `q` of the right to add network goroutines** (`netWg`). -/
def netAdder (c : Loc) (γ : AntNames) (q : Qp) : IProp GF :=
  njAdder antNetN (c.[H.Cluster, go!"netWg"]) γ.net q

/-! ## A node goroutine's state -/

/-- **Node `j`'s raft ghost state the harness's calls take** (`RawNode.Ready`'s and its *enter*'s
frame): its generation view and free batch slot, its durable state's ghost (`ownDurGhost`, at
`rs.dur`), its term ceiling within the budget, and the budget; and the cluster's ghost names'
static facts (`RunCluster` allocates them so): untraced (the inputs' and `Advance`'s exact effects
are guarded by it), the configuration the three voters (`rnCfg` is `AntSim.cfgM3`), no bound on
proposed data (`Step`'s message-size premise void). -/
def nodeRaft (γ : AntNames) (j : Fin 3) (rs : RNState) : IProp GF :=
  iprop(∃ (x : CrashNames) (g : Nat),
    genView γ.raft.raftNames (AntSim.nodeId j) x 1 g ∗ slotFree γ.raft.raftNames (AntSim.nodeId j) g ∗
    ownDurGhost γ.raft.raftNames (AntSim.nodeId j) rs.dur ∗ rnTermLB γ.raft rs.tc ∗
    rnBudget γ.raft ∗
    ⌜γ.raft.raftNames.reTrace = none ∧ γ.raft.raftNames.reCfg = AntSim.voters3 ∧
      γ.raft.raftNames.maxData = none⌝)

/-- **The cause cell** (`n.cause` at `cl`): while the drain's `recv` is not reported (`by = recv`,
`told = false`), the report of the handled message `m` (`msgOf(inp.msg, n.id)`, made before
`Step`), with `m`'s membership in the sent list, the report's numbers within the checker's bound
and its receipts; otherwise `nil`. -/
def causeOwn (γ : AntNames) (j : Fin 3) (v : AntSim.NodeView) (cl : Loc) : IProp GF :=
  if v.byE = go!"recv" ∧ v.told = false then
    iprop(∃ (m : Msg) (g : AntCheck.G.Msg), ⌜v.cause = some m ∧ m.dst = AntSim.nodeId j ∧
        (AntSim.evRecv (AntSim.nodeId j) m).NumsOk⌝ ∗
      cl ↦ g ∗ AntCheck.msgRO g (AntSim.msgOf m (AntSim.nodeId j)) ∗ sentW γ m ∗
      ⧗ (AntSim.evRecv (AntSim.nodeId j) m).weight)
  else iprop(⌜cl = null⌝)

/-- **The `RawNode`'s record against the view** (pure): the client record's last reported hard
state, role and durable log are the view's (its last `ready` report's, C1), what it handed out is
the view's delivered and unreported committed entries, nothing queued or unpersisted, not
following a snapshot. (The term is the node's, `rawNode_wf`: at a loop head it is the input's.) -/
def RsView (rs : RNState) (v : AntSim.NodeView) : Prop :=
  rs.phs = HardStateM.mk v.ps.term v.ps.vote v.ps.commit ∧ rs.role = roleGo v.ps.role ∧
  rs.dur.ents = v.ps.log ∧ rs.delivered = v.delivered ++ v.ce ∧ rs.steps = [] ∧
  rs.unpersisted = [] ∧ rs.flw = false

/-- **Node `j`'s goroutine's state** at `n`, its view `v`, the phase `ph` (see the file header): the
`RawNode` at `rs ps qs ip` and its raft ghost state; its `MemoryStorage` (`ms`, in the
`bootStorage` raft reads, `si`); the Go fields `role term vote commit` the view's (the last
`ready`'s), `applied` any; the cause cell; the view fragment and the right to report; and the
phase's facts:
- `idle`: nothing of a `Ready` left (`Idle`), the node at the view's state, idle (`PIdle`), its
  in-progress boundary at the log's end, the cause cell `nil`;
- `loop net₀ ps₁`: the node at `ps₁`, reached from the view (`Reach` over `net₀`, a lower bound of
  the sent list), nothing queued, the boundary at the common prefix of the view's log and `ps₁`'s;
- `drained`: as `idle`, but the cause cell as `causeOwn` (`run` resets it). -/
def nodeOwn (c : Loc) (γ : AntNames) (j : Fin 3) (n : Loc) (v : AntSim.NodeView) (ph : Phase) :
    IProp GF :=
  iprop(∃ (rn ms si : Loc) (rs : RNState) (ps : PState) (qs : List Msg) (ip : Nat) (cl : Loc)
      (applied : w64),
    n.[H.node, go!"rn"] ↦□ rn ∗ n.[H.node, go!"storage"] ↦□ ms ∗
    bootStorRec si ms [W64 1, W64 2, W64 3] ∗
    ⌜rs.storage = interface.ok ⟨go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.bootStorage.ty, #si⟩⌝ ∗
    rawNode γ.raft.raftNames rn (AntSim.nodeId j) rs ps qs ip ∗ nodeRaft γ j rs ∗
    ⌜RsView rs v⌝ ∗
    n.[H.node, go!"role"] ↦ roleStr (roleGo v.ps.role) ∗ n.[H.node, go!"term"] ↦ v.ps.term ∗
    n.[H.node, go!"vote"] ↦ v.ps.vote ∗ n.[H.node, go!"commit"] ↦ v.ps.commit ∗
    n.[H.node, go!"applied"] ↦ applied ∗ n.[H.node, go!"cause"] ↦ cl ∗
    viewFrag γ j v ∗ nodeLive γ j ∗
    match ph with
    | .idle => iprop(⌜v.Idle ∧ ps = v.ps ∧ qs = [] ∧ ip = v.ps.log.length ∧ PIdle rs ps ∧
        cl = null⌝)
    | .loop net₀ ps₁ => iprop(⌜ps = ps₁ ∧ AntSim.Reach (AntSim.nodeId j) net₀ v ps₁ ∧ qs = [] ∧
        ip = lcpLen v.ps.log ps₁.log⌝ ∗ sentLb γ net₀ ∗ causeOwn γ j v cl)
    | .drained => iprop(⌜v.Idle ∧ ps = v.ps ∧ qs = [] ∧ ip = v.ps.log.length ∧ PIdle rs ps⌝ ∗
        causeOwn γ j v cl))

/-- **What a node goroutine gives back at its end** (`nodesWg.Done()`): its right to report and
its share of the network's adders. -/
def nodeExit (c : Loc) (γ : AntNames) (j : Fin 3) (q : Qp) : IProp GF :=
  iprop(nodeLive γ j ∗ netAdder c γ q)

/-! ## Laws of the node's tokens and views (the reports' atomic updates) -/

/-- The run is not over while a node goroutine holds its `live` token. -/
theorem nodeLive_over (γ : AntNames) (j : Fin 3) :
    nodeLive (GF := GF) γ j ∗ (nodeLive γ 0 ∗ nodeLive γ 1 ∗ nodeLive γ 2) ⊢ False := by
  have h : ∀ k : Fin 3, nodeLive (GF := GF) γ k ∗ nodeLive γ k ⊢ False := by
    intro k
    unfold nodeLive
    iintro ⟨H1, H2⟩
    icombine H1 H2 gives %Hv
    exfalso
    have := DFrac.valid_own_op Hv.1
    simp at this
  obtain ⟨k, hk⟩ := j
  match k, hk with
  | 0, hk => rw [show (⟨0, hk⟩ : Fin 3) = 0 from rfl]; iintro ⟨H, H0, -, -⟩; iapply h 0; iframe H H0
  | 1, hk => rw [show (⟨1, hk⟩ : Fin 3) = 1 from rfl]; iintro ⟨H, -, H1, -⟩; iapply h 1; iframe H H1
  | 2, hk => rw [show (⟨2, hk⟩ : Fin 3) = 2 from rfl]; iintro ⟨H, -, -, H2⟩; iapply h 2; iframe H H2

/-- **Node `j`'s view updated**: the goroutine's half and the invariant's agree, and both move. -/
theorem view_update (E : CoPset) (γ : AntNames) (j : Fin 3) (V : Fin 3 → AntSim.NodeView)
    (v v' : AntSim.NodeView) :
    viewFrag (GF := GF) γ j v ∗ ghostVar (γ.view 0) (1 : Qp).half (V 0) ∗
        ghostVar (γ.view 1) (1 : Qp).half (V 1) ∗ ghostVar (γ.view 2) (1 : Qp).half (V 2) ⊢
      |={E}=> ⌜V j = v⌝ ∗ viewFrag γ j v' ∗
        ghostVar (γ.view 0) (1 : Qp).half (AntSim.setV V j v' 0) ∗
        ghostVar (γ.view 1) (1 : Qp).half (AntSim.setV V j v' 1) ∗
        ghostVar (γ.view 2) (1 : Qp).half (AntSim.setV V j v' 2) := by
  unfold viewFrag
  obtain ⟨k, hk⟩ := j
  match k, hk with
  | 0, hk =>
    rw [show (⟨0, hk⟩ : Fin 3) = 0 from rfl]
    iintro ⟨Hv, H0, H1, H2⟩
    ihave %Heq := ghostVar_agree (GF := GF) _ v _ (V 0) _ $$ Hv H0
    imod ghostVar_update_halves (GF := GF) v' _ v (V 0) $$ Hv H0 with ⟨Hv, H0⟩
    imodintro
    simp (config := { decide := true }) only [AntSim.setV, ite_true, ite_false]
    isplitr; · ipureintro; exact Heq.symm
    iframe Hv H0 H1 H2
  | 1, hk =>
    rw [show (⟨1, hk⟩ : Fin 3) = 1 from rfl]
    iintro ⟨Hv, H0, H1, H2⟩
    ihave %Heq := ghostVar_agree (GF := GF) _ v _ (V 1) _ $$ Hv H1
    imod ghostVar_update_halves (GF := GF) v' _ v (V 1) $$ Hv H1 with ⟨Hv, H1⟩
    imodintro
    simp (config := { decide := true }) only [AntSim.setV, ite_true, ite_false]
    isplitr; · ipureintro; exact Heq.symm
    iframe Hv H0 H1 H2
  | 2, hk =>
    rw [show (⟨2, hk⟩ : Fin 3) = 2 from rfl]
    iintro ⟨Hv, H0, H1, H2⟩
    ihave %Heq := ghostVar_agree (GF := GF) _ v _ (V 2) _ $$ Hv H2
    imod ghostVar_update_halves (GF := GF) v' _ v (V 2) $$ Hv H2 with ⟨Hv, H2⟩
    imodintro
    simp (config := { decide := true }) only [AntSim.setV, ite_true, ite_false]
    isplitr; · ipureintro; exact Heq.symm
    iframe Hv H0 H1 H2

end defs

end AntHarness
end EtcdGrove
end Perennial
