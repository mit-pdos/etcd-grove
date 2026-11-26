/-
Lean-first (no Rocq counterpart).

# The parity driver's run invariant and node state (#33 parity B1)

`notes/antithesis-parity-design.md` §3.1-§3.3, §3.6 over the parity driver
(`examples/raft/antithesis/{driver,node,harness}.go`): S4's `HarnessInv.lean` (its
`AntNames`/`antInv`/`nodeOwn`/`netAdder`) generalized from three nodes to the run's `Fin R.N`
(`R : AntSim.RunCfg`, read off the drawn mode: `ModeRun`), with the per-node ownership the Sim's
`NodeView` needs (design §3.2: the node's disk `v.dur`, its configuration `v.conf`, its pending reads
`v.reads`, whether it runs `v.alive`) and the new goroutines' resources:

- **Ghost names** `AntNames`: the run (`R`, the conf-change decoder `dec`, the driver's scope and
  mode), raft's cluster, the stream, each node's view and right to report (`Fin R.N`), the protocol
  messages sent (`sent`) and the transfer messages sent (`xsent`, `XMsg`: `MsgTransferLeader`,
  `MsgTimeoutNow`), the read contexts handed out (`rctx`), the network's join, the input channels,
  the stop channel.
- **The invariant** `antInv γ` (namespace `antN`): open (`antOpen`: the stream, the `N` views, the
  sent lists, the Sim's relation `AntRun` at `R`, raft's global facts), or over (every node's `live`
  token).
- **The network**: an in-flight protocol message `netMsg` (its receiver's `RawNode.Step` premises,
  `NetFacts`, at the types the mode carries, `netTypes`) or transfer message `netXMsg`
  (`XNetFacts`); what `send` takes, `sendMsg` (a forwarded proposal, dropped unless the mode
  forwards; or an in-flight message).
- **The inputs** `inputOk γ j inp`, one arm per input kind of `driver.go`: a message (`inMsg`), a
  proposal (`inProp`, with raft's proposal resources `propOk`), a read (`inRead`, a fresh context,
  `readOk`), a transfer (`inTransfer`, to a node), a campaign, an unreachable report; each B2/B3 kind
  (`inConf`, `inSnapStatus`, `inSnapshot`, `inFlush`, `inWork`, `inKill`) only in a mode with its
  feature on, and with no resources yet (its batch adds them: the arm is `False` while the B1 mask
  keeps the feature off, so B1's `RunCluster` never delivers one).
- **The cluster** `antCluster c γ` (persistent): read-only fields (`clusterRO`: nodes, mode,
  initial voters), the recorder, each node's read-only record `nodeRO` (id, name, input channel, disk
  pointer, its logger's cell `autoLeft` in an invariant: raft calls the logger, `nodeLogger.Infof`,
  from inside its own calls), the stop channel, the network's join, the `down` lock, the invariant,
  the proposer's minting of proposal resources (`propMinter`).
- **A node goroutine's state** `nodeOwn c γ j n v ph`, at a phase: `down` (before `start`: its disk
  at `v.dur`, its memory any), `idle`, `loop` (at a drain's loop head), `drained`.
- **What the behaviours hold**: the reader's contexts handed out so far (`readerOwn`).

The laws the proofs share (`nodeLive_over`, `view_update`) are stated here as `.law`s
(statements, proved with the invariant's proof, B1's second phase). As in S4, the bodies of
`nodeRaft`, `NetFacts`, `AntRun`, `raftFactsOwn` and the B2/B3 input arms are what the specs'
statements need; the proofs may strengthen them, which leaves every spec's text unchanged.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessBase
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessCountable
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.AntStorage
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Stmts
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.join.NetJoin
public import Proof.go_etcd_io.raft.v3.RawNodeApi
public import Perennial.Golang.Theory.Chan.Idioms.Bag
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast
public import Perennial.Proof.sync.WaitGroupJoin
public import Perennial.Ghost.MonoList
public import Perennial.Ghost.DGhostVar
public import Perennial.Ghost.AuthSet

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-! ## Names and pure parts -/

section pure
variable [GooseExts]

/-- **The ghost names of a run** (see the file header). `R`, `dec`, `scope` and `mode` are the
run's: `antCluster` relates them (`InScope scope mode`, `ModeRun scope mode R`). -/
structure AntNames where
  R : AntSim.RunCfg
  dec : CCDec
  scope : H.Scope
  mode : H.Mode
  raft : Cluster
  strm : GName
  view : Fin R.N → GName
  live : Fin R.N → GName
  sent : GName
  xsent : GName
  rctx : GName
  net : NetJoinNames
  inCh : Fin R.N → ChanNames
  stopCh : ChanNames

/-- The run's invariant's namespace. -/
def antN : Namespace := nroot.@"antithesis"

/-- The network join's namespace. -/
def antNetN : Namespace := nroot.@"antithesis_net"

/-- The nodes' logger cells' namespace (`nodeRO`). -/
def antLogN : Namespace := nroot.@"antithesis_log"

/-- **What the run's invariant knows of the stream so far** (pure; S4's `AntRun` at `R`): the
checker took it at `R.cfg`, rejected nothing, and is at `S` (`Prefix`); `S` is related to the views
and the sent messages (`AntSim R dec`); the stream is within `check.Run`'s bounds
(`Stream.Bounded`, `Stream.ConfBounded`) and no report carries an entry that changes a name
(`Event.ChgOk 0`). -/
def AntRun (R : AntSim.RunCfg) (dec : CCDec) (evs : List AntCheck.Event) (S : AntCheck.State)
    (V : Fin R.N → AntSim.NodeView) (net : List Msg) (xnet : List XMsg) : Prop :=
  AntSim.Prefix R.cfg evs S ∧ AntSim.AntSim R dec S V net xnet ∧ AntCheck.Stream.Bounded evs ∧
    AntCheck.Stream.ConfBounded R.cfg evs ∧ ∀ ev ∈ evs, ev.ChgOk 0

/-- **The protocol message types the driver's network carries in a run of mask `md`** (what a
node's `RawNode.Step` is handed from the network): S4's (`antStepTypes`), the pre-vote pair with
pre-vote, the read-index pair with reads, `MsgSnap` with snapshots (B3), a forwarded `MsgProp` with
forwarding (later). -/
def netTypes (md : RnMode) : List w32 :=
  antStepTypes ++ (if md.prevote then [MsgPreVote, MsgPreVoteResp] else []) ++
  (if md.reads then [MsgReadIndex, MsgReadIndexResp] else []) ++
  (if md.snapshots then [MsgSnap] else []) ++ (if md.forwarding then [MsgProp] else [])

/-- **What an in-flight protocol message's receiver needs of it** (pure; S4's `NetFacts` at `R`):
`RawNode.Step`'s premises at its destination (`NetMsgOk`, a type the mask carries; a heartbeat and
its response with no context while reads are off), its entries normal, its protocol reading `m`
from and to a server of the run, and every number below `2 ^ 61`. -/
def NetFacts (R : AntSim.RunCfg) (st : MsgSt) (m : Msg) : Prop :=
  NetMsgOk st.msg.To' st ∧ st.msg.Type' ∈ netTypes R.md ∧
  (R.md.reads = false → st.msg.Type' = MsgHeartbeat ∨ st.msg.Type' = MsgHeartbeatResp → st.ctx = []) ∧
  AllNormal st.ents ∧ absMsgOf st = some m ∧
  (∃ j : Fin R.N, m.dst = AntSim.nodeId j) ∧ (∃ i : Fin R.N, m.src = AntSim.nodeId i) ∧
  uint.Z st.msg.Term' < 2 ^ 61 ∧ uint.Z st.msg.Index' < 2 ^ 61 ∧ uint.Z st.msg.LogTerm' < 2 ^ 61 ∧
  uint.Z st.msg.Commit' < 2 ^ 61 ∧ (∀ e ∈ st.ents, uint.Z e.Term' < 2 ^ 61)

/-- **What an in-flight transfer message's receiver needs of it** (pure): a `MsgTimeoutNow` or a
(forwarded) `MsgTransferLeader`, read as the `XMsg` `x` (type, source, destination, term) between
two servers of the run, in a run with transfers on, its term below `2 ^ 61`. -/
def XNetFacts (R : AntSim.RunCfg) (st : MsgSt) (x : XMsg) : Prop :=
  R.md.transfer = true ∧ NetMsgOk st.msg.To' st ∧
  ((st.msg.Type' = MsgTimeoutNow ∧ x.ty = .timeoutNow) ∨
    (st.msg.Type' = MsgTransferLeader ∧ x.ty = .transferLeader)) ∧
  x.src = st.msg.From' ∧ x.dst = st.msg.To' ∧ x.term = st.msg.Term' ∧
  (∃ j : Fin R.N, x.dst = AntSim.nodeId j) ∧ (∃ i : Fin R.N, x.src = AntSim.nodeId i) ∧
  uint.Z st.msg.Term' < 2 ^ 61

/-- **The view's entries are normal** (S4's `ViewNormal` over the full log): `entryOf` takes them
without `changeOf` (conf entries are batch B3's), and the message its drain handles is a step's. -/
def ViewNormal (v : AntSim.NodeView) : Prop :=
  AllNormal v.r.full ∧ ∀ m, v.cause = some m → AllNormal m.entries ∧ uint.Z m.index < 2 ^ 61 ∧ uint.Z m.logterm < 2 ^ 61 ∧
    m.ty ≠ .propose

/-- A drain's `by`, one of the driver's (`node.go`'s `input`/`drain` callers). -/
def ByOk (b : AntCheck.Str) : Prop :=
  b = go!"boot" ∨ b = go!"recv" ∨ b = go!"tick" ∨ b = go!"propose" ∨ b = go!"read" ∨
  b = go!"campaign" ∨ b = go!"transfer"

/-- **The masked-off bits a node's input paths test** (`node.go`), off in a run of B1's mask: no
batching (`flush`, `note`), synchronous storage (`drainAsync`), no parallel or split writes
(`parallel`, `parts`), no snapshots and no snapshot reports (`drain`'s snapshot branch, `sent`), no
conf changes, no restarts (`emit`'s fuse). -/
def DrainB1 (scope : H.Scope) (mode : H.Mode) : Prop :=
  mode.Batch' = false ∧ mode.Async' = false ∧ mode.Parallel' = false ∧ mode.Split' = W64 0 ∧
  mode.SnapStatus' = false ∧ mode.Restarts' = false ∧ scope.Snapshots' = false ∧
  scope.ConfChanges' = false

/-- `InScope b1Scope` gives every bit `DrainB1` tests. -/
abbrev drainB1_of_inScope.law : Prop :=
  ∀ (m : H.Mode), InScope b1Scope m → DrainB1 b1Scope m

/-- The phases of a node goroutine (see the file header): before `start` (the node's memory not
built: a fresh node, or, B2, a killed one); between inputs; at a drain's loop head, the node at
`r₁`, reached from the view (`Reach`, at the fold's admissible configurations) over the sent
messages `net₀`, `xnet₀` (lower bounds of the invariant's), with the transfer messages `xs₁` the
input produced; after the drain. -/
inductive Phase where
  | down
  | idle
  | loop (net₀ : List Msg) (xnet₀ : List XMsg) (r₁ : RState) (xs₁ : List XMsg)
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
def viewFrag (γ : AntNames) (j : Fin γ.R.N) (v : AntSim.NodeView) : IProp GF :=
  ghostVar (γ.view j) (1 : Qp).half v

/-- **Node `j`'s goroutine may report** (exclusive; the invariant holds all of them once the run
is over). -/
def nodeLive (γ : AntNames) (j : Fin γ.R.N) : IProp GF := dghostVar (γ.live j) (DFrac.own 1) ()

/-- **`m` was sent** (persistent). -/
def sentW (γ : AntNames) (m : Msg) : IProp GF := iprop(∃ i : Nat, monoListIdxOwn γ.sent i m)

/-- **At least `net` was sent** (persistent). -/
def sentLb (γ : AntNames) (net : List Msg) : IProp GF := monoListLbOwn γ.sent net

/-- **The transfer message `x` was sent** (persistent). -/
def xsentW (γ : AntNames) (x : XMsg) : IProp GF := iprop(∃ i : Nat, monoListIdxOwn γ.xsent i x)

/-- **At least `xnet` was sent** (persistent). -/
def xsentLb (γ : AntNames) (xnet : List XMsg) : IProp GF := monoListLbOwn γ.xsent xnet

instance sentW_persistent (γ : AntNames) (m : Msg) : Persistent (sentW (GF := GF) γ m) := by
  unfold sentW; infer_instance

instance sentLb_persistent (γ : AntNames) (net : List Msg) :
    Persistent (sentLb (GF := GF) γ net) := by
  unfold sentLb; infer_instance

instance xsentW_persistent (γ : AntNames) (x : XMsg) : Persistent (xsentW (GF := GF) γ x) := by
  unfold xsentW; infer_instance

instance xsentLb_persistent (γ : AntNames) (xnet : List XMsg) :
    Persistent (xsentLb (GF := GF) γ xnet) := by
  unfold xsentLb; infer_instance

/-- **Raft's global facts `G`, as persistent ghost facts** (S4's `raftFactsOwn`; `G.logs` are
full logs, from index 1). -/
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

/-! ## The invariant -/

/-- **The run's invariant, open**: the stream (the invariant's half of `rec`), the `N` views (their
invariant halves), the sent lists (their authorities), the run's pure facts at `R` (`AntRun`,
`RaftLaws`, `GlobalOk`, each view's full log certified), and raft's facts. -/
def antOpen (γ : AntNames) : IProp GF :=
  iprop(∃ (evs : List AntCheck.Event) (S : AntCheck.State) (V : Fin γ.R.N → AntSim.NodeView)
      (net : List Msg) (xnet : List XMsg) (G : AntSim.RaftFacts),
    ghostVar γ.strm (1 : Qp).half evs ∗
    ([∗list] j ∈ List.finRange γ.R.N, ghostVar (γ.view j) (1 : Qp).half (V j)) ∗
    monoListAuthOwn γ.sent 1 net ∗ monoListAuthOwn γ.xsent 1 xnet ∗
    ⌜AntRun γ.R γ.dec evs S V net xnet ∧ AntSim.RaftLaws G ∧ AntSim.GlobalOk γ.R S net G ∧
      ∀ j : Fin γ.R.N, (V j).r.full ∈ G.logs⌝ ∗
    raftFactsOwn γ.raft.raftNames G)

/-- **The run's invariant** (`antN`): open, or over (every node's `live` token given up:
`RunCluster` took the stream out). -/
def antInv (γ : AntNames) : IProp GF :=
  iprop(antOpen γ ∨ [∗list] j ∈ List.finRange γ.R.N, nodeLive γ j)

/-! ## The network -/

/-- **An in-flight protocol message** `ml` at `st`, the protocol message `m`: owned, with its
receiver's premises (`NetFacts` at `R`), raft's certificate, its term within the budget, and sent. -/
def netMsg (γ : AntNames) (ml : Loc) (st : MsgSt) (m : Msg) : IProp GF :=
  iprop((∃ c : MsgC, msgPtsCC ml (DFrac.own 1) DFrac.discard (needsCap st.msg) c ∗
      ⌜c.model = st ∧ c.csUfNil⌝) ∗
    ⌜NetFacts γ.R st m⌝ ∗ □ isMessage γ.raft.raftNames m ∗ rnTermLB γ.raft st.msg.Term' ∗ sentW γ m)

/-- **An in-flight transfer message** `ml` at `st`, the `XMsg` `x`: owned, with its receiver's
premises (`XNetFacts`), its term within the budget, and sent. -/
def netXMsg (γ : AntNames) (ml : Loc) (st : MsgSt) (x : XMsg) : IProp GF :=
  iprop((∃ c : MsgC, msgPtsCC ml (DFrac.own 1) DFrac.discard (needsCap st.msg) c ∗
      ⌜c.model = st ∧ c.csUfNil⌝) ∗
    ⌜XNetFacts γ.R st x⌝ ∗ rnTermLB γ.raft st.msg.Term' ∗ xsentW γ x)

/-- **What makes a message sendable** (pure and persistent facts of its content `st`, `node.sendMsg`'s
premise): a forwarded proposal in a mode that does not forward it (`send` drops it), or an in-flight
protocol message's facts (`netMsg`'s), or an in-flight transfer message's (`netXMsg`'s). -/
def sendFacts (γ : AntNames) (st : MsgSt) : IProp GF :=
  iprop(⌜st.msg.Type' = MsgProp ∧ γ.mode.Forward' = false⌝ ∨
    (∃ m : Msg, ⌜NetFacts γ.R st m⌝ ∗ □ isMessage γ.raft.raftNames m ∗ rnTermLB γ.raft st.msg.Term' ∗
      sentW γ m) ∨
    (∃ x : XMsg, ⌜XNetFacts γ.R st x⌝ ∗ rnTermLB γ.raft st.msg.Term' ∗ xsentW γ x))

/-- **A message `Cluster.send` takes** (`node.sendMsg` hands it a clone of each message of a
`Ready`): owned, with its sendable facts. -/
def sendMsg (γ : AntNames) (ml : Loc) (st : MsgSt) : IProp GF :=
  iprop((∃ c : MsgC, msgPtsCC ml (DFrac.own 1) DFrac.discard (needsCap st.msg) c ∗
      ⌜c.model = st ∧ c.csUfNil⌝) ∗ sendFacts γ st)

/-- **A proposal's raft resources** (`RawNode.Propose`'s premises): the data's certificate and its
ticket, within raft's data bound. -/
def propOk (γ : AntNames) (data : List w8) : IProp GF :=
  iprop(propData γ.raft.raftNames (propEntryM data) ∗ entTk γ.raft.raftNames (propEntryM data) ∗
    ⌜∀ b, γ.raft.raftNames.maxData = some b → data.length ≤ b⌝)

/-- **The proposer's minting** (persistent): a proposal's resources for any data (raft's
`propMint.law` at the client log's invariant, `PropMint.lean`; `RunCluster` establishes it). -/
def propMinter (γ : AntNames) : IProp GF :=
  iprop(□ ∀ data : List w8, |={⊤}=> propOk γ data)

/-- **A read context handed out** (exclusive: the reader hands each context to one node, once):
`ReadIndex`'s premise in the driver. Raft's own read credit (`ReadIndex`'s `rdCred`, design §4) joins
this body when raft's spec of `ReadIndex` lands. -/
def readOk (γ : AntNames) (ctx : List w8) : IProp GF := authSetFrag γ.rctx ctx

/-- **The reader's contexts**: those handed out so far, `"r1" … "r(k-1)"` (the reader's counter at
`k`); the reader mints `readOk` for `"r<k>"` from it. -/
def readerOwn (γ : AntNames) (k : w64) : IProp GF :=
  authSetAuth γ.rctx (GMap.listToSet ((List.range (uint.nat k - 1)).map fun (i : Nat) =>
    (go!"r" ++ internal.strconv.fmtUint (W64 ((i : Int) + 1)) (W64 10) : List w8)))

/-- **An input to node `j`** (what `n.in` holds), by its kind (`driver.go`'s `in*` constants):
a message to it in flight (`inMsg`, 0); a proposal's data with its resources (`inProp`, 1); a read
with a fresh context (`inRead`, 3: reads on); a transfer to a node of the run (`inTransfer`, 4:
transfers on); a campaign (`inCampaign`, 5); an unreachable report about any id (`inUnreachable`,
7). The kinds of batches B2/B3 (`inConf` 2, `inSnapStatus` 6, `inSnapshot` 8, `inFlush` 9,
`inWork` 10, `inKill` 11) are not delivered in a run of B1's mask (their arms: `False`). -/
def inputOk (γ : AntNames) (j : Fin γ.R.N) (inp : H.input) : IProp GF :=
  iprop((⌜inp.kind' = W64 0⌝ ∗ ∃ (st : MsgSt),
      ((∃ m : Msg, netMsg γ inp.msg' st m ∗ ⌜m.dst = AntSim.nodeId j⌝) ∨
       (∃ x : XMsg, netXMsg γ inp.msg' st x ∗ ⌜x.dst = AntSim.nodeId j⌝))) ∨
    (⌜inp.kind' = W64 1⌝ ∗ ∃ data : List w8, inp.data' ↦*□ data ∗ propOk γ data) ∨
    (⌜inp.kind' = W64 3 ∧ γ.mode.Reads' = true⌝ ∗ ∃ ctx : List w8, inp.data' ↦*□ ctx ∗ readOk γ ctx) ∨
    (⌜inp.kind' = W64 4 ∧ γ.mode.Transfer' = true ∧ ∃ i : Fin γ.R.N, inp.to' = AntSim.nodeId i⌝) ∨
    ⌜inp.kind' = W64 5⌝ ∨ ⌜inp.kind' = W64 7⌝)

/-! ## The cluster -/

/-- **Node `j`'s read-only record** (persistent): `n` is the node of id `j + 1` of the cluster
`c`, its name, its input channel (a bag of `inputOk` inputs), its disk's pointer, and its logger's
cell `autoLeft` (in an invariant: raft calls the node's logger, `nodeLogger.Infof`, which counts
automatic leavings of a joint configuration there, from inside its own calls). -/
def nodeRO (c : Loc) (γ : AntNames) (n : Loc) (j : Fin γ.R.N) : IProp GF :=
  iprop(∃ (ch d : Loc), n.[H.node, go!"c"] ↦□ c ∗ n.[H.node, go!"id"] ↦□ AntSim.nodeId j ∗
    n.[H.node, go!"name"] ↦□ AntSim.nameOf (AntSim.nodeId j) ∗ n.[H.node, go!"in"] ↦□ ch ∗
    isChanBag (γ.inCh j) ch (inputOk γ j) ∗ n.[H.node, go!"disk"] ↦□ d ∗
    inv antLogN (∃ k : w64, n.[H.node, go!"autoLeft"] ↦ k))

/-- The `down` lock's invariant (`Cluster.mu`): which node goroutines have stopped (B2's
restarter reads it; in a run without restarts nothing is ever down). -/
def downInv (c : Loc) (γ : AntNames) : IProp GF :=
  iprop(∃ (dsl : GoSlice) (ds : List Bool), c.[H.Cluster, go!"down"] ↦ dsl ∗ dsl ↦* ds ∗
    ⌜ds.length = γ.R.N ∧ (γ.mode.Restarts' = false → ∀ b ∈ ds, b = false)⌝)

/-- **The cluster `c` of the run `γ`** (persistent): its pacing (`CfgOk`), the run's scope, mode
and configuration related (`InScope`, `ModeRun`), its recorder, its `N` nodes (`clusterRO`, each
`nodeRO`), its stop channel (broadcast), the network's join, the `down` lock, the run's invariant,
the receipts' fit, the proposer's minting, and raft's ghost names' static facts as `nodeRaft`
needs them. -/
def antCluster (c : Loc) (γ : AntNames) : IProp GF :=
  iprop(∃ (cfg : H.Config) (r : Loc) (ns : List Loc) (stop : Loc),
    c.[H.Cluster, go!"cfg"] ↦□ cfg ∗ ⌜CfgOk cfg⌝ ∗
    ⌜InScope γ.scope γ.mode ∧ ModeRun γ.scope γ.mode γ.R⌝ ∗
    c.[H.Cluster, go!"rec"] ↦□ r ∗ isRecorder γ.strm r ∗
    clusterRO c ns γ.mode ∗
    ([∗list] j ∈ List.finRange γ.R.N, nodeRO c γ ns[j.val]! j) ∗
    c.[H.Cluster, go!"stop"] ↦□ stop ∗ ownBroadcastChan stop γ.stopCh iprop(True) .Unknown ∗
    isNetJoin antNetN (c.[H.Cluster, go!"netWg"]) γ.net ∗
    sync.isMutex (c.[H.Cluster, go!"mu"]) (downInv c γ) ∗
    inv antN (antInv γ) ∗ ⌜antRunFits GF⌝ ∗ propMinter γ)

/-- **A share `q` of the right to add network goroutines** (`netWg`). -/
def netAdder (c : Loc) (γ : AntNames) (q : Qp) : IProp GF :=
  njAdder antNetN (c.[H.Cluster, go!"netWg"]) γ.net q

/-- **The run is over** (`RunCluster`'s post, `Main`'s and `Cluster.Events`' premise): the
cluster's recorder and its final stream, accepted by the checker at the configuration `R` of the
mode drawn within the scope `s`, within `check.Run`'s bounds. -/
def runOver (c : Loc) (s : H.Scope) : IProp GF :=
  iprop(∃ (r : Loc) (γr : GName) (evs : List AntCheck.Event) (m : H.Mode) (R : AntSim.RunCfg),
    c.[H.Cluster, go!"rec"] ↦□ r ∗ isRecorder γr r ∗ recDone γr evs ∗
    c.[H.Cluster, go!"mode"] ↦□ m ∗
    ⌜InScope s m ∧ ModeRun s m R ∧ AntCheck.Accepts R.cfg evs ∧ AntCheck.Stream.Bounded evs ∧
      AntCheck.Stream.ConfBounded R.cfg evs⌝)

/-! ## A node goroutine's state -/

/-- **Node `j`'s raft ghost state the driver's calls take** (S4's `nodeRaft` at `R`): its
generation view and free batch slot, its durable state's ghost, its term ceiling within the budget,
the budget; the cluster's static facts: untraced, the configuration the initial voters, no bound on
proposed data, the bootstrapped run's entry as the boot log, raft's namespace outside the driver's. -/
def nodeRaft (γ : AntNames) (j : Fin γ.R.N) (rs : RNState) : IProp GF :=
  iprop(∃ (x : CrashNames) (g : Nat),
    genView γ.raft.raftNames (AntSim.nodeId j) x 1 g ∗ slotFree γ.raft.raftNames (AntSim.nodeId j) g ∗
    ownDurGhost γ.raft.raftNames (AntSim.nodeId j) rs.dur ∗ rnTermLB γ.raft rs.tc ∗
    rnBudget γ.raft ∗
    ⌜γ.raft.raftNames.reTrace = none ∧ γ.raft.raftNames.reCfg = γ.R.voters0 ∧
      γ.raft.raftNames.maxData = none ∧ γ.raft.raftNames.reBoot = AntSim.bootLog γ.R ∧
      (↑(raftN γ.raft.raftNames) : CoPset) ⊆ ⊤ \ ↑antN⌝)

/-- **The cell of the handled message's report** (`n.cause` at `cl`, `reportCause`'s): `nil` with
nothing to report (`o = none`), or the report `m` of the message being handled, not yet recorded
(`o = some (recvEvM m)`). -/
def pendingCause (cl : Loc) (o : Option AntCheck.Event) : IProp GF :=
  iprop((⌜cl = null ∧ o = none⌝) ∨
    (∃ (g : AntCheck.G.Msg) (m : AntCheck.Msg), ⌜cl ≠ null ∧ o = some (recvEvM m)⌝ ∗ cl ↦ g ∗
      AntCheck.msgRO g m))

/-- **The cause cell against the view** (S4's `causeOwn` at `Fin R.N`): while the drain's `recv` is
not reported, the report of the handled message (`pendingCause`), sent, with its receipts;
otherwise `nil`. -/
def causeOwn (γ : AntNames) (j : Fin γ.R.N) (v : AntSim.NodeView) (cl : Loc) : IProp GF :=
  if v.byE = go!"recv" ∧ v.told = false then
    iprop(∃ m : Msg, ⌜v.cause = some m ∧ m.dst = AntSim.nodeId j ∧
        (AntSim.evRecv (AntSim.nodeId j) m).NumsOk⌝ ∗
      pendingCause cl (some (recvEvM (AntSim.msgOf m (AntSim.nodeId j)))) ∗ sentW γ m ∗
      ⧗ (AntSim.evRecv (AntSim.nodeId j) m).weight)
  else pendingCause cl none

/-- **A node may report** (`emit`'s fields): not dead, no kill due. In a run without restarts
these never change. -/
def emitOk (n : Loc) : IProp GF :=
  iprop(n.[H.node, go!"dead"] ↦ false ∗ n.[H.node, go!"fuse"] ↦ W64 0)

/-- **The `RawNode`'s record against the view** (pure; S4's `RsView` over the disk): the client
record's last reported hard state and durable log are the node's disk (`v.dur`, C1), what it handed
out is the view's delivered and unreported committed entries, nothing queued or unpersisted, not
following a snapshot. -/
def RsView (rs : RNState) (v : AntSim.NodeView) : Prop :=
  rs.phs = HardStateM.mk v.dur.term v.dur.vote v.dur.commit ∧ rs.dur.ents = v.dur.log ∧
  rs.delivered = v.delivered ++ v.ce ∧ rs.steps = [] ∧ rs.unpersisted = [] ∧ rs.flw = false

/-- **Node `j`'s disk** (`n.disk` at `d`, `harness.go`'s `disk`): the hard state and the entries of
the binding's disk `w` (`DurW`, from index 1), no snapshot (batch B3's). -/
def diskOwn (d : Loc) (w : AntSim.DurW) : IProp GF :=
  iprop(∃ (hsl : Loc) (esl : GoSlice),
    d.[H.disk, go!"hs"] ↦ hsl ∗ hsRO hsl (HardStateM.mk w.term w.vote w.commit) ∗
    d.[H.disk, go!"snap"] ↦ null ∗ d.[H.disk, go!"ents"] ↦ esl ∗ entsPts esl DFrac.discard w.log ∗
    ownSliceCap Loc esl (DFrac.own 1))

/-- A hard state pointer that may be `nil` (`disk.save`'s and `storeSave`'s `hs`): `nil` for none,
or read-only at `h`. -/
def hsOptRO (hp : Loc) (oh : Option HardStateM) : IProp GF :=
  iprop((⌜hp = null ∧ oh = none⌝) ∨ (∃ h : HardStateM, ⌜hp ≠ null ∧ oh = some h⌝ ∗ hsRO hp h))

/-- Go `disk.save(hs, ents)` on the binding's disk `w` (no snapshot): the hard state if any, and the
entries replacing the log from the first one's index on. -/
def saveW (w : AntSim.DurW) (oh : Option HardStateM) (es : List EntryM) : AntSim.DurW :=
  let w1 := match oh with
    | none => w
    | some h => { w with term := h.Term', vote := h.Vote', commit := h.Commit' }
  match es with
  | [] => w1
  | e :: _ => { w1 with log := w1.log.take (uint.nat e.Index' - 1) ++ es }

/-- A write `disk.save` takes without panicking: its entries continue the log (from index 1). -/
def SaveOk (w : AntSim.DurW) (es : List EntryM) : Prop :=
  ∀ e ∈ es.head?, 1 ≤ uint.nat e.Index' ∧ uint.nat e.Index' - 1 ≤ w.log.length

/-- **Node `j`'s B2/B3 bookkeeping** (`node`'s fields of batching, async storage, snapshots,
membership and kills), at their values in a run of B1's mask: nothing batched, queued, applying or
restoring, no configuration switched, no kill due. (B2/B3 widen this body.) -/
def nodeMemB1 (n : Loc) : IProp GF :=
  iprop(∃ (mhs rhs : Loc),
    n.[H.node, go!"items"] ↦ W64 0 ∗ n.[H.node, go!"mhs"] ↦ mhs ∗ n.[H.node, go!"rhs"] ↦ rhs ∗
    n.[H.node, go!"writes"] ↦ slice.nil ∗ n.[H.node, go!"inflight"] ↦ false ∗
    n.[H.node, go!"applies"] ↦ slice.nil ∗ n.[H.node, go!"applying"] ↦ false ∗
    n.[H.node, go!"restoring"] ↦ W64 0 ∗ n.[H.node, go!"wip"] ↦ null ∗ n.[H.node, go!"aip"] ↦ null ∗
    n.[H.node, go!"confs"] ↦ slice.nil ∗ n.[H.node, go!"confBase"] ↦ W64 0 ∗
    emitOk n)

/-- **Node `j`'s goroutine's state** at `n`, its view `v`, the phase `ph` (see the file header):
always its disk at `v.dur`, its B2/B3 bookkeeping, the view fragment and the right to report, its
entries normal; and, once started (any phase but `down`), the `RawNode` and its raft ghost state,
its `MemoryStorage` (`nodeStor`: at the disk's hard state, in the `bootStorage` raft reads, with the
run's initial voters), the Go fields agreeing with the view (`role` the last reported role, `hs` the
disk's hard state, `conf` the initial voters' configuration (no conf change in B1's mask), `applied` the delivered prefix), the
`RawNode`'s node constant the run's node flags (`rs.k = γ.R.k j`: the ends `RawNode` gives are at `rs.k`, the Sim's
inputs at `R.k j`), the
cause cell; and the phase's facts (S4's, over `RState`):
- `down`: not running (`v.alive = false`), nothing of a `Ready` left, the disk the node's state's
  (`SyncDisk`);
- `idle`: running, nothing of a `Ready` left, the node at the view's state, idle (`PIdle`), its
  in-progress boundary at the log's end, the cause cell `nil`;
- `loop net₀ xnet₀ r₁ xs₁`: the node at `r₁`, reached from the view, nothing queued, the boundary at the
  common prefix of the view's log and `r₁`'s, the drain's `by` one of the driver's;
- `drained`: as `idle`, but the cause cell as `causeOwn`. -/
def nodeOwn (c : Loc) (γ : AntNames) (j : Fin γ.R.N) (n : Loc) (v : AntSim.NodeView) (ph : Phase) :
    IProp GF :=
  iprop(∃ (d rn ms hsl cl csl : Loc) (role : GoString) (applied : w64),
    n.[H.node, go!"disk"] ↦□ d ∗ nodeMemB1 n ∗
    n.[H.node, go!"rn"] ↦ rn ∗ n.[H.node, go!"store"] ↦ ms ∗ n.[H.node, go!"role"] ↦ role ∗
    n.[H.node, go!"hs"] ↦ hsl ∗ n.[H.node, go!"cause"] ↦ cl ∗ n.[H.node, go!"applied"] ↦ applied ∗
    n.[H.node, go!"conf"] ↦ csl ∗
    viewFrag γ j v ∗ nodeLive γ j ∗ ⌜ViewNormal v⌝ ∗
    match ph with
    | .down => iprop(⌜v.alive = false ∧ v.Idle ∧ v.dur = AntSim.durOf v.r ∧ AntSim.PInitR γ.R v.r⌝ ∗
        diskOwn d ⟨W64 0, W64 0, W64 0, []⟩)
    | _ => iprop(diskOwn d v.dur ∗ ∃ (si : Loc) (rs : RNState) (qs : List Msg) (ip : Nat) (r : RState),
      nodeStor si ms ((List.range γ.R.K).map fun (i : Nat) => W64 ((i : Int) + 1))
        (HardStateM.mk v.dur.term v.dur.vote v.dur.commit) ∗
      ⌜rs.storage = interface.ok ⟨go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.bootStorage.ty, #si⟩⌝ ∗
      rawNode γ.raft.raftNames rn (AntSim.nodeId j) rs r qs ip ∗ nodeRaft γ j rs ∗
      ⌜RsView rs v ∧ v.alive = true ∧ role = AntSim.roleS v ∧ uint.nat applied = v.delivered.length ∧
        rs.k = γ.R.k j⌝ ∗
      hsRO hsl (HardStateM.mk v.dur.term v.dur.vote v.dur.commit) ∗
      csPts csl DFrac.discard
        (ConfStateM.mk ((List.range γ.R.K).map fun (i : Nat) => W64 ((i : Int) + 1)) [] [] [] false) false ∗
      ⌜v.conf = γ.R.c0⌝ ∗
      match ph with
      | .down => iprop(False)
      | .idle => iprop(⌜v.Idle ∧ r = v.r ∧ qs = [] ∧ ip = v.r.p.log.length ∧ PIdle rs r.p ∧
          cl = null⌝)
      | .loop net₀ xnet₀ r₁ xs₁ => iprop(⌜r = r₁ ∧
          AntSim.Reach γ.R γ.dec (AdmFold γ.dec γ.R.c0) net₀ xnet₀ j v r₁ ∧ qs = [] ∧
          ip = lcpLen v.r.p.log r₁.p.log ∧ ByOk v.byE⌝ ∗ sentLb γ net₀ ∗ xsentLb γ xnet₀ ∗
          causeOwn γ j v cl)
      | .drained => iprop(⌜v.Idle ∧ r = v.r ∧ qs = [] ∧ ip = v.r.p.log.length ∧ PIdle rs r.p⌝ ∗
          causeOwn γ j v cl)))

/-- **What a node goroutine gives back at its end** (`nodesWg.Done()`): its right to report and
its share of the network's adders. -/
def nodeExit (c : Loc) (γ : AntNames) (j : Fin γ.R.N) (q : Qp) : IProp GF :=
  iprop(nodeLive γ j ∗ netAdder c γ q)

/-! ## Laws of the node's tokens and views (statements; proved with the invariant, B1 phase 2) -/

/-- The run is not over while a node goroutine holds its `live` token. -/
abbrev nodeLive_over.law : Prop :=
  ∀ (γ : AntNames) (j : Fin γ.R.N),
    nodeLive (GF := GF) γ j ∗ ([∗list] k ∈ List.finRange γ.R.N, nodeLive γ k) ⊢ False

/-- **Node `j`'s view updated**: the goroutine's half and the invariant's agree, and both move. -/
abbrev view_update.law : Prop :=
  ∀ (E : CoPset) (γ : AntNames) (j : Fin γ.R.N) (V : Fin γ.R.N → AntSim.NodeView)
    (v v' : AntSim.NodeView),
    viewFrag (GF := GF) γ j v ∗ ([∗list] k ∈ List.finRange γ.R.N, ghostVar (γ.view k) (1 : Qp).half (V k)) ⊢
      |={E}=> ⌜V j = v⌝ ∗ viewFrag γ j v' ∗
        [∗list] k ∈ List.finRange γ.R.N, ghostVar (γ.view k) (1 : Qp).half (AntSim.setV V j v' k)

end defs

end AntHarness
end EtcdGrove
end Perennial
