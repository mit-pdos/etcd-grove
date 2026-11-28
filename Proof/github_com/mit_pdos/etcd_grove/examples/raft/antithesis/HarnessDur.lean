/-
Lean-first (no Rocq counterpart).

# The parity driver's state under batch B2's mask (#33 parity B2, statements)

`notes/antithesis-parity-design.md` §3.2 (the node's disk `dur`, `undo`, `made`, the queue `mems`), §4
(restart, the vacate law, async storage writes), §6.1 (E1), over the driver's durability paths
(`examples/raft/antithesis/{driver,node}.go`: `restarter`, `restart`, the death exit of `run`, `emit`'s
fuse, `flusher`/`flush`/`note`, `storage`/`work`/`drainAsync`/`runWrite`/`doneWrite`/`runApply`/
`doneApply`, `parallel`, `parts`' split). **Round 1: statements only.** Each definition here is the
future body of the B1 definition of the same name without the suffix (`HarnessRun.lean`): when B2's
proofs replace B1's, `nodeOwnB2` becomes `nodeOwn`, `antClusterB2` `antCluster`, `inputOkB2`
`inputOk`, ..., and the B1 names' unchanged helpers (`sendEv`, `stateEv`, `applyCommitted`, ...) keep
their specs' text. What changes from B1:

- **Liveness is a share** (`runLive γ q`, one ghost name `AntNamesB2.liveR`) carried by each node
  goroutine *outside* its node state (`nodeExitB2`): a killed goroutine's `nodesWg.Done` gives its share
  back while its node state waits in the `mu` lock (`downInvB2`) for the restarter, which splits a fresh
  share for the restarted goroutine from its own (`restarterOwn`). The run is over at `runLive γ 1`.
- **The disk is the view's disk or its undo** (`DiskRel`): a kill between a write's announcement and
  the write leaves the disk at `v.undo` with `v.made = false` (B 349-359; `boot`'s `Recovered`).
- **raft's durable ghost is at the disk** (`ownDurGhost γ id D`, `StorageHolds D (diskContents dk)`),
  not at the `RawNode`'s `rs.dur`: the queued write jobs carry the `Ready`s' enter promises
  (`jobEnter`, `RawNode.Ready.form`'s `Henter` shape), chained from `D` to `rs.dur`, each fired at its
  `saveDisk`.
- **The bookkeeping fields** (`nodeMemB2`): the batch's `items`, `mhs`/`rhs`, the write queue
  (`writeJobOwn`, `wip`, `inflight`), the apply queue (`applyJobOwn`, `aip`, `applying`); `restoring`,
  `confs`, `confBase` at their B3-off values; the kill fields (`killOwn`). The queue against the view's
  `mems` (`QueueView`).
- **A dead node** (`n.dead`): its view frozen at its last report, its raft resources kept for the
  vacate; every function on a dead node leaves it dead (`nodeOwnB2`'s `dead` arm).
- **The phases**: `idle` holds a waiting `Ready` in batch mode (for the flusher) and a queue in async
  mode (for the storage goroutine); `down` gains the killed node (`restartRaft`: what the vacate law
  gives back, at the disk).
- **A storage step in progress** (round 2): `nodeOwnB2H`'s `hole` (`WorkHole`), the job `work` holds
  between its dequeue and its record (the specs of `runWrite`, `doneWrite`, `runApply`, `doneApply`);
  `nodeOwnB2` is `nodeOwnB2H … none`. A run write job's enter promise is spent (`writeJobMade`).
- **The inputs** (`inputOkB2`): flush (9, batch), work (10, async), kill (11, restarts), no resources.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessRun
public import Proof.go_etcd_io.raft.v3.RawNodeStartApi
public import Perennial.Proof.sync.WaitGroupTokJoin
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.StmtsB2

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section types
variable [GooseExts]

abbrev H.writeJob := github_com.mit_pdos.etcd_grove.examples.raft.antithesis.writeJob
abbrev H.applyJob := github_com.mit_pdos.etcd_grove.examples.raft.antithesis.applyJob

end types

/-! ## Pure parts -/

section pure
variable [GooseExts]

/-- **Batch B2's mask** (`antithesis-parity-plan.md` §3, B2): B1's and durability (restarts,
batching, parallel writes); AsyncStorageWrites and split writes staged to B2.5; forwarding and B3's
features off. -/
def b2Scope : H.Scope :=
  { b1Scope with Restarts' := true, Batch' := true, Parallel' := true }

/-- **The masked-off bits a node's input paths test under B2's mask** (B1's `DrainB1`, its B2 bits
lifted): no snapshots and no snapshot reports (`drain`'s and `drainAsync`'s snapshot branches,
`sent`), no conf changes, no forwarding; the split order `none` or `splitTermEntriesCommit`. -/
def DrainB2 (scope : H.Scope) (mode : H.Mode) : Prop :=
  mode.SnapStatus' = false ∧ scope.Snapshots' = false ∧ scope.ConfChanges' = false ∧
  scope.Forwarding' = false ∧ (mode.Split' = W64 0 ∨ mode.Split' = W64 1)

/-- `InScope b2Scope` gives every bit `DrainB2` tests. -/
abbrev drainB2_of_inScope.law : Prop :=
  ∀ (m : H.Mode), InScope b2Scope m → DrainB2 b2Scope m

/-- A drain's `by` under B2 (`node.go`): B1's, and the batch's Ready (`"batch"`), the storage
goroutine's steps (`"write"`, `"apply"`). -/
def ByOkB2 (b : AntCheck.Str) : Prop :=
  ByOk b ∨ b = go!"batch" ∨ b = go!"write" ∨ b = go!"apply"

/-- **The disk against the view** (design §3.2): the view's disk (the last announced write, made), or,
while that write is announced and not made, the disk before it (`undo`, B 349-359). -/
def DiskRel (v : AntSim.NodeView) (dk : AntSim.DurW) : Prop :=
  dk = v.dur ∨ (v.undo = some dk ∧ v.made = false)

/-- **What `memoryOf` builds raft's storage from** (`StorContents`): the disk's hard state and its log
from `base0`, no snapshot (B3's). -/
def diskContents (dk : AntSim.DurW) : StorContents :=
  ⟨HardStateM.mk dk.term dk.vote dk.commit, none, base0, dk.log⟩

/-- A disk with nothing written (a fresh node's, before `start`). -/
def emptyDisk : AntSim.DurW := ⟨W64 0, W64 0, W64 0, []⟩

/-- **A write job** (`writeJob`, rawnode's `Write`): the hard state to write (`none`: none), the
entries, the hard state on disk after it, the messages waiting for it (`resp`: raft's held
responses, its self-addressed storage acknowledgement, and the driver's held `MsgVote`s, E1), the
report of the message the `Ready` answered, the `by` of its reports, whether there is something to
write, the batch's `mem` count (`-1`: not a batch's); and raft's durable state before and after it
(`pre`, `post`: the enter promise's, `jobEnter`). No snapshot (B3's). -/
structure WJob where
  hs : Option HardStateM
  ents : List EntryM
  after : HardStateM
  resp : List MsgSt
  cause : Option AntCheck.Msg
  byE : AntCheck.Str
  writes : Bool
  k : Int
  pre : RaftState
  post : RaftState

/-- **An apply job** (`applyJob`, rawnode's `Apply`): the committed entries, the messages raft steps
after them (its storage acknowledgement), the `by`. No restore (B3's). -/
structure AJob where
  ents : List EntryM
  resp : List MsgSt
  byE : AntCheck.Str

/-- (#33 parity B2 round 2) **A storage job `work` holds between its dequeue and its record** (its
four arms; `node.go`'s `work`): the oldest write job dequeued (`inflight` set) and not yet run, held at
`l` (`runWrite`'s); the write job made, held at `l` (`wip` cleared, `inflight` still set: `doneWrite`'s);
the oldest apply job dequeued (`applying` set), held at `l` (`runApply`'s); the apply job applied, held
at `l` (`aip` cleared: `doneApply`'s). Outside a storage step there is none (`nodeOwnB2`). -/
inductive WorkHole where
  | runW (l : Loc)
  | doneW (l : Loc)
  | runA (l : Loc)
  | doneA (l : Loc)

/-- The write job out of the queue is held by `work` (not in `wip`). -/
def WorkHole.wHeld : Option WorkHole → Bool
  | some (.runW _) | some (.doneW _) => true
  | _ => false

/-- The apply job out of the queue is held by `work` (not in `aip`). -/
def WorkHole.aHeld : Option WorkHole → Bool
  | some (.runA _) | some (.doneA _) => true
  | _ => false

/-- The write job out of the queue is not yet run: its report not made, its write not entered. -/
def WorkHole.wFresh : Option WorkHole → Bool
  | some (.runW _) => true
  | _ => false

/-- How many `mem` reports of the queue a write job stands for: a batch's `k`; otherwise one if it
writes (its `mem` report had `w = 1`), none if it only carries responses. -/
def WJob.mems (w : WJob) : Nat :=
  if 0 ≤ w.k then w.k.toNat else if w.writes then 1 else 0

/-- **The queue against the view** (design §3.3 `QueueIs`, the harness's half): the view's announced,
unwritten states are the queued jobs', oldest first, then the batch's `items` not yet in a job; a
job that is not a batch's and writes is its `mem` report's record (`after`'s hard state, the entries).
The job in flight (`wip`) has left the queue (its `write`/`net` report popped it); a job dequeued and
not yet run (`WorkHole.runW`) is still its head (the caller passes it first in `jobs`). -/
def QueueView (v : AntSim.NodeView) (jobs : List WJob) (items : Nat) : Prop :=
  v.mems.length = (jobs.map WJob.mems).sum + items ∧
  ∀ (i : Nat) (w : WJob), jobs[i]? = some w → w.k < 0 → w.writes = true →
    ∃ mr ∈ v.mems[(jobs.take i |>.map WJob.mems).sum]?,
      mr.term = w.after.Term' ∧ mr.vote = w.after.Vote' ∧ mr.commit = w.after.Commit' ∧ mr.ents = w.ents

/-- **The enter promises chain**: the durable state on disk `D` is the first unentered job's `pre`
(the job in flight's write is entered at its `saveDisk`), each job's `post` the next one's `pre`, the
last one's `post` the `RawNode`'s durable state; a job with nothing to write enters nothing. -/
def JobsChain (D : RaftState) (jobs : List WJob) (dur : RaftState) : Prop :=
  match jobs with
  | [] => D = dur
  | w :: ws => w.pre = D ∧ (w.writes = false → w.post = w.pre) ∧ JobsChain w.post ws dur

/-- Go `flush` report (`flushes`): `more` from the second on. -/
def flushEvM (more : Bool) : AntCheck.Event :=
  { e := go!"flush", node := [], more := some (if more then 1 else 0) }

/-- `flushes(k)`'s reports. -/
def flushEvs (k : Nat) : List AntCheck.Event := (List.range k).map fun i => flushEvM (decide (0 < i))

/-- Go `n.causeSendEv(by, m, cause)` of a message holding `st` (async: `cause` the message its
`Ready` answered, the empty list for none). -/
def causeSendEvM (by_ : AntCheck.Str) (st : MsgSt) (cause : Option AntCheck.Msg) : AntCheck.Event :=
  { sendEvM by_ st with cause := some cause.toList }

/-- Go `n.batchSendEv(by, m)`: `sendEv`'s with `b = 1`. -/
def batchSendEvM (by_ : AntCheck.Str) (st : MsgSt) : AntCheck.Event :=
  { sendEvM by_ st with b := true }

/-- Go `isRequest(m)`: an append request or a heartbeat (what `parallel` sends before the write). -/
def isRequestTy (t : w32) : Bool := decide (t = MsgApp) || decide (t = MsgHeartbeat)

/-- **The run's relation under B2** (`AntRun`'s, over B2's refinement relation `AntSimD`). -/
def AntRunD (R : AntSim.RunCfg) (dec : CCDec) (evs : List AntCheck.Event) (S : AntCheck.State)
    (V : Fin R.N → AntSim.NodeView) (net : List Msg) (xnet : List XMsg) : Prop :=
  AntSim.Prefix R.cfg evs S ∧ AntSim.AntSimD R dec S V net xnet ∧ AntCheck.Stream.Bounded evs ∧
    AntCheck.Stream.ConfBounded R.cfg evs ∧ ∀ ev ∈ evs, ev.ChgOk 0

end pure

/-! ## Ghost names and resources -/

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]

/-- **B2's ghost names**: B1's and the run's liveness (`liveR`, shared by the node goroutines and the
restarter). (At the unification, a field of `AntNames`.) -/
structure AntNamesB2 extends AntNames where
  liveR : GName

/-- **A share `q` of the run's liveness**: the run is not over while any share is out of the
invariant (`antInvB2`). -/
def runLive (γ : AntNamesB2) (q : Qp) : IProp GF := dghostVar γ.liveR (DFrac.own q) ()

/-- **The run's invariant under B2, open** (`antOpen`'s, its relation `AntRunD`). -/
def antOpenB2 (γ : AntNames) : IProp GF :=
  iprop(∃ (evs : List AntCheck.Event) (S : AntCheck.State) (V : Fin γ.R.N → AntSim.NodeView)
      (net : List Msg) (xnet : List XMsg) (G : AntSim.RaftFacts),
    ghostVar γ.strm (1 : Qp).half evs ∗
    ([∗list] j ∈ List.finRange γ.R.N, ghostVar (γ.view j) (1 : Qp).half (V j)) ∗
    monoListAuthOwn γ.sent 1 net ∗ monoListAuthOwn γ.xsent 1 xnet ∗
    ⌜AntRunD γ.R γ.dec evs S V net xnet ∧ AntSim.RaftLaws G ∧ AntSim.GlobalOk γ.R S net G ∧
      ∀ j : Fin γ.R.N, (V j).r.full ∈ G.logs⌝ ∗
    raftFactsOwn γ.raft.raftNames G)

/-- **The run's invariant under B2**: open, or over (the whole liveness given up). -/
def antInvB2 (γ : AntNamesB2) : IProp GF :=
  iprop(antOpenB2 γ.toAntNames ∨ runLive γ 1)

/-- **An input to node `j` under B2** (`n.in`'s): B1's arms, and the flusher's (`inFlush`, 9: batching
on), the storage goroutine's (`inWork`, 10: async on), the restarter's kill (`inKill`, 11: restarts
on); none carries resources. (`inConf`, `inSnapStatus`, `inSnapshot`: B3's, not delivered.) -/
def inputOkB2 (γ : AntNamesB2) (j : Fin γ.R.N) (inp : H.input) : IProp GF :=
  iprop(inputOk γ.toAntNames j inp ∨
    ⌜inp.kind' = W64 9 ∧ γ.mode.Batch' = true⌝ ∨ ⌜inp.kind' = W64 10 ∧ γ.mode.Async' = true⌝ ∨
    ⌜inp.kind' = W64 11 ∧ γ.mode.Restarts' = true⌝)

/-- **Node `j`'s read-only record under B2** (`nodeRO`, its channel's inputs `inputOkB2`). -/
def nodeROB2 (c : Loc) (γ : AntNamesB2) (n : Loc) (j : Fin γ.R.N) : IProp GF :=
  iprop(∃ (ch d : Loc), n.[H.node, go!"c"] ↦□ c ∗ n.[H.node, go!"id"] ↦□ AntSim.nodeId j ∗
    n.[H.node, go!"name"] ↦□ AntSim.nameOf (AntSim.nodeId j) ∗ n.[H.node, go!"in"] ↦□ ch ∗
    isChanBag (γ.inCh j) ch (inputOkB2 γ j) ∗ n.[H.node, go!"disk"] ↦□ d ∗
    inv antLogN (∃ k : w64, n.[H.node, go!"autoLeft"] ↦ k))

/-- **The kill fields** (`n.dead`, `n.fuse`). `emitOk n` is `killOwn n false 0`. -/
def killOwn (n : Loc) (dead : Bool) (fuse : w64) : IProp GF :=
  iprop(n.[H.node, go!"dead"] ↦ dead ∗ n.[H.node, go!"fuse"] ↦ fuse)

/-- `emit`'s step on the kill fields (`node.go`'s `emit`): dead, nothing recorded; a fuse that burns
out kills, nothing recorded; otherwise recorded. The result: recorded, and the fields after. -/
def emitStep (dead : Bool) (fuse : w64) : Bool × Bool × w64 :=
  if dead then (false, true, fuse)
  else if uint.Z fuse > 0 then
    (if fuse - W64 1 = W64 0 then (false, true, W64 0) else (true, false, fuse - W64 1))
  else (true, false, fuse)

/-- `reportCause`'s step on the kill fields: with a cause to report, `emit`'s (`emitStep`); with none,
nothing happens (`true`: the caller's `Q` at once). -/
def causeStep (o : Option AntCheck.Event) (dead : Bool) (fuse : w64) : Bool × Bool × w64 :=
  if o.isSome then emitStep dead fuse else (true, dead, fuse)

/-- **The reports `evs` then `Q`, or, if the node died on the way** (`emit`'s fuse), what is left of
them: a suffix not recorded, still to be given back to the run's invariant. -/
def reportsOrDead (γr : GName) (dead : Bool) (evs : List AntCheck.Event) (Q : IProp GF) : IProp GF :=
  if dead then iprop(∃ k : Nat, ⌜k ≤ evs.length⌝ ∗ reports γr (evs.drop k) Q) else Q

/-- **A message pointer that may be `nil`, read-only** (a write job's `cause`): `nil` for none, or a
report's message. -/
def causeRO (cl : Loc) (o : Option AntCheck.Msg) : IProp GF :=
  iprop((⌜cl = null ∧ o = none⌝) ∨
    (∃ (g : AntCheck.G.Msg) (m : AntCheck.Msg), ⌜cl ≠ null ∧ o = some m⌝ ∗ cl ↦□ g ∗ AntCheck.msgRO g m))

/-- **A `Ready`'s enter promise, kept by its write job** (`RawNode.Ready.form`'s `Henter`, from the
job's `pre` to its `post`): fired at the job's `saveDisk`, it moves raft's durable ghost and certifies
the messages that waited for the write. (The raft helper's async `Ready` spec states it per `Ready`,
without the batch slot: several `Ready`s queue before the first write is entered.) -/
def jobEnter (γ : RaftNames) (id : w64) (x : CrashNames) (g : Nat) (w : WJob) : IProp GF :=
  iprop(∀ (E : CoPset) (q' : Qp), ⌜↑(raftN γ) ⊆ E⌝ -∗ notCrashed -∗
    ownDurGhost γ id w.pre ∗ genView γ id x q' g ={E}=∗
      notCrashed ∗ ownDurGhost γ id w.post ∗ genView γ id x q' g ∗ [∗list] st ∈ w.resp, isRaftMsg γ id st)

/-- (#33 parity B2 round 2) **A message a storage job holds for after it** (`resp`): one to the node
itself (`id`: a storage acknowledgement, or raft's own vote) owned, as `RawNode.Step` takes it
(`doneWrite`/`doneApply` step it back); one to another node frozen, as `node.sendMsg` takes it. -/
def jobMsg (id : w64) (ml : Loc) (st : MsgSt) : IProp GF :=
  if st.msg.To' = id then
    iprop(∃ c : MsgC, msgPtsCC ml (DFrac.own 1) DFrac.discard (needsCap st.msg) c ∗ ⌜c.model = st ∧ c.csUfNil⌝)
  else iprop(∃ cap : Bool, msgPtsC ml DFrac.discard DFrac.discard cap st)

/-- **A write job's Go object** at `l` (`writeJob`) of node `id`, its fields. -/
def writeJobObj (id : w64) (l : Loc) (w : WJob) : IProp GF :=
  iprop(∃ (hp ap cl : Loc) (esl rsl : GoSlice) (mls : List Loc),
    l.[H.writeJob, go!"hs"] ↦ hp ∗ hsOptRO hp w.hs ∗ l.[H.writeJob, go!"snap"] ↦ null ∗
    l.[H.writeJob, go!"ents"] ↦ esl ∗ entsRO esl w.ents ∗
    l.[H.writeJob, go!"after"] ↦ ap ∗ hsRO ap w.after ∗
    l.[H.writeJob, go!"resp"] ↦ rsl ∗ rsl ↦* mls ∗ ownSliceCap Loc rsl (DFrac.own 1) ∗
    ([∗list] ml;st ∈ mls;w.resp, jobMsg id ml st) ∗
    l.[H.writeJob, go!"cause"] ↦ cl ∗ causeRO cl w.cause ∗ l.[H.writeJob, go!"by"] ↦ w.byE ∗
    l.[H.writeJob, go!"writes"] ↦ w.writes ∗ l.[H.writeJob, go!"k"] ↦ W64 w.k ∗
    ⌜w.k = -1 ∨ 0 ≤ w.k⌝)

/-- **A queued write job** at `l`: its object and its enter promise. -/
def writeJobOwn (γ : AntNamesB2) (j : Fin γ.R.N) (x : CrashNames) (g : Nat) (l : Loc) (w : WJob) :
    IProp GF :=
  iprop(writeJobObj (AntSim.nodeId j) l w ∗ jobEnter γ.raft.raftNames (AntSim.nodeId j) x g w)

/-- (#33 parity B2 round 2) **A run write job** at `l` (in flight, or held by `work` for `doneWrite`),
against raft's durable ghost `D`: its enter promise fired at its `saveDisk` (the ghost at its `post`,
the messages that waited for it certified), or, on a node killed before the save (`dead`), not fired
(the ghost still at its `pre`, the disk not written). -/
def writeJobMade (γ : AntNamesB2) (j : Fin γ.R.N) (l : Loc) (w : WJob) (D : RaftState) (dead : Bool) :
    IProp GF :=
  iprop(writeJobObj (AntSim.nodeId j) l w ∗
    ((⌜w.post = D⌝ ∗ [∗list] st ∈ w.resp, isRaftMsg γ.raft.raftNames (AntSim.nodeId j) st) ∨
     ⌜dead = true ∧ w.pre = D⌝))

/-- **An apply job's Go object** at `l` (`applyJob`; no restore in B2) of node `id`. -/
def applyJobOwn (id : w64) (l : Loc) (a : AJob) : IProp GF :=
  iprop(∃ (esl rsl : GoSlice) (mls : List Loc),
    l.[H.applyJob, go!"ents"] ↦ esl ∗ entsRO esl a.ents ∗ l.[H.applyJob, go!"restore"] ↦ null ∗
    l.[H.applyJob, go!"resp"] ↦ rsl ∗ rsl ↦* mls ∗
    ([∗list] ml;st ∈ mls;a.resp, jobMsg id ml st) ∗
    l.[H.applyJob, go!"by"] ↦ a.byE)

/-- **Node `j`'s B2 bookkeeping** (`nodeMemB1`'s fields at B2's values) against its view `v`, the
`RawNode`'s durable state `dur` and raft's durable ghost at the disk `D`: the batch's `items`; `mhs`
the in-memory hard state the last `mem` reported (batching), `rhs` the last `Ready`'s (async: `drainAsync`
alone sets it); the
write queue (`writes`, each job owned) and the job out of it (`inflight`: in `wip`, or held by `work`,
`hole`; once run, `writeJobMade`), the enter promises chained from `D` to `dur` (`JobsChain`; not on a
dead node, whose `Ready` taken and not entered is dropped with it, `rawNode_vacate.law`), the queue against the view (`QueueView`; not on a dead node either, whose view may hold a `-parallel` `mem` its write never popped); the
apply queue and the job applying; B3's fields at their off values. In a run without batching or
async storage both queues are empty and `items` is `0`. -/
def nodeMemB2 (γ : AntNamesB2) (j : Fin γ.R.N) (n : Loc) (v : AntSim.NodeView) (x : CrashNames)
    (g : Nat) (phs : HardStateM) (dur D : RaftState) (dead : Bool) (hole : Option WorkHole) : IProp GF :=
  iprop(∃ (items : Nat) (mhs rhs wip aip : Loc) (wsl asl : GoSlice) (wls als : List Loc)
      (jobs : List WJob) (ajobs : List AJob) (ow : Option WJob) (oa : Option AJob) (hm rh : HardStateM),
    n.[H.node, go!"items"] ↦ W64 items ∗ n.[H.node, go!"mhs"] ↦ mhs ∗ hsRO mhs hm ∗
    n.[H.node, go!"rhs"] ↦ rhs ∗ hsRO rhs rh ∗
    n.[H.node, go!"writes"] ↦ wsl ∗ wsl ↦* wls ∗ ownSliceCap Loc wsl (DFrac.own 1) ∗
    ([∗list] l;w ∈ wls;jobs, writeJobOwn γ j x g l w) ∗
    n.[H.node, go!"inflight"] ↦ ow.isSome ∗
    n.[H.node, go!"wip"] ↦ (if WorkHole.wHeld hole then null else wip) ∗
    (match ow with
     | none => iprop(⌜wip = null ∧ WorkHole.wHeld hole = false⌝)
     | some w => if WorkHole.wFresh hole then iprop(writeJobOwn γ j x g wip w ∗ ⌜w.pre = D⌝)
                 else writeJobMade γ j wip w D dead) ∗
    n.[H.node, go!"applies"] ↦ asl ∗ asl ↦* als ∗ ownSliceCap Loc asl (DFrac.own 1) ∗
    ([∗list] l;a ∈ als;ajobs, applyJobOwn (AntSim.nodeId j) l a) ∗
    n.[H.node, go!"applying"] ↦ oa.isSome ∗
    n.[H.node, go!"aip"] ↦ (if WorkHole.aHeld hole then null else aip) ∗
    (match oa with
     | none => iprop(⌜aip = null ∧ WorkHole.aHeld hole = false⌝)
     | some a => applyJobOwn (AntSim.nodeId j) aip a) ∗
    n.[H.node, go!"restoring"] ↦ W64 0 ∗ n.[H.node, go!"confs"] ↦ slice.nil ∗
    n.[H.node, go!"confBase"] ↦ W64 0 ∗
    ⌜(dead = false → QueueView v ((if WorkHole.wFresh hole then ow.toList else []) ++ jobs) items) ∧
      (dead = false → JobsChain (match ow with | some w => w.post | none => D) jobs dur) ∧
      (∀ l, hole = some (.runW l) ∨ hole = some (.doneW l) → wip = l ∧ ow.isSome) ∧
      (∀ l, hole = some (.runA l) ∨ hole = some (.doneA l) → aip = l ∧ oa.isSome) ∧
      (γ.mode.Batch' = true → hm = HardStateM.mk v.r.p.term v.r.p.vote v.r.p.commit) ∧
      (γ.mode.Batch' = false → items = 0) ∧ (γ.mode.Async' = true → rh = phs) ∧
      (γ.mode.Async' = false → jobs = [] ∧ ow = none ∧ ajobs = [] ∧ oa = none)⌝)

/-- **What a node goroutine gives back at its end** (`nodesWg.Done()`), under B2: its share of the
run's liveness and of the network's adders (not its node state: a killed node's waits in the `mu`
lock for the restarter). The node's reporting functions carry it through (their reports open the
run's invariant, `antInvB2`: the liveness share rules out its over arm). -/
def nodeExitB2 (c : Loc) (γ : AntNamesB2) (q : Qp) : IProp GF :=
  iprop(runLive γ q ∗ netAdder c γ.toAntNames q)

/-- (#33 parity B2) **A killed node's raft resources** (what the vacate law gives back when its
goroutine ends dead, `Cluster.run`; what `node.start`'s restart, `NewRawNode.restartAtApiSpec`, takes):
the id's slot vacant at a crash generation `x`, raft's durable state `D` (with the term budget) at the
disk `dk` (`StorageHolds`: the restart's), the configuration of no entry the initial voters' (the
driver restarts at `Applied = 0`), the cluster with its receipts' fit, and the cluster's static facts
(`nodeDownRaft`'s). -/
def restartRaft (γ : AntNamesB2) (j : Fin γ.R.N) (dk : AntSim.DurW) : IProp GF :=
  iprop(∃ (x : CrashNames) (D : RaftState),
    nodeVacantA γ.raft (AntSim.nodeId j) x ∗ raftState γ.raft (AntSim.nodeId j) D ∗
    ⌜StorageHolds D (diskContents dk)⌝ ∗
    confAt γ.raft 0 (Membership.simple γ.R.voters0) ∗
    (∃ Nr : Namespace, isCluster γ.raft Nr ∗ readyFits γ.raft Nr) ∗
    ⌜¬ clusterNoSnap γ.raft ∧ Cluster.trace γ.raft = none ∧ γ.raft.maxData = none ∧
      γ.raft.bootLen = (AntSim.bootLog γ.R).length ∧
      γ.raft.raftNames.reTrace = none ∧ γ.raft.raftNames.reCfg = γ.R.voters0 ∧
      γ.raft.raftNames.maxData = none ∧ γ.raft.raftNames.reBoot = AntSim.bootLog γ.R ∧
      (↑(raftN γ.raft.raftNames) : CoPset) ⊆ ⊤ \ ↑antN⌝)

/-- **The `RawNode`'s record against the view under B2** (`RsView`'s): what it handed out is the
view's delivered and unreported committed entries, nothing stepped, not following a snapshot, the role
the last `Ready` reported the view's; with synchronous storage (no queue) its last hard state and
durable log the view's disk and nothing unpersisted (B1's). -/
def RsViewB2 (md : H.Mode) (rs : RNState) (v : AntSim.NodeView) : Prop :=
  rs.delivered = v.delivered ++ v.ce ∧ rs.steps = [] ∧ rs.flw = false ∧
  roleStr rs.role = AntSim.roleS v ∧
  (md.Async' = false → rs.phs = HardStateM.mk v.dur.term v.dur.vote v.dur.commit ∧
    rs.dur.ents = v.dur.log ∧ rs.unpersisted = [] ∧ rs.dur.term = v.dur.term)

/-- **Node `j`'s goroutine's state under B2** at `n`, its view `v`, the phase `ph` (`nodeOwn`'s, see
the file header): always its fields, its kill fields (never set without restarts), the view fragment,
its entries normal, its disk at `dk` related to the view (`DiskRel`); then by phase:
- `down`: a fresh node (B1's: `FreshView`, the empty disk, `nodeDownRaft`), or a killed one (not
  running, `restartRaft` at the disk);
- otherwise the started node: its storage, its `RawNode` (its raft ghost state, B1's `nodeRaft` but
  for the durable ghost, which is at the disk, `D`, and the generation view the queue's enter promises
  name), its bookkeeping (`nodeMemB2`), the cause cell; and either **dead** (`n.dead`: the view frozen,
  nothing more), or alive with B1's per-phase facts over `RsViewB2` (`idle`'s `PIdle` and empty queue
  only without batching and, for the queue, without async storage), the Go fields agreeing with the
  view (with synchronous storage `n.hs` the view's disk's hard state at the drain's loop head and
between inputs, and the disk the view's at the drain's loop head: `DiskRel` alone allows the undo
record, and `StorageHolds` does not pin the disk's commit; no split write in progress there). The kill flag `n.dead` is the index `dead`. -/
def nodeOwnB2HD (c : Loc) (γ : AntNamesB2) (j : Fin γ.R.N) (n : Loc) (v : AntSim.NodeView) (ph : Phase)
    (hole : Option WorkHole) (dead : Bool) : IProp GF :=
  iprop(∃ (d rn ms hsl cl csl : Loc) (role : GoString) (applied : w64) (fuse : w64)
      (dk : AntSim.DurW),
    n.[H.node, go!"disk"] ↦□ d ∗
    n.[H.node, go!"rn"] ↦ rn ∗ n.[H.node, go!"store"] ↦ ms ∗ n.[H.node, go!"role"] ↦ role ∗
    n.[H.node, go!"hs"] ↦ hsl ∗ n.[H.node, go!"cause"] ↦ cl ∗ n.[H.node, go!"applied"] ↦ applied ∗
    n.[H.node, go!"conf"] ↦ csl ∗ killOwn n dead fuse ∗
    viewFrag γ.toAntNames j v ∗ diskOwn d dk ∗
    ⌜ViewNormal v ∧ DiskRel v dk ∧ (γ.mode.Restarts' = false → dead = false ∧ fuse = W64 0)⌝ ∗
    match ph with
    | .down => iprop(
        (⌜AntSim.FreshView γ.R v ∧ v.byE = go!"boot" ∧ dk = emptyDisk⌝ ∗ nodeDownRaft γ.toAntNames j) ∨
        (⌜v.alive = false⌝ ∗ restartRaft γ j dk))
    | _ => iprop(∃ (si : Loc) (rs : RNState) (qs : List Msg) (ip : Nat) (r : RState) (x : CrashNames)
          (g : Nat) (D : RaftState) (hn : HardStateM),
        nodeStor si ms ((List.range γ.R.K).map fun (i : Nat) => W64 ((i : Int) + 1)) hn ∗
        ⌜rs.storage = interface.ok ⟨go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.bootStorage.ty, #si⟩⌝ ∗
        rawNode γ.raft.raftNames γ.R.md rn (AntSim.nodeId j) rs r qs ip ∗
        genView γ.raft.raftNames (AntSim.nodeId j) x 1 g ∗
        ownDurGhost γ.raft.raftNames (AntSim.nodeId j) D ∗ rnTermLB γ.raft rs.tc ∗ rnBudget γ.raft ∗
        ⌜StorageHolds D (diskContents dk) ∧ uint.Z D.term ≤ uint.Z rs.tc⌝ ∗
        nodeMemB2 γ j n v x g rs.phs rs.dur D dead hole ∗
        hsRO hsl hn ∗
        if dead then iprop(True)
        else iprop(
          (⌜γ.mode.Async' = true⌝ ∨ slotFree γ.raft.raftNames (AntSim.nodeId j) g) ∗
          ⌜RsViewB2 γ.mode rs v ∧ v.alive = true ∧ role = AntSim.roleS v ∧
            uint.nat applied = v.delivered.length ∧ rs.k = γ.R.k j⌝ ∗
          csPts csl DFrac.discard
            (ConfStateM.mk ((List.range γ.R.K).map fun (i : Nat) => W64 ((i : Int) + 1)) [] [] [] false) false ∗
          readsOwn γ.toAntNames v ∗
          ⌜v.conf = γ.R.c0⌝ ∗
          match ph with
          | .down => iprop(False)
          | .idle => iprop(⌜v.Idle ∧ r = v.r ∧ cl = null ∧
              (γ.mode.Batch' = false → PIdle rs r.p) ∧
              (γ.mode.Batch' = false ∧ γ.mode.Async' = false → qs = [] ∧ ip = v.r.p.log.length) ∧
              (γ.mode.Async' = false → hn = HardStateM.mk v.dur.term v.dur.vote v.dur.commit)⌝)
          | .loop net₀ xnet₀ r₁ xs₁ => iprop(⌜r = r₁ ∧
              AntSim.ReachIn (if γ.mode.Async' then AntSim.mskB25 else AntSim.mskB2) γ.R γ.dec
                (AdmFold γ.dec γ.R.c0) net₀ xnet₀ j v r₁ ∧
              (γ.mode.Async' = false → qs = [] ∧ ip = lcpLen v.r.p.log r₁.p.log ∧
                hn = HardStateM.mk v.dur.term v.dur.vote v.dur.commit ∧ dk = v.dur ∧ v.parts = []) ∧
              ByOkB2 v.byE⌝ ∗
              sentLb γ.toAntNames net₀ ∗ xsentLb γ.toAntNames xnet₀ ∗ causeOwn γ.toAntNames j v cl)
          | .drained => iprop(⌜v.Idle ∧ r = v.r ∧
              (γ.mode.Batch' = false → PIdle rs r.p) ∧
              (γ.mode.Batch' = false ∧ γ.mode.Async' = false → qs = [] ∧ ip = v.r.p.log.length) ∧
              (γ.mode.Async' = false → hn = HardStateM.mk v.dur.term v.dur.vote v.dur.commit)⌝ ∗
              causeOwn γ.toAntNames j v cl))))

/-- **Node `j`'s goroutine's state under B2**, its kill flag `n.dead` (`nodeOwnB2HD`) left open. -/
def nodeOwnB2H (c : Loc) (γ : AntNamesB2) (j : Fin γ.R.N) (n : Loc) (v : AntSim.NodeView) (ph : Phase)
    (hole : Option WorkHole) : IProp GF :=
  iprop(∃ dead : Bool, nodeOwnB2HD c γ j n v ph hole dead)

/-- **Node `j`'s goroutine's state under B2** between its storage steps (`nodeOwnB2H` with no job held
by `work`). -/
abbrev nodeOwnB2 (c : Loc) (γ : AntNamesB2) (j : Fin γ.R.N) (n : Loc) (v : AntSim.NodeView) (ph : Phase) :
    IProp GF :=
  nodeOwnB2H c γ j n v ph none

/-- **The `mu` lock's invariant under B2** (`Cluster.down`, `downInv`'s): which node goroutines have
stopped dead and not been restarted; each such node's state deposited (`nodeOwnB2 … .down`, killed),
for the restarter. -/
def downInvB2 (c : Loc) (γ : AntNamesB2) (ns : List Loc) : IProp GF :=
  iprop(∃ (dsl : GoSlice) (ds : List Bool), c.[H.Cluster, go!"down"] ↦ dsl ∗ dsl ↦* ds ∗
    ⌜ds.length = γ.R.N ∧ (γ.mode.Restarts' = false → ∀ b ∈ ds, b = false)⌝ ∗
    [∗list] j ∈ List.finRange γ.R.N,
      if ds[j.val]! then iprop(∃ v : AntSim.NodeView, nodeOwnB2 c γ j ns[j.val]! v .down) else iprop(emp))

/-- **The cluster under B2** (`antCluster`'s, with the `mu` lock's invariant `downInvB2`, the nodes'
records `nodeROB2`, the invariant `antInvB2`). -/
def antClusterB2 [AntStor GF] (c : Loc) (γ : AntNamesB2) : IProp GF :=
  iprop(∃ (cfg : H.Config) (r : Loc) (ns : List Loc) (stop : Loc),
    c.[H.Cluster, go!"cfg"] ↦□ cfg ∗ ⌜CfgOk cfg⌝ ∗
    ⌜InScope γ.scope γ.mode ∧ ModeRun γ.scope γ.mode γ.R⌝ ∗
    c.[H.Cluster, go!"rec"] ↦□ r ∗ isRecorder γ.strm r ∗
    clusterRO c ns γ.mode ∗
    ([∗list] j ∈ List.finRange γ.R.N, nodeROB2 c γ ns[j.val]! j) ∗
    c.[H.Cluster, go!"stop"] ↦□ stop ∗ ownBroadcastChan stop γ.stopCh iprop(True) .Unknown ∗
    isNetJoin antNetN (c.[H.Cluster, go!"netWg"]) γ.net ∗
    sync.isMutex (c.[H.Cluster, go!"mu"]) (downInvB2 c γ ns) ∗
    inv antN (antInvB2 γ) ∗ ⌜antRunFits GF⌝ ∗ propMinter γ.toAntNames ∗ rdMinter γ.toAntNames ∗
    antStorInv ∗
    ⌜(∀ a : w64, (γ.raft.raftNames.reAcks !! a).isSome → ∃ j : Fin γ.R.N, a = AntSim.nodeId j) ∧
      (∀ a : w64, (γ.raft.raftNames.reWins !! a).isSome → ∃ j : Fin γ.R.N, a = AntSim.nodeId j) ∧
      (∀ j : Fin γ.R.N, (γ.raft.raftNames.reAcks !! AntSim.nodeId j).isSome)⌝)

/-- The node goroutines' join's namespace (`nodesWg` under B2: `sync.tokJoin`, its counter backed by
thread tokens, since the restarter adds without bound). -/
def antNodesN : Namespace := nroot.@"antithesis_nodes"

/-- **The restarter's resources** (`restarter`, `restart`): the `nodesWg` join's adder (single-adder,
thread-token-backed `sync.tokJoin`, no lending: the only adder after `RunCluster`'s first `N` adds,
handed to the restarter and back through `behWg`), whose accumulated `Done` resources give back the
shares `qp`, and its own share `q` of the run's liveness and of the network's adders, from which it
splits a restarted goroutine's; the two make up `Q`, what `RunCluster` handed it. -/
def restarterOwn (c : Loc) (γ : AntNamesB2) (Q : Qp) : IProp GF :=
  iprop(∃ (k : Nat) (P : IProp GF) (q qp : Qp),
    sync.tokJoin.ownAdder antNodesN iprop(False) (c.[H.Cluster, go!"nodesWg"]) k P ∗
    (P -∗ nodeExitB2 c γ qp) ∗ nodeExitB2 c γ q ∗ ⌜q + qp = Q⌝)

/-- **What a node goroutine holds to end** (`Cluster.run`'s, under B2): the right to call
`nodesWg.Done` with its share of the run's liveness and of the network's adders. -/
def nodeDoneB2 (c : Loc) (γ : AntNamesB2) (q : Qp) : IProp GF :=
  sync.tokJoin.ownDone antNodesN iprop(False) (c.[H.Cluster, go!"nodesWg"]) (nodeExitB2 c γ q)

end defs

end AntHarness
end EtcdGrove
end Perennial
