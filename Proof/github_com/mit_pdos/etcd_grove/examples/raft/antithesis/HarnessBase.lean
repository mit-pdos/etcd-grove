/-
Lean-first (no Rocq counterpart).

# The Antithesis driver's vocabulary, pure and read-only part (#33 parity B1)

`notes/antithesis-parity-design.md` §3.1 (the run's configuration), over the parity driver
(`examples/raft/antithesis/{driver,node,harness,main}.go`). It replaces S4's `HarnessDefs.lean`
(whose `CfgOk` read the old `Config.Nodes`): the pure readings of Go data and the recorder are
S4's text unchanged; new are the driver's scope and mode and their reading as a run's
configuration (`AntSim.RunCfg`):

- **The scope and the mode** (`H.Scope`, `H.Mode`): `mainScope` (`MainScope()`, the constants of
  `main.go`, all on: the final program), `b1Scope` (batch B1's mask: messages and N servers, every
  B2/B3 feature off and forwarding off, `antithesis-parity-plan.md` §3), `InScope s m` (what
  `DrawMode(s)` returns: every drawn flag allowed by `s`, rawnode's exclusions, the simulator's
  values), and `ModeRun s m R` (the run's configuration `R` read off the mode `m` drawn within the
  scope `s`: `N`, `K`, `boot`, the nodes' `Config` flags `modeK m`, the mask `scopeMd s`).
- **The pure readings of Go data** (S4's): `msgTypeStr`, `roleStr`, `entOfE` (now with the
  bootstrapped run's `"config"` entry), `msgOfSt`, `AllNormal`.
- **The recorder** (S4's): `recAuth`, `recDone`, `recLockInv`, `isRecorder`; the stream's fit
  `Stream.Fits`, `antRunFits`.
- **The configuration's premise** `CfgOk` (a positive tick), `defaultCfg`; the storage wrapper's
  record `bootStorRec`, `bootConfState`; the cluster's nodes `clusterRO`, `nodeOf`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Rep
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Abs
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Base
public import Proof.go_etcd_io.raft.v3.Protocol.RnMode
public import Spec.go_etcd_io.raft.v3.MemoryStorage__InitialState
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Snapshot
public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis
public import Perennial.Proof.sync.Base
public import Perennial.ProgramLogic.Bounds

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI go_etcd_io.raft.v3

section types
variable [GooseExts]

/-- The driver's types, by their short names. -/
abbrev H.Recorder := github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Recorder
abbrev H.Cluster := github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster
abbrev H.Config := github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Config
abbrev H.Scope := github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Scope
abbrev H.Mode := github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Mode
abbrev H.input := github_com.mit_pdos.etcd_grove.examples.raft.antithesis.input
abbrev H.bootStorage := github_com.mit_pdos.etcd_grove.examples.raft.antithesis.bootStorage
abbrev H.node := github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node
abbrev H.disk := github_com.mit_pdos.etcd_grove.examples.raft.antithesis.disk
abbrev H.nodeLogger := github_com.mit_pdos.etcd_grove.examples.raft.antithesis.nodeLogger
abbrev H.part := github_com.mit_pdos.etcd_grove.examples.raft.antithesis.part

end types

/-! ## The stream's values are countable (the recorder's ghost variable holds a stream) -/

instance value_countable : Pos.Countable AntCheck.Value :=
  countableOfLeftInverse (fun v : AntCheck.Value => (v.isRec, v.str, v.add, v.remove, v.joint, v.leave))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2⟩) (fun _ => rfl)

instance entry_countable : Pos.Countable AntCheck.Entry :=
  countableOfLeftInverse (fun e : AntCheck.Entry => (e.term, e.type, e.value))
    (fun p => ⟨p.1, p.2.1, p.2.2⟩) (fun _ => rfl)

instance msg_countable : Pos.Countable AntCheck.Msg :=
  countableOfLeftInverse
    (fun m : AntCheck.Msg => (m.type, m.frm, m.to, m.term, m.index, m.logTerm, m.entries, m.commit, m.reject))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2⟩) (fun _ => rfl)

instance snapRef_countable : Pos.Countable AntCheck.SnapRef :=
  countableOfLeftInverse (fun s : AntCheck.SnapRef => (s.index, s.term)) (fun p => ⟨p.1, p.2⟩) (fun _ => rfl)

instance event_countable : Pos.Countable AntCheck.Event :=
  countableOfLeftInverse
    (fun ev : AntCheck.Event =>
      ((ev.e, ev.node, ev.byE, ev.role, ev.term, ev.vote),
       (ev.commit, ev.first, ev.entries, ev.lastIndex, ev.lastTerm, ev.applied),
       (ev.voters, ev.outgoing, ev.snap, ev.msg, ev.cause, ev.b),
       (ev.a, ev.w, ev.more, ev.index, ev.ctx, ev.bad)))
    (fun p =>
      { e := p.1.1, node := p.1.2.1, byE := p.1.2.2.1, role := p.1.2.2.2.1, term := p.1.2.2.2.2.1,
        vote := p.1.2.2.2.2.2,
        commit := p.2.1.1, first := p.2.1.2.1, entries := p.2.1.2.2.1, lastIndex := p.2.1.2.2.2.1,
        lastTerm := p.2.1.2.2.2.2.1, applied := p.2.1.2.2.2.2.2,
        voters := p.2.2.1.1, outgoing := p.2.2.1.2.1, snap := p.2.2.1.2.2.1, msg := p.2.2.1.2.2.2.1,
        cause := p.2.2.1.2.2.2.2.1, b := p.2.2.1.2.2.2.2.2,
        a := p.2.2.2.1, w := p.2.2.2.2.1, more := p.2.2.2.2.2.1, index := p.2.2.2.2.2.2.1,
        ctx := p.2.2.2.2.2.2.2.1, bad := p.2.2.2.2.2.2.2.2 })
    (fun _ => rfl)

/-! ## The scope and the run's mode -/

section mode
variable [GooseExts]

/-- `MainScope()`: the constants `scope*` of `main.go`'s driver (`driver.go`), all on (the final
program; each interim theorem's program has its batch's mask there instead). -/
def mainScope : H.Scope :=
  ⟨true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true⟩

/-- **Batch B1's mask** (`antithesis-parity-plan.md` §3, B1: messages and N servers): pre-vote,
check-quorum, reads, transfers, duplication, non-voters, bootstrapped logs and the limits on; network
forwarding of proposals off (it comes later, with `raft.Step`'s widening); every B2/B3 feature off
(restarts, async, batch, parallel, split, snapshots, conf changes). -/
def b1Scope : H.Scope :=
  { PreVote' := true, CheckQuorum' := true, Reads' := true, Transfer' := true, Forwarding' := false,
    Dup' := true, NonVoters' := true, Boot' := true, Limits' := true, Restarts' := false,
    Async' := false, Batch' := false, Parallel' := false, Split' := false, Snapshots' := false,
    ConfChanges' := false }

/-- **`DrawMode(s)`'s result** (`driver.go`): every flag drawn on only where `s` allows it, within
what rawnode allows (no batching with `Parallel` or `Split`; `Parallel` and `Split` only for
synchronous storage; `Split` the order the model accepts), from the simulator's values:
3 or 5 servers, all voters or (non-voters) 3 of 5; `MaxInflightMsgs ∈ {1, 2, 256}` and
`MaxSizePerMsg ∈ {0, 64, 2^20}` (raft's usual `256`, `2^20` without limits); `MaxDeliveries` 1 or
(dup) 2; `SnapStatus` only with snapshots, `StepDownOnRemoval` only with conf changes; the anchor
an initial voter. -/
def InScope (s : H.Scope) (m : H.Mode) : Prop :=
  (m.Nodes' = W64 3 ∨ m.Nodes' = W64 5) ∧
  (m.Voters' = m.Nodes' ∨ (s.NonVoters' = true ∧ m.Nodes' = W64 5 ∧ m.Voters' = W64 3)) ∧
  (m.Boot' = true → s.Boot' = true) ∧
  (m.PreVote' = true → s.PreVote' = true) ∧ (m.CheckQuorum' = true → s.CheckQuorum' = true) ∧
  (if s.Limits' then (m.MaxInflightMsgs' = W64 1 ∨ m.MaxInflightMsgs' = W64 2 ∨
      m.MaxInflightMsgs' = W64 256) ∧
      (m.MaxSizePerMsg' = W64 0 ∨ m.MaxSizePerMsg' = W64 64 ∨ m.MaxSizePerMsg' = W64 (2 ^ 20))
    else m.MaxInflightMsgs' = W64 256 ∧ m.MaxSizePerMsg' = W64 (2 ^ 20)) ∧
  (m.Forward' = true → s.Forwarding' = true) ∧
  (m.MaxDeliveries' = W64 1 ∨ (s.Dup' = true ∧ m.MaxDeliveries' = W64 2)) ∧
  (m.Async' = true → s.Async' = true) ∧ (m.Batch' = true → s.Batch' = true) ∧
  (m.Parallel' = true → s.Parallel' = true ∧ m.Async' = false ∧ m.Batch' = false) ∧
  (m.Split' = W64 0 ∨ (s.Split' = true ∧ m.Async' = false ∧ m.Batch' = false ∧ m.Split' = W64 1)) ∧
  (m.Reads' = true → s.Reads' = true) ∧ (m.Transfer' = true → s.Transfer' = true) ∧
  (m.Restarts' = true → s.Restarts' = true) ∧ (m.Snapshots' = true → s.Snapshots' = true) ∧
  (m.ConfChanges' = true → s.ConfChanges' = true) ∧
  (m.SnapStatus' = true → m.Snapshots' = true) ∧
  (m.StepDownOnRemoval' = true → m.ConfChanges' = true) ∧
  1 ≤ uint.Z m.Anchor' ∧ uint.Z m.Anchor' ≤ uint.Z m.Voters'

/-- The nodes' `Config` flags of a run (`node.start`'s `raft.Config`: equal across nodes). -/
def modeK (m : H.Mode) : NodeK :=
  { prevote := m.PreVote', cq := m.CheckQuorum', sdr := m.StepDownOnRemoval' }

/-- The RawNode scope mask of a driver scope (design R3: the `RnMode` value of a batch is its
mask; forwarding and non-voters are the scope's flags of the same names). -/
def scopeMd (s : H.Scope) : RnMode :=
  { prevote := s.PreVote', cq := s.CheckQuorum', reads := s.Reads', transfer := s.Transfer',
    forwarding := s.Forwarding', snapshots := s.Snapshots', confChanges := s.ConfChanges',
    async := s.Async', nonVoters := s.NonVoters' }

/-- **The run's configuration `R` of the mode `m` drawn within the scope `s`** (design §3.1):
`Server = names(Nodes)`, `InitVoters = names(Voters)`, `Bootstrapped = Boot`, each node's flags the
mode's, the mask the scope's. -/
def ModeRun (s : H.Scope) (m : H.Mode) (R : AntSim.RunCfg) : Prop :=
  R.N = uint.nat m.Nodes' ∧ R.K = uint.nat m.Voters' ∧ R.boot = m.Boot' ∧
  (∀ n, R.k n = modeK m) ∧ R.md = scopeMd s

end mode

/-! ## The driver's pure readings of Go data -/

section readings
variable [GooseExts]

/-- Go `msgType(t)` (the switch; `"other"` for a type it does not list). -/
def msgTypeStr (t : w32) : AntCheck.Str :=
  if t = MsgApp then go!"app" else if t = MsgAppResp then go!"appresp"
  else if t = MsgVote then go!"vote" else if t = MsgVoteResp then go!"voteresp"
  else if t = MsgHeartbeat then go!"hb" else if t = MsgHeartbeatResp then go!"hbresp"
  else if t = MsgPreVote then go!"prevote" else if t = MsgPreVoteResp then go!"prevoteresp"
  else if t = MsgSnap then go!"snap" else if t = MsgTimeoutNow then go!"timeoutnow"
  else if t = MsgReadIndex then go!"readindex" else if t = MsgReadIndexResp then go!"readindexresp"
  else if t = MsgProp then go!"prop" else if t = MsgTransferLeader then go!"transfer"
  else go!"other"

/-- Go `roleOf(s)`. -/
def roleStr (s : w64) : AntCheck.Str :=
  if s = StateLeader then go!"leader" else if s = StateCandidate then go!"candidate"
  else if s = StatePreCandidate then go!"precandidate" else go!"follower"

/-- Go `bootData()`: what the bootstrapped run's first entry holds (`"boot"`). -/
def bootDataL : List w8 := go!"boot"

/-- Go `entryOf(e, n)` of a normal entry (a conf entry's arm, `changeOf`, is batch B3's): the
bootstrapped run's first entry (index 1, data `bootData()`) is `"config"`; otherwise `"noop"` when
its data is empty, `"command"` with the data as the value; the term is `int(e.Term)`. -/
def entOfE (e : EntryM) : AntCheck.Entry :=
  if e.Index' = W64 1 ∧ e.Data' = bootDataL then
    { term := sint.Z e.Term', type := go!"config", value := { str := [] } }
  else if e.Data' = [] then { term := sint.Z e.Term', type := go!"noop", value := { str := [] } }
  else { term := sint.Z e.Term', type := go!"command", value := { str := e.Data' } }

/-- Go `msgOf(m, to, n)` of a `*pb.Message` holding `st`: every field present (`check.MFAll`), each
read by its getter; a `MsgSnap`'s index and log term its snapshot's metadata (`0` for none, the nil
getters'). The Go's `Hint` is not in the transcription. -/
def msgOfSt (st : MsgSt) (to : w64) : AntCheck.Msg :=
  let isSnap := decide (st.msg.Type' = MsgSnap)
  { type := some (msgTypeStr st.msg.Type'), frm := some (AntSim.nameOf st.msg.From'),
    to := some (AntSim.nameOf to), term := some (sint.Z st.msg.Term'),
    index := some (if isSnap then sint.Z ((st.snap.map (·.Metadata'.Index')).getD (W64 0))
      else sint.Z st.msg.Index'),
    logTerm := some (if isSnap then sint.Z ((st.snap.map (·.Metadata'.Term')).getD (W64 0))
      else sint.Z st.msg.LogTerm'),
    entries := some (st.ents.map entOfE), commit := some (sint.Z st.msg.Commit'),
    reject := some st.msg.Reject' }

/-- The entries `entryOf` takes without calling `changeOf`: normal ones (`EntryNormal = 0`). -/
def AllNormal (es : List EntryM) : Prop := ∀ e ∈ es, e.Type' = W32 0

/-- Entries whose term and index are below `2 ^ 61` (so that the Go's `int(x)` readings are the
refinement's `uint.Z` ones). -/
def EntsSmall (es : List EntryM) : Prop := ∀ e ∈ es, uint.Z e.Term' < 2 ^ 61 ∧ uint.Z e.Index' < 2 ^ 61

/-- Go `firstIndex(ents)`: the first entry's index, `0` for none. -/
def firstIdx (es : List EntryM) : w64 := (es.head?.map (·.Index')).getD (W64 0)

/-- Go `n.stateEv(e, hs, ents)`: a report of kind `e` with rawnode's `state` fields (term, vote,
commit, first index, entries; the node's name is set when it is recorded, `emit`). -/
def stateEvM (e : AntCheck.Str) (hs : HardStateM) (es : List EntryM) : AntCheck.Event :=
  { e := e, node := [], term := some (sint.Z hs.Term'), vote := some (AntSim.nameOf hs.Vote'),
    commit := some (sint.Z hs.Commit'), first := some (sint.Z (firstIdx es)),
    entries := some (es.map entOfE) }

/-- Go `withByRole(ev, by, role)`. -/
def withByRoleM (ev : AntCheck.Event) (by_ role : AntCheck.Str) : AntCheck.Event :=
  { ev with byE := some by_, role := some role }

/-- Go `n.sendEv(by, m)` of a message holding `st`. -/
def sendEvM (by_ : AntCheck.Str) (st : MsgSt) : AntCheck.Event :=
  { e := go!"send", node := [], byE := some by_, msg := some (msgOfSt st st.msg.To') }

/-- `applyCommitted`'s `apply` report of the entries `es` (not empty). -/
def applyEvM (by_ : AntCheck.Str) (es : List EntryM) : AntCheck.Event :=
  { e := go!"apply", node := [], byE := some by_, first := some (sint.Z (firstIdx es)),
    entries := some (es.map entOfE) }

/-- `reads`'s `read` report of a read state. -/
def readEvM (r : ReadStateM) : AntCheck.Event :=
  { e := go!"read", node := [], ctx := some r.RequestCtx', index := some (sint.Z r.Index') }

/-- `readIndex`'s `readreq` report of the context `ctx`. -/
def readReqEvM (ctx : List w8) : AntCheck.Event := { e := go!"readreq", node := [], ctx := some ctx }

/-- `reportCause`'s `recv` report of the handled message's report `m`. -/
def recvEvM (m : AntCheck.Msg) : AntCheck.Event := { e := go!"recv", node := [], msg := some m }

/-- The report `ev` as `emit` records it at the node named `nm`. -/
def atNode (nm : AntCheck.Str) (ev : AntCheck.Event) : AntCheck.Event :=
  { ev with node := nm }

/-! ## The run's pacing -/

/-- **What `RunCluster` needs of its pacing**: a positive tick (`time.NewTicker` panics otherwise,
in each node's `run`). Any other durations give a run the theorem covers. -/
def CfgOk (cfg : H.Config) : Prop := 0 < sint.Z cfg.Tick'

/-- `DefaultConfig()`'s record (durations in nanoseconds): 150ms to run, a 2ms tick, a behaviour
every 1ms, a restart every 40ms, an election or a transfer every 20ms. -/
def defaultCfg : H.Config :=
  { Settle' := W64 150000000, Tick' := W64 2000000, Pace' := W64 1000000,
    RestartPace' := W64 40000000, ElectionPace' := W64 20000000, NoHoldVote' := false }

/-! ## Bounds -/

/-- **The stream fits the receipts** the recorder's lock holds: its weight (`Event.weight`, two plus
each report's size, summed) is below the receipts' bound. -/
def Stream.Fits (GF : BundledGFunctors) [ReceiptGS GF] (evs : List AntCheck.Event) : Prop :=
  (evs.map AntCheck.Event.weight).sum < receiptBound GF

/-- **The driver's receipts fit** (`receiptBound GF + 3 ≤ 2^61`, the closed theorem's `n + 4 ≤
2^61`): with `Stream.Fits`, `Stream.Bounded`'s size part, and raft's term budget (`rnTermLB_rb`)
the stream's numbers. -/
def antRunFits (GF : BundledGFunctors) [ReceiptGS GF] : Prop := receiptBound GF + 3 ≤ 2 ^ 61

end readings

/-! ## The recorder, the storage wrapper, the cluster's nodes -/

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]

/-- **A report's right to append**: the caller's half of the stream's ghost variable. -/
def recAuth (γr : GName) (evs : List AntCheck.Event) : IProp GF := ghostVar γr (1 : Qp).half evs

/-- **The stream, final**: `recAuth` held by the caller once every goroutine that records has
finished (the run's invariant gave it up), so that no report can be recorded any more. -/
def recDone (γr : GName) (evs : List AntCheck.Event) : IProp GF := recAuth γr evs

/-- The recorder's lock invariant: the recorded slice (and its capacity) holding the stream, the
lock's half of the ghost variable, and the reports' receipts. -/
def recLockInv (γr : GName) (r : Loc) : IProp GF :=
  iprop(∃ (sl : GoSlice) (evs : List AntCheck.Event),
    r.[H.Recorder, go!"events"] ↦ sl ∗ AntCheck.eventsRO sl evs ∗
    ownSliceCap Loc sl (DFrac.own 1) ∗ ghostVar γr (1 : Qp).half evs ∗
    ⧗ ((evs.map AntCheck.Event.weight).sum))

/-- **The recorder at `r`, recording the stream `γr`** (persistent). -/
def isRecorder (γr : GName) (r : Loc) : IProp GF :=
  iprop(sync.isMutex (r.[H.Recorder, go!"mu"]) (recLockInv γr r))

instance isRecorder_persistent (γr : GName) (r : Loc) : Persistent (isRecorder (GF := GF) γr r) := by
  unfold isRecorder; infer_instance

/-- **A report being built** at `p` (owned: `emit` sets its node, `withByRole` its by and role),
holding `ev`: `check`'s `eventRO` with the struct owned. -/
def eventOwn (p : Loc) (ev : AntCheck.Event) : IProp GF :=
  iprop(∃ g : AntCheck.G.Event, p ↦ g ∗
    ⌜g.E' = ev.e ∧ g.Node' = ev.node ∧ g.Bad' = ev.bad ∧
      (AntCheck.hasBit g.Has' AntCheck.fB ↔ ev.b = true) ∧
      (AntCheck.hasBit g.Has' AntCheck.fA ↔ ev.a = true) ∧
      AntCheck.fieldIs g.Has' AntCheck.fBy g.By' ev.byE ∧
      AntCheck.fieldIs g.Has' AntCheck.fRole g.Role' ev.role ∧
      AntCheck.fieldZ g.Has' AntCheck.fTerm g.Term' ev.term ∧
      AntCheck.fieldIs g.Has' AntCheck.fVote g.Vote' ev.vote ∧
      AntCheck.fieldZ g.Has' AntCheck.fCommit g.Commit' ev.commit ∧
      AntCheck.fieldZ g.Has' AntCheck.fFirst g.First' ev.first ∧
      AntCheck.fieldZ g.Has' AntCheck.fLastIndex g.LastIdx' ev.lastIndex ∧
      AntCheck.fieldZ g.Has' AntCheck.fLastTerm g.LastTerm' ev.lastTerm ∧
      AntCheck.fieldZ g.Has' AntCheck.fApplied g.Applied' ev.applied ∧
      AntCheck.fieldRel g.Has' AntCheck.fSnap AntCheck.snapRel g.Snap' ev.snap ∧
      AntCheck.fieldZ g.Has' AntCheck.fW g.W' ev.w ∧ AntCheck.fieldZ g.Has' AntCheck.fMore g.More' ev.more ∧
      AntCheck.fieldZ g.Has' AntCheck.fIndex g.Index' ev.index ∧
      AntCheck.fieldIs g.Has' AntCheck.fCtx g.Ctx' ev.ctx⌝ ∗
    AntCheck.fieldRO g.Has' AntCheck.fEntries AntCheck.logRO g.Entries' ev.entries ∗
    AntCheck.fieldRO g.Has' AntCheck.fVoters AntCheck.strsRO g.Voters' ev.voters ∗
    AntCheck.fieldRO g.Has' AntCheck.fOutgoing AntCheck.strsRO g.Outgoing' ev.outgoing ∗
    AntCheck.fieldRO g.Has' AntCheck.fMsg AntCheck.msgRO g.Msg' ev.msg ∗
    AntCheck.fieldRO g.Has' AntCheck.fCause AntCheck.msgsRO g.Cause' ev.cause)

/-- **The reports `evs` may be recorded, in order, then `Q`**: for each, its receipts and an atomic
update appending it to the stream (`Recorder.record`'s), whose commit gives the rest. The caller
(a drain's proof) builds it from the run's invariant, keeping the view's fragment inside. -/
def reports (γr : GName) : List AntCheck.Event → IProp GF → IProp GF
  | [], Q => Q
  | ev :: evs, Q => iprop(⧗ ev.weight ∗
      (AU <{ ∃∃ es, recAuth (GF := GF) γr es }> @ ⊤, ∅
        <{ recAuth γr (es ++ [ev]) ∗ ⌜Stream.Fits GF (es ++ [ev])⌝, COMM reports γr evs Q }>))

/-- **A `bootStorage`'s fields** (persistent): its `MemoryStorage` `ms` and its voters `vs`. -/
def bootStorRec (s ms : Loc) (vs : List w64) : IProp GF :=
  iprop(∃ vsl : GoSlice, s.[H.bootStorage, go!"ms"] ↦□ ms ∗ s.[H.bootStorage, go!"voters"] ↦□ vsl ∗
    vsl ↦*□ vs)

instance bootStorRec_persistent (s ms : Loc) (vs : List w64) :
    Persistent (bootStorRec (GF := GF) s ms vs) := by
  unfold bootStorRec; infer_instance

/-- The conf state `InitialState` reports at the stored snapshot `sv`: the voters' while there is
no snapshot (index `0`), the snapshot's otherwise. -/
def bootConfState (vs : List w64) (sv : SnapshotM) : ConfStateM :=
  if sv.Metadata'.Index' = W64 0 then ConfStateM.mk vs [] [] [] false else sv.Metadata'.ConfState'

/-- The node at `c.node(id)`: the `id`-th of the nodes `ns`, `nil` for `0` or past the end. -/
def nodeOf (ns : List Loc) (id : w64) : Loc :=
  if id = W64 0 ∨ ns.length < uint.nat id then null else ns[uint.nat id - 1]!

/-- **The cluster's read-only fields** (persistent): the nodes `ns`, the run's mode `m` (its
`Nodes`, `pick`'s and `node`'s bound) and the initial voters `1, …, Voters` (`initVoters`). -/
def clusterRO (c : Loc) (ns : List Loc) (m : H.Mode) : IProp GF :=
  iprop(∃ (nsl ivl : GoSlice), c.[H.Cluster, go!"nodes"] ↦□ nsl ∗ nsl ↦*□ ns ∗
    ⌜ns.length = uint.nat m.Nodes'⌝ ∗ c.[H.Cluster, go!"mode"] ↦□ m ∗
    c.[H.Cluster, go!"initVoters"] ↦□ ivl ∗
    ivl ↦*□ ((List.range (uint.nat m.Voters')).map fun (i : Nat) => W64 ((i : Int) + 1)))

instance clusterRO_persistent (c : Loc) (ns : List Loc) (m : H.Mode) :
    Persistent (clusterRO (GF := GF) c ns m) := by
  unfold clusterRO; infer_instance

end defs

end AntHarness
end EtcdGrove
end Perennial
