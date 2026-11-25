/-
Lean-first (no Rocq counterpart).

# The Antithesis harness's vocabulary (#33 S4, specs first; `notes/antithesis-s4-design.md` §2-§3)

What the harness's specs (`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/<fn>.lean`)
are written in. This first part has no invariant yet (§6 of the note lists what is still missing):

- **The harness's pure readings of Go data**, each the Go function's reading field by field:
  `msgTypeStr` (`msgType`, over raftpb's `MessageType`), `roleStr` (`roleOf`, over raft's
  `StateType`), `entOfE` (`entryOf` of a normal entry), `msgOfSt st to` (`msgOf(m, to)` of a
  `*pb.Message` holding `st`). Numbers are Go's `int(x)` of a `uint64`, `sint.Z x`; the refinement's
  `AntSim.entOf`/`AntSim.msgOf` read `uint.Z`, the same below `2^63` (the harness's proof carries
  the bound). Names are `AntSim.nameOf` (`Name`'s).
- **The recorder** `isRecorder γr r`: its lock guards the recorded slice, holding the stream `evs`
  (`eventsRO`), half of the stream's ghost variable `γr`, and `Event.weight` time receipts per
  report, which bound the stream (`Stream.Fits`). The other half is `recAuth γr evs`: what a report's
  atomic update takes (from the harness's invariant), and, held by the caller once every recording
  goroutine has finished, `recDone γr evs` (no report can be recorded any more).
- **The run over**, `runOver c`: what `RunCluster` returns and `Cluster.Events` and `Main` read.
- **The storage wrapper's record** `bootStorRec s ms vs`, **the configuration's premise** `CfgOk`,
  the default configuration `defaultCfg`, the cluster's read-only fields `clusterRO`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Rep
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Abs
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Base
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

/-- The harness's types, by their short names. -/
abbrev H.Recorder := github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Recorder
abbrev H.Cluster := github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster
abbrev H.Config := github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Config
abbrev H.bootStorage := github_com.mit_pdos.etcd_grove.examples.raft.antithesis.bootStorage
abbrev H.node := github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node

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

/-! ## The harness's pure readings of Go data -/

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

/-- Go `entryOf(e)` of a normal entry (the Go panics on any other): `"noop"` when its data is
empty, `"command"` with the data as the value otherwise; the term is `int(e.Term)`. -/
def entOfE (e : EntryM) : AntCheck.Entry :=
  if e.Data' = [] then { term := sint.Z e.Term', type := go!"noop", value := { str := [] } }
  else { term := sint.Z e.Term', type := go!"command", value := { str := e.Data' } }

/-- Go `msgOf(m, to)` of a `*pb.Message` holding `st`: every field present (`check.MFAll`), each
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

/-- The entries `entryOf` takes without panicking: normal ones (`EntryNormal = 0`). -/
def AllNormal (es : List EntryM) : Prop := ∀ e ∈ es, e.Type' = W32 0

/-! ## The run's configuration -/

/-- **What `RunCluster` needs of its configuration**: three voters (the closed statement's
`cfg3`) and a positive tick (`time.NewTicker` panics otherwise, in each node's `run`). -/
def CfgOk (cfg : H.Config) : Prop :=
  cfg.Nodes' = W64 3 ∧ 0 < sint.Z cfg.Tick'

/-- `DefaultConfig()`'s record: 3 voters, 60ms to run, a 2ms tick (durations in nanoseconds). -/
def defaultCfg : H.Config :=
  { Nodes' := W64 3, Settle' := W64 60000000, Tick' := W64 2000000 }

/-! ## Bounds -/

/-- **The stream fits the receipts** the recorder's lock holds: its weight (`Event.weight`, two plus
each report's size, summed) is below the receipts' bound. -/
def Stream.Fits (GF : BundledGFunctors) [ReceiptGS GF] (evs : List AntCheck.Event) : Prop :=
  (evs.map AntCheck.Event.weight).sum < receiptBound GF

/-- **The harness's receipts fit** (`receiptBound GF + 3 ≤ 2^61`, the closed theorem's `n + 4 ≤
2^61`; the trace check's `tcRunFits`): with `Stream.Fits`, `Stream.Bounded`'s size part, and raft's
term budget (`rnTermLB_rb`) the stream's numbers. -/
def antRunFits (GF : BundledGFunctors) [ReceiptGS GF] : Prop := receiptBound GF + 3 ≤ 2 ^ 61

end readings

/-! ## The recorder, the storage wrapper, the cluster's fields -/

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]

/-- **A report's right to append**: the caller's half of the stream's ghost variable. -/
def recAuth (γr : GName) (evs : List AntCheck.Event) : IProp GF := ghostVar γr (1 : Qp).half evs

/-- **The stream, final**: `recAuth` held by the caller once every goroutine that records has
finished (the harness's invariant gave it up), so that no report can be recorded any more. -/
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

/-- **The run is over** (`RunCluster`'s post): the cluster's recorder and its final stream, accepted
by the checker at `cfg3`, within the Go `int`'s budget (`Stream.Bounded`) and with no configuration
change (`Stream.ConfBounded`, which `check.Run` also takes), and the configuration's three nodes
(`Servers`). -/
def runOver (c : Loc) : IProp GF :=
  iprop(∃ (r : Loc) (γr : GName) (evs : List AntCheck.Event),
    c.[H.Cluster, go!"rec"] ↦□ r ∗ isRecorder γr r ∗ recDone γr evs ∗
    c.[H.Cluster, go!"cfg"].[H.Config, go!"Nodes"] ↦□ W64 3 ∗
    ⌜AntCheck.Accepts AntSim.cfg3 evs ∧ AntCheck.Stream.Bounded evs ∧
      AntCheck.Stream.ConfBounded AntSim.cfg3 evs⌝)

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

/-- **The cluster's read-only fields** (persistent): the nodes and the configuration's `Nodes`. -/
def clusterRO (c : Loc) (ns : List Loc) (N : w64) : IProp GF :=
  iprop(∃ nsl : GoSlice, c.[H.Cluster, go!"nodes"] ↦□ nsl ∗ nsl ↦*□ ns ∗
    c.[H.Cluster, go!"cfg"].[H.Config, go!"Nodes"] ↦□ N)

instance clusterRO_persistent (c : Loc) (ns : List Loc) (N : w64) :
    Persistent (clusterRO (GF := GF) c ns N) := by
  unfold clusterRO; infer_instance

end defs

end AntHarness
end EtcdGrove
end Perennial
