/-
Lean-first (no Rocq counterpart).

# The refinement to Antithesis's binding: abstractions and reports (#33 S3c step 5 / S4)

What the harness (`examples/raft/antithesis/harness.go`) reports, as functions of raft's protocol
data (`Protocol/Model.lean`: `Msg`, `EntryM`, `Role`), over the S3b transcription's types
(`AntCheck`, `check/Tla/Types.lean`). Each function mirrors the Go function of the same name
(`Name`, `names`, `entryOf`, `msgOf`, `roleOf`) or the `check.Event` literal of one report
(`evBoot`: `RunCluster`'s `boot`; `evRecv`: `reportCause`; `evReady`, `evSend`, `evApply`:
`drain`), field by field and with the same fields present (`Has`); the S4 harness proof shows
each Go function returns them (`notes/antithesis-s4-design.md` §2). `notes/antithesis-rawnode-design.md`
§3.1 is the design, §3.5 the deviations.

Numbers: Go's `int(x)` of a `uint64` is `sint.Z x`; here a number is `uint.Z x`, which is the
same below `2^63`: the harness's specs carry the bound (terms through raft's term budget,
indices through the log's length, both below `2^61`), so the refinement's lemmas need none.

Pure: imports only raft's protocol model (and its plain records `NodeK`, `RnMode`), the transcription
and Perennial's `fmtUint`, the model of `strconv.FormatUint` that `Name`'s spec returns.
-/
module

public import Proof.go_etcd_io.raft.v3.Protocol.Model
public import Proof.go_etcd_io.raft.v3.Protocol.RnMode
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Tla.Check
public import Perennial.Proof.internal.strconv.FormatBasics

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

/-! ## Names -/

/-- Go `Name(id)`: `"raft<id>"`, `""` (the binding's `Nil`) for `0`. -/
def nameOf (id : w64) : AntCheck.Str :=
  if id = W64 0 then [] else go!"raft" ++ internal.strconv.fmtUint id (W64 10)

/-- Go `names(n)`: `Name(1), ..., Name(n)`. -/
def namesL (n : Nat) : List AntCheck.Str := (List.range n).map (fun (i : Nat) => nameOf (W64 ((i : Int) + 1)))

/-- **The run's configuration** (`notes/antithesis-parity-design.md` §3.1, parity B1): servers
`raft1 … raftN`, the first `K` of them the initial voters, bootstrapped (`BootInit` written into each
node's storage, B 733-753) or not, each node's `Config` flags (`NodeK`, drawn per run), and the
batch's scope mask (`RnMode`, design R3). `N ≤ 9` keeps `setOf (namesL N) = namesL N` (string order
is numeric order for `raft1`-`raft9`); `K ≤ N` is `Server ⊇ InitVoters`. -/
structure RunCfg where
  N : Nat
  K : Nat
  boot : Bool
  k : Fin N → NodeK
  md : RnMode
  hK : 1 ≤ K ∧ K ≤ N ∧ N ≤ 9

/-- The binding's constants for the run: `Server = SetOf(names(N))`, `InitVoters = SetOf(names(K))`,
`Bootstrapped`. -/
def RunCfg.cfg (R : RunCfg) : AntCheck.Config :=
  { server := AntCheck.setOf (namesL R.N), initVoters := AntCheck.setOf (namesL R.K),
    bootstrapped := R.boot }

/-- The nodes' ids, `1, …, N` (the driver's `i`). The node at position `n` of `R.cfg.server` is
`nodeId n`. -/
def nodeId {N : Nat} (n : Fin N) : w64 := W64 ((n.val : Int) + 1)

/-- The first harness's run (S4): three servers, all voters, not bootstrapped, no flag, scope `{}`. -/
def R3 : RunCfg := { N := 3, K := 3, boot := false, k := fun _ => {}, md := {}, hK := by decide }

/-- `Main`'s configuration in S4: `Server = InitVoters = c.Servers() = check.SetOf(names(3))`,
`Bootstrapped = FALSE` (`EtcdBindingEmpty.cfg`); `R3`'s (kept while the Sim proofs migrate). -/
def cfg3 : AntCheck.Config := R3.cfg

theorem cfg3_eq : cfg3 = R3.cfg := rfl

theorem namesL_three : namesL 3 = [go!"raft1", go!"raft2", go!"raft3"] := by
  decide +kernel

theorem cfg3_server : cfg3.server = namesL 3 := by
  rw [show cfg3.server = AntCheck.setOf (namesL 3) from rfl, namesL_three]; decide +kernel

theorem cfg3_initVoters : cfg3.initVoters = namesL 3 := cfg3_server

section abs
variable [GooseExts]

open go_etcd_io.raft.v3

/-! ## Entries and logs -/

/-- Go `bootData()`: the data of the entry a bootstrapped run's node writes first (`node.start`). -/
def bootData : List w8 := go!"boot"

/-- Go `entryOf(e, n)`: the bootstrapped run's first entry (index 1, data `bootData()`) is
`"config"`; otherwise `"noop"` when its data is empty and `"command"` with the data as the value.
The index is not reported. (Go's `"conf"` arm, a membership change's value `changeOf(e, n)`, is
parity B3's: `confChanges` is off in B1's mask, so the harness's entries are normal.) -/
def entOf (e : EntryM) : AntCheck.Entry :=
  if e.Index' = W64 1 ∧ e.Data' = bootData then
    { term := uint.Z e.Term', type := go!"config", value := { str := [] } }
  else if e.Data' = [] then { term := uint.Z e.Term', type := go!"noop", value := { str := [] } }
  else { term := uint.Z e.Term', type := go!"command", value := { str := e.Data' } }

/-- A log (Go `entriesOf`). -/
def logOf (l : List EntryM) : List AntCheck.Entry := l.map entOf

/-! ## Messages -/

/-- Go `msgType(t)` (rawnode's `msgTypes`) of a protocol message type. -/
def msgTypeStr : MsgType → AntCheck.Str
  | .vote => go!"vote"
  | .voteResp => go!"voteresp"
  | .app => go!"app"
  | .appResp => go!"appresp"
  | .heartbeat => go!"hb"
  | .heartbeatResp => go!"hbresp"
  | .propose => go!"prop"
  | .snap => go!"snap"
  | .preVote => go!"prevote"
  | .preVoteResp => go!"prevoteresp"
  | .readIndex => go!"readindex"
  | .readIndexResp => go!"readindexresp"

/-- Go `msgOf(m, to)`: every field present (`check.MFAll`). A `snap`'s `index`/`logTerm` are its
snapshot's metadata in Go; the protocol message already holds them there (`Msg`'s docstring). The
Go's `Hint` is not in the transcription (the binding never reads it). -/
def msgOf (m : Msg) (to : w64) : AntCheck.Msg :=
  { type := some (msgTypeStr m.ty), frm := some (nameOf m.src), to := some (nameOf to),
    term := some (uint.Z m.term), index := some (uint.Z m.index), logTerm := some (uint.Z m.logterm),
    entries := some (logOf m.entries), commit := some (uint.Z m.commit), reject := some m.reject }

/-- Go `roleOf(s)` (raft's `StateType`) of a protocol role (`Role` has no pre-candidate: a
pre-candidate's protocol role is `.follower`, `roleStr` reports it). -/
def roleOf : Role → AntCheck.Str
  | .follower => go!"follower"
  | .candidate => go!"candidate"
  | .leader => go!"leader"

/-- Go `roleOf(s)` of a node whose protocol role is `r`, `pre` when it is a pre-candidate
(`StatePreCandidate`, the binding's `"precandidate"`, B 248-249). -/
def roleStr (pre : Bool) (r : Role) : AntCheck.Str := if pre then go!"precandidate" else roleOf r

/-- Go `msgOf(m, m.GetTo())` of a `MsgTransferLeader` or `MsgTimeoutNow` (`XMsg`): its type
(`"transfer"`, `"timeoutnow"`), sender, receiver and term; the other fields zero (the message
carries none), every one present. -/
def xmsgOf (x : XMsg) : AntCheck.Msg :=
  { type := some (match x.ty with | .transferLeader => go!"transfer" | .timeoutNow => go!"timeoutnow"),
    frm := some (nameOf x.src), to := some (nameOf x.dst), term := some (uint.Z x.term),
    index := some 0, logTerm := some 0, entries := some [], commit := some 0, reject := some false }

/-! ## The reports -/

/-- `node.start`'s `boot` report of a fresh node `id` of the run `R` (B 162-194): what it recovered,
nothing, or in a bootstrapped run the entry it wrote first (`HardState{Term: 1}` and the entry
`{1, 1, bootData()}`): term 0 or 1, vote `""`, commit 0, `lastIndex`/`lastTerm` 0 or 1, applied 0,
voters `names(K)`, no outgoing voters. -/
def evBoot (R : RunCfg) (id : w64) : AntCheck.Event :=
  { e := go!"boot", node := nameOf id, term := some (if R.boot then 1 else 0), vote := some [],
    commit := some 0, lastIndex := some (if R.boot then 1 else 0),
    lastTerm := some (if R.boot then 1 else 0), applied := some 0, voters := some (namesL R.K),
    outgoing := some [] }

/-- `node.start`'s `boot` report after a restart (parity B2): the durable hard state (`term`, `vote`,
`commit`), the stored log's last index and term (`lastIdx`, `lastTerm`), the applied index `a`, and
the configuration `c` (`storeConf`) as voters and outgoing voters. -/
def evBootR (id : w64) (term vote commit : w64) (lastIdx lastTerm : Int) (a : Nat)
    (c : AntCheck.Conf) : AntCheck.Event :=
  { e := go!"boot", node := nameOf id, term := some (uint.Z term), vote := some (nameOf vote),
    commit := some (uint.Z commit), lastIndex := some lastIdx, lastTerm := some lastTerm,
    applied := some a, voters := some c.cin, outgoing := some c.cout }

/-- `reportCause`'s `recv` report at node `id` of the message `m` it handles (`msgOf(n.cause, n.id)`). -/
def evRecv (id : w64) (m : Msg) : AntCheck.Event :=
  { e := go!"recv", node := nameOf id, msg := some (msgOf m id) }

/-- `reportCause`'s `recv` report at node `id` of a transfer message it handles (`MsgTimeoutNow`, a
forwarded `MsgTransferLeader`). -/
def evRecvX (id : w64) (x : XMsg) : AntCheck.Event :=
  { e := go!"recv", node := nameOf id, msg := some (xmsgOf x) }

/-- `int(first)` of a `ready`'s entries: the first entry's index, `0` for none. -/
def firstOf : List EntryM → Int
  | [] => 0
  | e :: _ => uint.Z e.Index'

/-- A report's `snap` (Go `snapRef`): a snapshot's index and term. -/
def snapRefOf (b : entryID) : AntCheck.SnapRef := { index := uint.Z b.index', term := uint.Z b.term' }

/-- `node`'s `ready` report at node `id`, its drain caused by `by` (`withSnap(withByRole(stateEv("ready",
hs, ents), by, role), snap)`): the reported role (`roleStr`), the term, vote and commit after the
`Ready` (its hard state or the last written one), the first index and the entries, and, for a
`Ready` with a snapshot, its index and term. -/
def evReady (id : w64) (by_ : AntCheck.Str) (role : AntCheck.Str) (term vote commit : w64)
    (es : List EntryM) (snap : Option entryID := none) : AntCheck.Event :=
  { e := go!"ready", node := nameOf id, byE := some by_, role := some role,
    term := some (uint.Z term), vote := some (nameOf vote), commit := some (uint.Z commit),
    first := some (firstOf es), entries := some (logOf es), snap := snap.map snapRefOf }

/-- A report with rawnode's `state` fields (Go `stateEv(e, hs, ents)`): term, vote, commit, first
index, entries. -/
def stateEv (e : AntCheck.Str) (id : w64) (term vote commit : w64) (es : List EntryM) :
    AntCheck.Event :=
  { e := e, node := nameOf id, term := some (uint.Z term), vote := some (nameOf vote),
    commit := some (uint.Z commit), first := some (firstOf es), entries := some (logOf es) }

/-- Async (parity B2): the `mem` report of what raft has in memory at a `Ready` whose write comes
later (`withSnap(withByRole(stateEv("mem", hs, rd.Entries), by, role), snap)`). -/
def evMem (id : w64) (by_ role : AntCheck.Str) (term vote commit : w64) (es : List EntryM)
    (snap : Option entryID) : AntCheck.Event :=
  { e := go!"mem", node := nameOf id, byE := some by_, role := some role,
    term := some (uint.Z term), vote := some (nameOf vote), commit := some (uint.Z commit),
    first := some (firstOf es), entries := some (logOf es), snap := snap.map snapRefOf }

/-- Async (parity B2): the storage goroutine's `write` report (`stateEv("write", after, ents)`, with
the snapshot it writes). -/
def evWrite (id : w64) (term vote commit : w64) (es : List EntryM) (snap : Option entryID) :
    AntCheck.Event :=
  { e := go!"write", node := nameOf id, term := some (uint.Z term), vote := some (nameOf vote),
    commit := some (uint.Z commit), first := some (firstOf es), entries := some (logOf es),
    snap := snap.map snapRefOf }

/-- The `wrote` report (a write is made and the messages after it may go). -/
def evWrote (id : w64) : AntCheck.Event := { e := go!"wrote", node := nameOf id }

/-- Batch (parity B2): the `made` report (the batch's write is on disk). -/
def evMade (id : w64) : AntCheck.Event := { e := go!"made", node := nameOf id }

/-- Batch (parity B2): a `flush` report (`more` = 1 for every flushed `mem` after the first). -/
def evFlush (id : w64) (more : Bool) : AntCheck.Event :=
  { e := go!"flush", node := nameOf id, more := some (if more then 1 else 0) }

/-- Batch (parity B2): the `net` report of a batch's write (`stateEv("net", hs, ents)`). -/
def evNet (id : w64) (term vote commit : w64) (es : List EntryM) : AntCheck.Event :=
  stateEv go!"net" id term vote commit es

/-- `drain`'s `send` report at node `id` of the `Ready`'s message `m` (`msgOf(m, m.GetTo())`). -/
def evSend (id : w64) (by_ : AntCheck.Str) (m : Msg) : AntCheck.Event :=
  { e := go!"send", node := nameOf id, byE := some by_, msg := some (msgOf m m.dst) }

/-- Batch (parity B2): a batch's `send` (`batchSendEv`: the field `b`). -/
def evSendB (id : w64) (by_ : AntCheck.Str) (m : Msg) : AntCheck.Event :=
  { (evSend id by_ m) with b := true }

/-- Async (parity B2): a `send` after its write (`causeSendEv`: the message that caused it, if any,
as reported at its `recv`). -/
def evSendC (id : w64) (by_ : AntCheck.Str) (m : Msg) (cause : Option Msg) : AntCheck.Event :=
  { (evSend id by_ m) with cause := some ((cause.map (fun c => msgOf c id)).toList) }

/-- The `send` report of a `MsgTransferLeader` or `MsgTimeoutNow` (`sendEv(by, m)`; the binding's
`isUnmodelled`, B 702). -/
def evSendX (id : w64) (by_ : AntCheck.Str) (x : XMsg) : AntCheck.Event :=
  { e := go!"send", node := nameOf id, byE := some by_, msg := some (xmsgOf x) }

/-- `drain`'s `apply` report at node `id` of the `Ready`'s committed entries `ce` (not empty: the
harness reports none otherwise). -/
def evApply (id : w64) (by_ : AntCheck.Str) (ce : List EntryM) : AntCheck.Event :=
  { e := go!"apply", node := nameOf id, byE := some by_, first := some (firstOf ce),
    entries := some (logOf ce) }

/-- Async (parity B2): the apply goroutine's `apply` (the field `a`). -/
def evApplyA (id : w64) (by_ : AntCheck.Str) (ce : List EntryM) : AntCheck.Event :=
  { (evApply id by_ ce) with a := true }

/-- Parity B3: a membership change applied (`confEv("conf", index, cs)`): its index and the
configuration after it. -/
def evConf (id : w64) (k : Nat) (c : AntCheck.Conf) : AntCheck.Event :=
  { e := go!"conf", node := nameOf id, index := some k, voters := some c.cin, outgoing := some c.cout }

/-- Parity B3: a snapshot restored (`confEv("restore", index, cs)`, `a` when the apply goroutine
reports it). -/
def evRestore (id : w64) (k : Nat) (c : AntCheck.Conf) (a : Bool) : AntCheck.Event :=
  { e := go!"restore", node := nameOf id, index := some k, voters := some c.cin,
    outgoing := some c.cout, a := a }

/-- Parity B3: a snapshot taken (`snap`: its index and term). -/
def evSnap (id : w64) (k : Nat) (t : w64) : AntCheck.Event :=
  { e := go!"snap", node := nameOf id, index := some k, term := some (uint.Z t) }

/-- The reader's `readreq` report: the read context asked (`ReadIndex(ctx)`). -/
def evReadReq (id : w64) (ctx : AntCheck.Str) : AntCheck.Event :=
  { e := go!"readreq", node := nameOf id, ctx := some ctx }

/-- A `Ready`'s read state reported (`read`: the context and the read index). -/
def evRead (id : w64) (ctx : AntCheck.Str) (i : w64) : AntCheck.Event :=
  { e := go!"read", node := nameOf id, ctx := some ctx, index := some (uint.Z i) }

end abs

end AntSim
end EtcdGrove
end Perennial
