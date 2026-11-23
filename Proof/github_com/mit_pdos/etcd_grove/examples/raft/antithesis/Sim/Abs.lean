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

Pure: imports only raft's protocol model and the transcription (and Perennial's `fmtUint`, the
model of `strconv.FormatUint` that `Name`'s spec returns).
-/
module

public import Proof.go_etcd_io.raft.v3.Protocol.Model
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

/-- `Main`'s configuration: `Server = InitVoters = c.Servers() = check.SetOf(names(3))`,
`Bootstrapped = FALSE` (`EtcdBindingEmpty.cfg`). -/
def cfg3 : AntCheck.Config :=
  { server := AntCheck.setOf (namesL 3), initVoters := AntCheck.setOf (namesL 3), bootstrapped := false }

/-- The three nodes' ids, `1, 2, 3` (`RunCluster`'s `i`). The node at position `n` of
`cfg3.server` is `nodeId n`. -/
def nodeId (n : Fin 3) : w64 := W64 ((n.val : Int) + 1)

theorem namesL_three : namesL 3 = [go!"raft1", go!"raft2", go!"raft3"] := by
  decide +kernel

theorem cfg3_server : cfg3.server = namesL 3 := by
  rw [show cfg3.server = AntCheck.setOf (namesL 3) from rfl, namesL_three]; decide +kernel

theorem cfg3_initVoters : cfg3.initVoters = namesL 3 := cfg3_server

section abs
variable [GooseExts]

/-! ## Entries and logs -/

/-- Go `entryOf(e)` of a normal entry (the harness panics on any other, which the S4 proof
excludes: `entryOf`'s spec takes `e.Type' = EntryNormal`): `"noop"` when its data is empty,
`"command"` with the data as the value otherwise. The index is not reported. -/
def entOf (e : EntryM) : AntCheck.Entry :=
  if e.Data' = [] then { term := uint.Z e.Term', type := go!"noop", value := { str := [] } }
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

/-- Go `roleOf(s)` (raft's `StateType`; pre-candidate never arises: pre-vote is off). -/
def roleOf : Role → AntCheck.Str
  | .follower => go!"follower"
  | .candidate => go!"candidate"
  | .leader => go!"leader"

/-! ## The reports -/

/-- `RunCluster`'s `boot` report of node `id`: what it recovered (nothing): term 0, vote `""`,
commit 0, `lastIndex`/`lastTerm` 0 (Go: the fields' zero values, their `Has` bits set), applied 0,
voters `names(3)`, no outgoing voters. -/
def evBoot (id : w64) : AntCheck.Event :=
  { e := go!"boot", node := nameOf id, term := some 0, vote := some [], commit := some 0,
    lastIndex := some 0, lastTerm := some 0, applied := some 0, voters := some (namesL 3),
    outgoing := some [] }

/-- `reportCause`'s `recv` report at node `id` of the message `m` it handles (`msgOf(n.cause, n.id)`). -/
def evRecv (id : w64) (m : Msg) : AntCheck.Event :=
  { e := go!"recv", node := nameOf id, msg := some (msgOf m id) }

/-- `int(first)` of a `ready`'s entries: the first entry's index, `0` for none. -/
def firstOf : List EntryM → Int
  | [] => 0
  | e :: _ => uint.Z e.Index'

/-- `drain`'s `ready` report at node `id`, its drain caused by `by`: the role, term, vote and
commit after the `Ready` (`role`, and `term vote commit` the `Ready`'s hard state or the last
written one: under the relation, the node's at the `Ready`), the first index and the entries. -/
def evReady (id : w64) (by_ : AntCheck.Str) (role : Role) (term vote commit : w64)
    (es : List EntryM) : AntCheck.Event :=
  { e := go!"ready", node := nameOf id, byE := some by_, role := some (roleOf role),
    term := some (uint.Z term), vote := some (nameOf vote), commit := some (uint.Z commit),
    first := some (firstOf es), entries := some (logOf es) }

/-- `drain`'s `send` report at node `id` of the `Ready`'s message `m` (`msgOf(m, m.GetTo())`). -/
def evSend (id : w64) (by_ : AntCheck.Str) (m : Msg) : AntCheck.Event :=
  { e := go!"send", node := nameOf id, byE := some by_, msg := some (msgOf m m.dst) }

/-- `drain`'s `apply` report at node `id` of the `Ready`'s committed entries `ce` (not empty: the
harness reports none otherwise). -/
def evApply (id : w64) (by_ : AntCheck.Str) (ce : List EntryM) : AntCheck.Event :=
  { e := go!"apply", node := nameOf id, byE := some by_, first := some (firstOf ce),
    entries := some (logOf ce) }

end abs

end AntSim
end EtcdGrove
end Perennial
