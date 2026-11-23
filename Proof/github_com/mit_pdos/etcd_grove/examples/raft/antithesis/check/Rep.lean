/-
Lean-first (no Rocq counterpart).

# The Go checker's values, related to the Lean transcription (#33 S3b, 2026-11-23)

The checker's specs (`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/check/`) relate
the Go transcription's values (package `check`, translated by Goose) to the Lean transcription's
(`Tla/`, namespace `AntCheck`). Everything the checker reads is read-only once built (a stream's
events and a configuration are never written; a `State` is never written once built: an action
builds its successor from copies, `state.go`), so every predicate here is persistent (`↦□`,
`↦*□`), as tracecheck's (`Proof/.../tracecheck/etcdraft/Rep.lean`).

Strings are `GoString`s on both sides (the relation is equality). Numbers: the Lean's are `Int`,
the Go's 64-bit `int`, read signed (`sint.Z`); the stream's numbers and sizes are kept far from
overflow by `Stream.Bounded` (below `numBound`). A report's optional field is an `Option` in the
Lean and a `Has` bit in the Go (`fieldRel`): the Go's value of an absent field is unconstrained,
since the checker reads a field only after `need` finds its bit.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Tla.Check

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI

section types
variable [GooseExts]

/-- The Go package's types, by their short names. -/
abbrev G.Value := github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Value
abbrev G.Entry := github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Entry
abbrev G.Msg := github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg
abbrev G.SnapRef := github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.SnapRef
abbrev G.Event := github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event
abbrev G.Config := github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Config
abbrev G.Verdict := github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Verdict
abbrev G.Conf := github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Conf
abbrev G.Fact := github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Fact
abbrev G.VoteRec := github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.VoteRec
abbrev G.LeaderRec := github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.LeaderRec
abbrev G.Confirmed := github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Confirmed
abbrev G.TermLog := github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermLog
abbrev G.TermConf := github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermConf
abbrev G.TermInt := github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermInt
abbrev G.Pre := github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Pre
abbrev G.QItem := github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.QItem
abbrev G.ReadRec := github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.ReadRec
abbrev G.State := github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State
abbrev G.AppendFact := github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.AppendFact

end types

/-! ## Bounds -/

/-- The bound on the stream's numbers and on its size: a sum of three numbers below it, or of a
number and a length, stays within the Go `int` (`first + len(entries) - 1`, `prevLogIndex + k`,
`T0 + 1`; every list the checker builds is a sublist of the stream's entries put together, so no
longer than the stream's size), and as high as that allows (tracecheck's `numBound`, Q12 (a): the
closed statement's step bound, `n < 2^61`, bounds what a run reports). -/
def numBound : Int := 2 ^ 61

/-- A number of the stream within `numBound`, either sign (TLC's numbers are any 32-bit ones). -/
def numOk (x : Int) : Prop := -numBound < x ∧ x < numBound

/-- An optional number within `numBound`. -/
def optNumOk : Option Int → Prop
  | none => True
  | some x => numOk x

/-- The entries' numbers within `numBound`. -/
def entriesOk (es : List Entry) : Prop := ∀ e ∈ es, numOk e.term

/-- A reported message's numbers within `numBound`. -/
def Msg.NumsOk (m : Msg) : Prop :=
  optNumOk m.term ∧ optNumOk m.index ∧ optNumOk m.logTerm ∧ optNumOk m.commit ∧
  ∀ es, m.entries = some es → entriesOk es

/-- The entries a message carries (0 if it has none). -/
def Msg.size (m : Msg) : Nat := (m.entries.getD []).length

/-- A report's numbers within `numBound`. -/
def Event.NumsOk (ev : Event) : Prop :=
  optNumOk ev.term ∧ optNumOk ev.commit ∧ optNumOk ev.first ∧ optNumOk ev.lastIndex ∧
  optNumOk ev.lastTerm ∧ optNumOk ev.applied ∧ optNumOk ev.w ∧ optNumOk ev.more ∧
  optNumOk ev.index ∧ (∀ s, ev.snap = some s → numOk s.index ∧ numOk s.term) ∧
  (∀ es, ev.entries = some es → entriesOk es) ∧ (∀ m, ev.msg = some m → m.NumsOk) ∧
  (∀ ms, ev.cause = some ms → ∀ m ∈ ms, m.NumsOk)

/-- A report's size: its entries, its messages' entries, its lists of names and messages. -/
def Event.size (ev : Event) : Nat :=
  (ev.entries.getD []).length + (ev.msg.map Msg.size).getD 0 +
  ((ev.cause.getD []).map Msg.size).sum + (ev.cause.getD []).length +
  (ev.voters.getD []).length + (ev.outgoing.getD []).length

/-- **The stream's numbers and size within `numBound`** (`Run`'s premise for the Go `int`): every
number of every report, and the number of reports plus their sizes. -/
def Stream.Bounded (evs : List Event) : Prop :=
  ((evs.length + (evs.map Event.size).sum : Nat) : Int) < numBound ∧ ∀ ev ∈ evs, ev.NumsOk

/-- The configuration's sets within `numBound` (`Majority`'s `Cardinality(...) * 2`). -/
def Config.Bounded (cfg : Config) : Prop :=
  (cfg.server.length : Int) < numBound ∧ (cfg.initVoters.length : Int) < numBound

/-- The sizes a configuration change can add (`ConfOf`'s sets grow by its changes' `add`s; `SetOf`
of a change's `remove`). -/
def Entry.chgSize (e : Entry) : Nat := e.value.add.length + e.value.remove.length

/-- `ConfOf(l, a)` from `c0`: the sets it builds far from overflow (`Majority`'s `* 2`, `SetAdd`'s
`len + 1`). -/
def ConfOf.Bounded (l : List Entry) (c0 : Conf) : Prop :=
  ((c0.cin.length + c0.cout.length + (l.map Entry.chgSize).sum : Nat) : Int) < 2 ^ 61

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

/-! ## Optional fields -/

/-- `bit` is set in `has` (Go: `Has&bit != 0`). -/
def hasBit (has bit : w32) : Prop := (has &&& bit) ≠ W32 0

/-- A report's optional field: absent, its bit clear; present, its bit set and the Go value
`rel`-related to the Lean's. -/
def fieldRel {α β : Type} (has bit : w32) (rel : α → β → Prop) (g : α) : Option β → Prop
  | none => ¬ hasBit has bit
  | some b => hasBit has bit ∧ rel g b

/-- `fieldRel` for a field compared by `=` (a string, a boolean). -/
abbrev fieldIs {α : Type} (has bit : w32) (g : α) (o : Option α) : Prop := fieldRel has bit (· = ·) g o

/-- `fieldRel` for an `int` field. -/
abbrev fieldZ (has bit : w32) (g : w64) (o : Option Int) : Prop :=
  fieldRel has bit (fun g x => sint.Z g = x) g o

/-- An optional field held in memory (a slice): absent, its bit clear; present, its bit set and
`rep` of the Go value. -/
def fieldRO {α β : Type} (has bit : w32) (rep : α → β → IProp GF) (g : α) : Option β → IProp GF
  | none => iprop(⌜¬ hasBit has bit⌝)
  | some b => iprop(⌜hasBit has bit⌝ ∗ rep g b)

/-! ## Strings, values, entries, messages -/

/-- A Go `[]string` (a `Set` among them) holding `xs`. -/
def strsRO (sl : GoSlice) (xs : List Str) : IProp GF := iprop(sl ↦*□ xs)

/-- A Go `Value` holding `w`. -/
def valueRO (v : G.Value) (w : Value) : IProp GF :=
  iprop(⌜v.IsRec' = w.isRec ∧ v.Str' = w.str ∧ v.Joint' = w.joint ∧ v.Leave' = w.leave⌝ ∗
    strsRO v.Add' w.add ∗ strsRO v.Remove' w.remove)

/-- A Go `Entry` holding `x`. -/
def entryRO (e : G.Entry) (x : Entry) : IProp GF :=
  iprop(⌜sint.Z e.Term' = x.term ∧ e.Type' = x.type⌝ ∗ valueRO e.Value' x.value)

/-- A Go `[]Entry` holding `l`. -/
def logRO (sl : GoSlice) (l : List Entry) : IProp GF :=
  iprop(∃ es : List G.Entry, sl ↦*□ es ∗ [∗list] e;x ∈ es;l, entryRO e x)

/-- The bits of `Msg.Has` (`event.go`'s `MF*`). -/
def mfType : w32 := W32 1
def mfFrom : w32 := W32 2
def mfTo : w32 := W32 4
def mfTerm : w32 := W32 8
def mfIndex : w32 := W32 16
def mfLogTerm : w32 := W32 32
def mfEntries : w32 := W32 64
def mfCommit : w32 := W32 128
def mfReject : w32 := W32 256

/-- A Go `Msg` (a value) holding `m`. -/
def msgRO (g : G.Msg) (m : Msg) : IProp GF :=
  iprop(⌜fieldIs g.Has' mfType g.Type' m.type ∧ fieldIs g.Has' mfFrom g.From' m.frm ∧
      fieldIs g.Has' mfTo g.To' m.to ∧ fieldZ g.Has' mfTerm g.Term' m.term ∧
      fieldZ g.Has' mfIndex g.Index' m.index ∧ fieldZ g.Has' mfLogTerm g.LogTerm' m.logTerm ∧
      fieldZ g.Has' mfCommit g.Commit' m.commit ∧ fieldIs g.Has' mfReject g.Reject' m.reject⌝ ∗
    fieldRO g.Has' mfEntries logRO g.Entries' m.entries)

/-- A Go `[]Msg` holding `ms`. -/
def msgsRO (sl : GoSlice) (ms : List Msg) : IProp GF :=
  iprop(∃ gs : List G.Msg, sl ↦*□ gs ∗ [∗list] g;m ∈ gs;ms, msgRO g m)

/-! ## Reports and the configuration -/

/-- The bits of `Event.Has` (`event.go`'s `F*`). -/
def fBy : w32 := W32 1
def fRole : w32 := W32 2
def fTerm : w32 := W32 4
def fVote : w32 := W32 8
def fCommit : w32 := W32 16
def fFirst : w32 := W32 32
def fEntries : w32 := W32 64
def fLastIndex : w32 := W32 128
def fLastTerm : w32 := W32 256
def fApplied : w32 := W32 512
def fVoters : w32 := W32 1024
def fOutgoing : w32 := W32 2048
def fSnap : w32 := W32 4096
def fMsg : w32 := W32 8192
def fCause : w32 := W32 16384
def fB : w32 := W32 32768
def fA : w32 := W32 65536
def fW : w32 := W32 131072
def fMore : w32 := W32 262144
def fIndex : w32 := W32 524288
def fCtx : w32 := W32 1048576

/-- A Go `SnapRef` holding `s`. -/
def snapRel (g : G.SnapRef) (s : SnapRef) : Prop := sint.Z g.Index' = s.index ∧ sint.Z g.Term' = s.term

/-- `ev.has(f)` (Go: `Event.has`): whether the report has the field of bit `f`, for the bits the
checker tests (`none` for another `f`). -/
def Event.hasF (ev : Event) (f : w32) : Option Bool :=
  if f = fBy then some ev.byE.isSome else if f = fRole then some ev.role.isSome
  else if f = fTerm then some ev.term.isSome else if f = fVote then some ev.vote.isSome
  else if f = fCommit then some ev.commit.isSome else if f = fFirst then some ev.first.isSome
  else if f = fEntries then some ev.entries.isSome else if f = fLastIndex then some ev.lastIndex.isSome
  else if f = fLastTerm then some ev.lastTerm.isSome else if f = fApplied then some ev.applied.isSome
  else if f = fVoters then some ev.voters.isSome else if f = fOutgoing then some ev.outgoing.isSome
  else if f = fSnap then some ev.snap.isSome else if f = fMsg then some ev.msg.isSome
  else if f = fCause then some ev.cause.isSome else if f = fB then some ev.b
  else if f = fA then some ev.a else if f = fW then some ev.w.isSome
  else if f = fMore then some ev.more.isSome else if f = fIndex then some ev.index.isSome
  else if f = fCtx then some ev.ctx.isSome else none

/-- A Go `*Event` holding `ev`. -/
def eventRO (p : Loc) (ev : Event) : IProp GF :=
  iprop(∃ g : G.Event, p ↦□ g ∗
    ⌜g.E' = ev.e ∧ g.Node' = ev.node ∧ g.Bad' = ev.bad ∧
      (hasBit g.Has' fB ↔ ev.b = true) ∧ (hasBit g.Has' fA ↔ ev.a = true) ∧
      fieldIs g.Has' fBy g.By' ev.byE ∧ fieldIs g.Has' fRole g.Role' ev.role ∧
      fieldZ g.Has' fTerm g.Term' ev.term ∧ fieldIs g.Has' fVote g.Vote' ev.vote ∧
      fieldZ g.Has' fCommit g.Commit' ev.commit ∧ fieldZ g.Has' fFirst g.First' ev.first ∧
      fieldZ g.Has' fLastIndex g.LastIdx' ev.lastIndex ∧ fieldZ g.Has' fLastTerm g.LastTerm' ev.lastTerm ∧
      fieldZ g.Has' fApplied g.Applied' ev.applied ∧ fieldRel g.Has' fSnap snapRel g.Snap' ev.snap ∧
      fieldZ g.Has' fW g.W' ev.w ∧ fieldZ g.Has' fMore g.More' ev.more ∧
      fieldZ g.Has' fIndex g.Index' ev.index ∧ fieldIs g.Has' fCtx g.Ctx' ev.ctx⌝ ∗
    fieldRO g.Has' fEntries logRO g.Entries' ev.entries ∗
    fieldRO g.Has' fVoters strsRO g.Voters' ev.voters ∗
    fieldRO g.Has' fOutgoing strsRO g.Outgoing' ev.outgoing ∗
    fieldRO g.Has' fMsg msgRO g.Msg' ev.msg ∗
    fieldRO g.Has' fCause msgsRO g.Cause' ev.cause)

/-- A Go `[]*Event` holding the stream `evs`. -/
def eventsRO (sl : GoSlice) (evs : List Event) : IProp GF :=
  iprop(∃ ps : List Loc, sl ↦*□ ps ∗ [∗list] p;ev ∈ ps;evs, eventRO p ev)

/-- A Go `*Config` holding `cfg`. -/
def configRO (p : Loc) (cfg : Config) : IProp GF :=
  iprop(∃ g : G.Config, p ↦□ g ∗ strsRO g.Server' cfg.server ∗ strsRO g.InitVoters' cfg.initVoters ∗
    ⌜g.Bootstrapped' = cfg.bootstrapped⌝)

/-- A Go `AppendFact` (a value) holding `m`. -/
def appendFactRO (g : G.AppendFact) (m : AppendFact) : IProp GF :=
  iprop(⌜g.Src' = m.src ∧ g.Dst' = m.dst ∧ sint.Z g.Term' = m.term ∧ sint.Z g.PrevLogIndex' = m.prevLogIndex ∧
      sint.Z g.PrevLogTerm' = m.prevLogTerm ∧ sint.Z g.Commit' = m.commit⌝ ∗ logRO g.Entries' m.entries)

/-! ## Verdicts -/

/-- The Go `Kind` of a verdict's kind (`Accepted` .. `Error`, `iota`'s). -/
def kindW : Kind → w64
  | .accepted => W64 0 | .rejected => W64 1 | .violated => W64 2 | .error => W64 3

/-- A Go `Verdict` holding `v` (`Err` empty: `Run` never sets it). -/
def verdictRO (r : G.Verdict) (v : Verdict) : IProp GF :=
  iprop(⌜r.Kind' = kindW v.kind ∧ sint.Z r.K' = v.k ∧ r.Err' = []⌝ ∗ strsRO r.Names' v.names)

/-! ## States (`state.go`; the laws to read and build them: `StateLaws.lean`) -/

/-- A Go `[]int` holding `xs`. -/
def intsRO (sl : GoSlice) (xs : List Int) : IProp GF :=
  iprop(∃ ws : List w64, sl ↦*□ ws ∗ ⌜ws.map sint.Z = xs⌝)

/-- A Go `Conf` holding `c`. -/
def confRO (g : G.Conf) (c : Conf) : IProp GF := iprop(strsRO g.In' c.cin ∗ strsRO g.Out' c.cout)

/-- A Go `[]Conf` holding `cs`. -/
def confsRO (sl : GoSlice) (cs : List Conf) : IProp GF :=
  iprop(∃ gs : List G.Conf, sl ↦*□ gs ∗ [∗list] g;c ∈ gs;cs, confRO g c)

/-- A Go `[][]Entry` holding `ls`. -/
def logsRO (sl : GoSlice) (ls : List (List Entry)) : IProp GF :=
  iprop(∃ gs : List GoSlice, sl ↦*□ gs ∗ [∗list] g;l ∈ gs;ls, logRO g l)

/-- A Go `Fact` holding `f` (every field: Go's `==` on `Fact`s is the Lean's `=`). -/
def factRel (g : G.Fact) (f : Fact) : Prop :=
  g.Type' = f.type ∧ g.Src' = f.src ∧ g.Dst' = f.dst ∧ sint.Z g.Term' = f.term ∧
  sint.Z g.LastLogIndex' = f.lastLogIndex ∧ sint.Z g.LastLogTerm' = f.lastLogTerm ∧ sint.Z g.Index' = f.index

/-- A Go `[]Fact` holding `fs`. -/
def factsRO (sl : GoSlice) (fs : List Fact) : IProp GF :=
  iprop(∃ gs : List G.Fact, sl ↦*□ gs ∗ ⌜List.Forall₂ factRel gs fs⌝)

/-- A Go `VoteRec` holding `v`. -/
def voteRel (g : G.VoteRec) (v : VoteRec) : Prop :=
  g.Voter' = v.voter ∧ sint.Z g.Term' = v.term ∧ g.Cand' = v.cand

/-- A Go `[]VoteRec` holding `vs`. -/
def votesRO (sl : GoSlice) (vs : List VoteRec) : IProp GF :=
  iprop(∃ gs : List G.VoteRec, sl ↦*□ gs ∗ ⌜List.Forall₂ voteRel gs vs⌝)

/-- A Go `[]LeaderRec` holding `ls`. -/
def leadersRO (sl : GoSlice) (ls : List LeaderRec) : IProp GF :=
  iprop(∃ gs : List G.LeaderRec, sl ↦*□ gs ∗
    ⌜List.Forall₂ (fun (g : G.LeaderRec) (l : LeaderRec) => g.Server' = l.server ∧ sint.Z g.Term' = l.term) gs ls⌝)

/-- A Go `Confirmed` holding `c`. -/
def confirmedRel (g : G.Confirmed) (c : Confirmed) : Prop := sint.Z g.Term' = c.term ∧ sint.Z g.Index' = c.index

/-- A Go `[]Confirmed` holding `cs`. -/
def confirmedsRO (sl : GoSlice) (cs : List Confirmed) : IProp GF :=
  iprop(∃ gs : List G.Confirmed, sl ↦*□ gs ∗ ⌜List.Forall₂ confirmedRel gs cs⌝)

/-- A Go `TermLogs` holding `f`. -/
def termLogsRO (sl : GoSlice) (f : TermFn (List Entry)) : IProp GF :=
  iprop(∃ gs : List G.TermLog, sl ↦*□ gs ∗
    [∗list] g;p ∈ gs;f, ⌜sint.Z g.T' = p.1⌝ ∗ logRO g.L' p.2)

/-- A Go `TermConfs` holding `f`. -/
def termConfsRO (sl : GoSlice) (f : TermFn Conf) : IProp GF :=
  iprop(∃ gs : List G.TermConf, sl ↦*□ gs ∗
    [∗list] g;p ∈ gs;f, ⌜sint.Z g.T' = p.1⌝ ∗ confRO g.C' p.2)

/-- A Go `TermInts` holding `f`. -/
def termIntsRO (sl : GoSlice) (f : TermFn Int) : IProp GF :=
  iprop(∃ gs : List G.TermInt, sl ↦*□ gs ∗
    ⌜List.Forall₂ (fun (g : G.TermInt) (p : Int × Int) => sint.Z g.T' = p.1 ∧ sint.Z g.V' = p.2) gs f⌝)

/-- A Go `*Pre` holding `o`: nil for `none` (`NoWrite`). -/
def preRO (p : Loc) (o : Option Pre) : IProp GF :=
  match o with
  | none => iprop(⌜p = null⌝)
  | some u => iprop(∃ g : G.Pre, p ↦□ g ∗
      ⌜sint.Z g.Term' = u.term ∧ sint.Z g.VoteTerm' = u.voteTerm ∧ g.VoteFor' = u.voteFor ∧
        sint.Z g.Commit' = u.commit ∧ sint.Z g.Keep' = u.keep ∧ confirmedRel g.Confirmed' u.confirmed ∧
        sint.Z g.Low' = u.low ∧ g.Made' = u.made⌝ ∗
      logRO g.Suffix' u.suffix ∗ factsRO g.Msgs' u.msgs ∗ votesRO g.Votes' u.votes ∗ factsRO g.Acks' u.acks)

/-- A Go `[]*Pre` holding `us`. -/
def undoRO (sl : GoSlice) (us : List (Option Pre)) : IProp GF :=
  iprop(∃ ps : List Loc, sl ↦*□ ps ∗ [∗list] p;u ∈ ps;us, preRO p u)

/-- A Go `[][]Msg` holding `ms`. -/
def pendingRO (sl : GoSlice) (ms : List (List Msg)) : IProp GF :=
  iprop(∃ gs : List GoSlice, sl ↦*□ gs ∗ [∗list] g;m ∈ gs;ms, msgsRO g m)

/-- A Go `QItem` holding `q`. -/
def qitemRO (g : G.QItem) (q : QItem) : IProp GF := iprop(eventRO g.Ev' q.ev ∗ msgsRO g.M' q.m)

/-- A Go `[]QItem` holding `q` (a node's queue). -/
def qitemsRO (sl : GoSlice) (q : List QItem) : IProp GF :=
  iprop(∃ items : List G.QItem, sl ↦*□ items ∗ [∗list] i;x ∈ items;q, qitemRO i x)

/-- A Go `[][]QItem` holding `qs`. -/
def queueRO (sl : GoSlice) (qs : List (List QItem)) : IProp GF :=
  iprop(∃ gs : List GoSlice, sl ↦*□ gs ∗ [∗list] g;q ∈ gs;qs, qitemsRO g q)

/-- A Go `ReadRec` holding `r`. -/
def readRel (i : G.ReadRec) (r : ReadRec) : Prop := i.Ctx' = r.ctx ∧ sint.Z i.Floor' = r.floor

/-- A Go `[]ReadRec` holding `r` (a node's reads). -/
def readRecsRO (sl : GoSlice) (r : List ReadRec) : IProp GF :=
  iprop(∃ items : List G.ReadRec, sl ↦*□ items ∗ ⌜List.Forall₂ readRel items r⌝)

/-- A Go `[][]ReadRec` holding `rs`. -/
def readsRO (sl : GoSlice) (rs : List (List ReadRec)) : IProp GF :=
  iprop(∃ gs : List GoSlice, sl ↦*□ gs ∗ [∗list] g;r ∈ gs;rs, readRecsRO g r)

/-- The shape of a state: every function on `Server` (a per-server list) has one entry per server
(the Go indexes its slices by `idx`'s positions). Every state the checker builds has it (`init0`,
and every successor, which `List.set`s these lists). -/
def State.Wf (s : State) : Prop :=
  s.currentTerm.length = s.cfg.server.length ∧ s.voteTerm.length = s.cfg.server.length ∧
  s.voteFor.length = s.cfg.server.length ∧ s.log.length = s.cfg.server.length ∧
  s.commitIndex.length = s.cfg.server.length ∧ s.role.length = s.cfg.server.length ∧
  s.lastApplied.length = s.cfg.server.length ∧ s.config.length = s.cfg.server.length ∧
  s.confAt.length = s.cfg.server.length ∧ s.confirmed.length = s.cfg.server.length ∧
  s.undo.length = s.cfg.server.length ∧ s.pending.length = s.cfg.server.length ∧
  s.queue.length = s.cfg.server.length ∧ s.reads.length = s.cfg.server.length

/-- A Go `State` value `g` holding `s`: each field (named `H<Field>`, for `iNamed`) holds the Lean
state's variable, and the state has its shape (`State.Wf`). Persistent: what a state's fields
point to is never written. -/
def stateFields (g : G.State) (s : State) : IProp GF :=
  iprop("HCfg" ∷ configRO g.Cfg' s.cfg ∗
    "HCurrentTerm" ∷ intsRO g.CurrentTerm' s.currentTerm ∗ "HVoteTerm" ∷ intsRO g.VoteTerm' s.voteTerm ∗
    "HVoteFor" ∷ strsRO g.VoteFor' s.voteFor ∗ "HLog" ∷ logsRO g.Log' s.log ∗
    "HCommitIndex" ∷ intsRO g.CommitIndex' s.commitIndex ∗ "HRole" ∷ strsRO g.Role' s.role ∗
    "HLastApplied" ∷ intsRO g.LastApplied' s.lastApplied ∗ "HConfig" ∷ confsRO g.Config' s.config ∗
    "HConfAt" ∷ intsRO g.ConfAt' s.confAt ∗ "HConfirmed" ∷ confirmedsRO g.Confirmed' s.confirmed ∗
    "HMsgs" ∷ factsRO g.Msgs' s.msgs ∗ "HVotes" ∷ votesRO g.Votes' s.votes ∗
    "HLeaders" ∷ leadersRO g.Leaders' s.leaders ∗ "HLedLog" ∷ termLogsRO g.LedLog' s.ledLog ∗
    "HLedConf" ∷ termConfsRO g.LedConf' s.ledConf ∗ "HLedAt" ∷ termIntsRO g.LedAt' s.ledAt ∗
    "HElAt" ∷ termIntsRO g.ElAt' s.elAt ∗ "%HI" ∷ ⌜sint.Z g.I' = s.i⌝ ∗
    "HUndo" ∷ undoRO g.Undo' s.undo ∗ "HPending" ∷ pendingRO g.Pending' s.pending ∗
    "HQueue" ∷ queueRO g.Queue' s.queue ∗ "HReads" ∷ readsRO g.Reads' s.reads ∗
    "HChain" ∷ logRO g.Chain' s.chain ∗ "HTermLen" ∷ termIntsRO g.TermLen' s.termLen ∗
    "HViol" ∷ strsRO g.Viol' s.viol ∗ "%HWf" ∷ ⌜s.Wf⌝)

/-- A Go `*State` holding `s`, read-only (a state is never written once built: `Run`'s states,
an action's argument). -/
def stateRO (p : Loc) (s : State) : IProp GF :=
  iprop(∃ g : G.State, "Hp" ∷ p ↦□ g ∗ "Hf" ∷ stateFields g s)

/-- A Go `*State` holding `s`, the struct owned (a successor being built: `clone`'s result, whose
fields an action then sets; `Step` sets `I`). Frozen into `stateRO` by `stateOwn_persist`. -/
def stateOwn (p : Loc) (s : State) : IProp GF :=
  iprop(∃ g : G.State, "Hp" ∷ p ↦ g ∗ "Hf" ∷ stateFields g s)

/-- An action's result `(ns, ok)` (Go: `(*State, bool)`) holding the Lean action's `Option State`:
`none` (the TLA+ action is false) is `ok = false`, `some s` an owned successor holding `s`. -/
def succOwn (q : Loc) (ok : Bool) : Option State → IProp GF
  | none => iprop(⌜ok = false⌝)
  | some s => iprop(⌜ok = true⌝ ∗ stateOwn q s)

/-- **The spec of an action of `Bind`** (`binding.go`'s `Boot` .. `ReadGiven`, and `Bind`):
`s.<name>(n, ev)` on a read-only state, server `n` (a position `idx` returned) and a report, where
the Lean action `act` evaluates (to `o`), returns `act`'s successor, owned (`Step` then sets its
`I`), or `ok = false` where `act` gives `none`. Where `act` errs the Go panics (an `EvalError`),
which the premise excludes. -/
abbrev ActionSpec (name : GoString) (act : State → Nat → Event → EvalM (Option State)) : Prop :=
  ∀ (p : Loc) (s : State) (n : w64) (e : Loc) (ev : Event) (o : Option State),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      stateRO p s ∗ eventRO e ev ∗
      ⌜0 ≤ sint.Z n ∧ sint.Z n < s.cfg.server.length ∧ act s (sint.nat n) ev = .ok o⌝ }}
    (App (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State.ty
      @!! name)) (Val #n)) (Val #e))
  {{ (q : Loc) (ok : Bool), RET (PairV #q #ok); succOwn q ok o }}

/-! ## Persistence -/

instance fieldRO_persistent {α β : Type} (has bit : w32) (rep : α → β → IProp GF)
    [∀ a b, Persistent (rep a b)] (g : α) (o : Option β) : Persistent (fieldRO has bit rep g o) := by
  cases o <;> unfold fieldRO <;> infer_instance

instance strsRO_persistent (sl : GoSlice) (xs : List Str) : Persistent (strsRO (GF := GF) sl xs) := by
  unfold strsRO; infer_instance

instance valueRO_persistent (v : G.Value) (w : Value) : Persistent (valueRO (GF := GF) v w) := by
  unfold valueRO; infer_instance

instance entryRO_persistent (e : G.Entry) (x : Entry) : Persistent (entryRO (GF := GF) e x) := by
  unfold entryRO; infer_instance

instance logRO_persistent (sl : GoSlice) (l : List Entry) : Persistent (logRO (GF := GF) sl l) := by
  unfold logRO; infer_instance

instance msgRO_persistent (g : G.Msg) (m : Msg) : Persistent (msgRO (GF := GF) g m) := by
  unfold msgRO; infer_instance

instance msgsRO_persistent (sl : GoSlice) (ms : List Msg) : Persistent (msgsRO (GF := GF) sl ms) := by
  unfold msgsRO; infer_instance

instance appendFactRO_persistent (g : G.AppendFact) (m : AppendFact) : Persistent (appendFactRO (GF := GF) g m) := by
  unfold appendFactRO; infer_instance

instance eventRO_persistent (p : Loc) (ev : Event) : Persistent (eventRO (GF := GF) p ev) := by
  unfold eventRO; infer_instance

instance eventsRO_persistent (sl : GoSlice) (evs : List Event) : Persistent (eventsRO (GF := GF) sl evs) := by
  unfold eventsRO; infer_instance

instance configRO_persistent (p : Loc) (cfg : Config) : Persistent (configRO (GF := GF) p cfg) := by
  unfold configRO; infer_instance

instance intsRO_persistent (sl : GoSlice) (xs : List Int) : Persistent (intsRO (GF := GF) sl xs) := by
  unfold intsRO; infer_instance

instance confRO_persistent (g : G.Conf) (c : Conf) : Persistent (confRO (GF := GF) g c) := by
  unfold confRO; infer_instance

instance confsRO_persistent (sl : GoSlice) (cs : List Conf) : Persistent (confsRO (GF := GF) sl cs) := by
  unfold confsRO; infer_instance

instance logsRO_persistent (sl : GoSlice) (ls : List (List Entry)) : Persistent (logsRO (GF := GF) sl ls) := by
  unfold logsRO; infer_instance

instance factsRO_persistent (sl : GoSlice) (fs : List Fact) : Persistent (factsRO (GF := GF) sl fs) := by
  unfold factsRO; infer_instance

instance votesRO_persistent (sl : GoSlice) (vs : List VoteRec) : Persistent (votesRO (GF := GF) sl vs) := by
  unfold votesRO; infer_instance

instance leadersRO_persistent (sl : GoSlice) (ls : List LeaderRec) : Persistent (leadersRO (GF := GF) sl ls) := by
  unfold leadersRO; infer_instance

instance confirmedsRO_persistent (sl : GoSlice) (cs : List Confirmed) : Persistent (confirmedsRO (GF := GF) sl cs) := by
  unfold confirmedsRO; infer_instance

instance termLogsRO_persistent (sl : GoSlice) (f : TermFn (List Entry)) : Persistent (termLogsRO (GF := GF) sl f) := by
  unfold termLogsRO; infer_instance

instance termConfsRO_persistent (sl : GoSlice) (f : TermFn Conf) : Persistent (termConfsRO (GF := GF) sl f) := by
  unfold termConfsRO; infer_instance

instance termIntsRO_persistent (sl : GoSlice) (f : TermFn Int) : Persistent (termIntsRO (GF := GF) sl f) := by
  unfold termIntsRO; infer_instance

instance preRO_persistent (p : Loc) (o : Option Pre) : Persistent (preRO (GF := GF) p o) := by
  cases o <;> unfold preRO <;> infer_instance

instance undoRO_persistent (sl : GoSlice) (us : List (Option Pre)) : Persistent (undoRO (GF := GF) sl us) := by
  unfold undoRO; infer_instance

instance pendingRO_persistent (sl : GoSlice) (ms : List (List Msg)) : Persistent (pendingRO (GF := GF) sl ms) := by
  unfold pendingRO; infer_instance

instance qitemRO_persistent (g : G.QItem) (q : QItem) : Persistent (qitemRO (GF := GF) g q) := by
  unfold qitemRO; infer_instance

instance qitemsRO_persistent (sl : GoSlice) (q : List QItem) : Persistent (qitemsRO (GF := GF) sl q) := by
  unfold qitemsRO; infer_instance

instance readRecsRO_persistent (sl : GoSlice) (r : List ReadRec) : Persistent (readRecsRO (GF := GF) sl r) := by
  unfold readRecsRO; infer_instance

instance queueRO_persistent (sl : GoSlice) (qs : List (List QItem)) : Persistent (queueRO (GF := GF) sl qs) := by
  unfold queueRO; infer_instance

instance readsRO_persistent (sl : GoSlice) (rs : List (List ReadRec)) : Persistent (readsRO (GF := GF) sl rs) := by
  unfold readsRO; infer_instance

instance stateFields_persistent (g : G.State) (st : State) : Persistent (stateFields (GF := GF) g st) := by
  unfold stateFields; infer_instance

instance stateRO_persistent (p : Loc) (st : State) : Persistent (stateRO (GF := GF) p st) := by
  unfold stateRO; infer_instance

instance verdictRO_persistent (r : G.Verdict) (v : Verdict) : Persistent (verdictRO (GF := GF) r v) := by
  unfold verdictRO; infer_instance

/-! ## Sub-slices -/

/-- A big separating conjunction over two lists of the same length holds over their sublists
`[lo, hi)` (a copy of tracecheck's `Etcdraft.bigSepL2_subslice`, a candidate for Perennial). -/
theorem bigSepL2_subslice {A B : Type} (Φ : A → B → IProp GF) (l1 : List A) (l2 : List B)
    (lo hi : Nat) (hlen : l1.length = l2.length) :
    ([∗list] x;y ∈ l1;l2, Φ x y) ⊢ [∗list] x;y ∈ subslice lo hi l1;subslice lo hi l2, Φ x y := by
  conv => lhs; rw [← List.take_append_drop hi l1, ← List.take_append_drop hi l2]
  refine (BigSepL2.bigSepL2_append (Or.inl (by simp [hlen]))).1.trans (sep_elim_left.trans ?_)
  unfold subslice
  conv => lhs; rw [← List.take_append_drop lo (l1.take hi), ← List.take_append_drop lo (l2.take hi)]
  exact (BigSepL2.bigSepL2_append (Or.inl (by simp [hlen]))).1.trans sep_elim_right

/-- A log's sub-slice `sl[lo:hi]` holds the log's elements `[lo, hi)`. -/
theorem logRO_subslice (sl : GoSlice) (l : List Entry) (lo hi : w64)
    (hb : 0 ≤ sint.Z lo ∧ sint.Z lo ≤ sint.Z hi ∧ sint.Z hi ≤ sint.Z sl.len) :
    logRO (GF := GF) sl l ⊢
      logRO (slice.slice sl G.Entry lo hi) (subslice (sint.nat lo) (sint.nat hi) l) := by
  unfold logRO
  iintro ⟨%es, #Hes, #Hb⟩
  ihave %Hl := BigSepL2.bigSepL2_length $$ Hb
  icases (ownSlice_slice lo hi sl _ es hb).1 $$ Hes with ⟨-, #H2, -⟩
  iexists (subslice (sint.nat lo) (sint.nat hi) es)
  isplitr
  · iexact H2
  iapply bigSepL2_subslice (fun e x => entryRO (GF := GF) e x) es l _ _ Hl
  iexact Hb

end defs

end AntCheck
end EtcdGrove
end Perennial
