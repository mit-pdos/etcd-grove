/-
Lean-first (no Rocq counterpart).

# The Go checker's values, related to the Lean transcription (Draft, 2026-11-08)

Layer C of `notes/trace-validation-plan.md`: the checker's spec (`NewTrace`, `CheckTrace`,
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/tracecheck/etcdraft/`) relates the Go
transcription's values (package `etcdraft`, translated by Goose) to the Lean transcription's
(`Tla/`). Everything the specs relate is read-only once built (a `Trace` and its initial `State`
are never written: the search clones a state before it changes it), so every predicate here is
persistent (`↦□`, `↦*□`, `↦$□`).

Each relation is canonical where the Go compares by value, so that the Go's equality agrees with
the Lean's `=`: a value that is not a configuration record has empty `NewConf`/`Learners`, one
that is not a client value has `Val` 0.

Numbers: the Lean's are `Int`, the Go's 64-bit `int`; a relation reads the Go number signed
(`sint.Z`), and the specs' premises (`Event.Bounded`) keep the trace's numbers far from overflow.
-/
module

public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Tla.Check
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Base

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI

section types
variable [GooseExts]

/-- The Go package's types, by their short names. -/
abbrev G.Event := github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Event
abbrev G.EventState := github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.EventState
abbrev G.EventMsg := github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.EventMsg
abbrev G.EventProps := github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.EventProps
abbrev G.EventConfChange :=
  github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.EventConfChange
abbrev G.EventChange := github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.EventChange
abbrev G.Value := github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Value
abbrev G.Entry := github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Entry
abbrev G.Msg := github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Msg
abbrev G.Bag := github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag
abbrev G.bagItem := github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.bagItem
abbrev G.Config := github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Config
abbrev G.Durable := github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Durable
abbrev G.Server := github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Server
abbrev G.State := github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State
abbrev G.line := github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.line
abbrev G.Trace := github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace
abbrev G.Result := github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Result

end types

/-! ## Bounds -/

/-- The bound on the trace's numbers and length: far from the Go `int`'s overflow (`len(log)+1`,
`b + ev.Entries`), and small enough that the Go's `make([]Entry, n)` of a bootstrap log of `n`
entries is a real allocation (as the porcupine example's `ClientIdsOk`, gc's `maxAlloc`; review
round 1 of layer C, S2). -/
def numBound : Int := 2 ^ 40

/-- A number of the trace within `numBound`. -/
def numOk (n : Int) : Prop := 0 ≤ n ∧ n < numBound

/-- An event whose numbers are `numOk` (layer B gives it of raft's: its terms and indices are
bounded by the time receipts, `notes/trace-validation-sim.md`, "Increment 2"). -/
def Event.Bounded (e : Event) : Prop :=
  numOk e.state.term ∧ numOk e.state.commit ∧ numOk e.log ∧
  ∀ m, e.msg = some m →
    numOk m.term ∧ numOk m.entries ∧ numOk m.logTerm ∧ numOk m.index ∧ numOk m.commit ∧
    numOk m.rejectHint

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

/-! ## Sets, values, entries, messages -/

/-- A Go `Set` (a slice of ids, sorted, no duplicates) holding `s`. -/
def setRO (sl : GoSlice) (s : SetIds) : IProp GF :=
  iprop(∃ xs : List w64, sl ↦*□ xs ∗ ⌜xs.map (fun x => uint.nat x) = s⌝)

/-- A Go `Value` holding `w`, canonically. -/
def valueRO (v : G.Value) (w : Value) : IProp GF :=
  match w with
  | .val n => iprop(⌜v.Kind' = W8 0 ∧ sint.Z v.Val' = n⌝ ∗ setRO v.NewConf' [] ∗ setRO v.Learners' [])
  | .emptySeq => iprop(⌜v.Kind' = W8 1 ∧ v.Val' = W64 0⌝ ∗ setRO v.NewConf' [] ∗ setRO v.Learners' [])
  | .conf nc ln => iprop(⌜v.Kind' = W8 2 ∧ v.Val' = W64 0⌝ ∗ setRO v.NewConf' nc ∗ setRO v.Learners' ln)

/-- A Go `Entry` holding `x`. -/
def entryRO (e : G.Entry) (x : Entry) : IProp GF :=
  iprop(⌜sint.Z e.Term' = x.term ∧ e.Type' = (match x.type with | .value => W8 0 | .config => W8 1)⌝ ∗
    valueRO e.Value' x.value)

/-- A Go `[]Entry` holding `l`. -/
def logRO (sl : GoSlice) (l : List Entry) : IProp GF :=
  iprop(∃ es : List G.Entry, sl ↦*□ es ∗ [∗list] e;x ∈ es;l, entryRO e x)

/-- The Go `MsgType` of a message type. -/
def msgTypeW (t : MsgType) : w8 :=
  match t with
  | .requestVoteRequest => W8 0 | .requestVoteResponse => W8 1
  | .appendEntriesRequest => W8 2 | .appendEntriesResponse => W8 3

/-- A Go `*Msg` holding `m`. -/
def msgRO (p : Loc) (m : Msg) : IProp GF :=
  iprop(∃ v : G.Msg, p ↦□ v ∗
    ⌜v.Type' = msgTypeW m.type ∧ v.Subtype' = stringToGoString m.subtype ∧ sint.Z v.Term' = m.term ∧
      sint.Z v.LastLogTerm' = m.lastLogTerm ∧ sint.Z v.LastLogIndex' = m.lastLogIndex ∧
      v.VoteGranted' = m.voteGranted ∧ sint.Z v.PrevLogIndex' = m.prevLogIndex ∧
      sint.Z v.PrevLogTerm' = m.prevLogTerm ∧ sint.Z v.CommitIndex' = m.commitIndex ∧
      v.Success' = m.success ∧ sint.Z v.MatchIndex' = m.matchIndex ∧
      uint.nat v.Source' = m.source ∧ uint.nat v.Dest' = m.dest⌝ ∗
    logRO v.Entries' m.entries)

/-- A Go `Bag` holding `b`, item by item. -/
def bagRO (g : G.Bag) (b : Bag) : IProp GF :=
  iprop(∃ items : List G.bagItem, g.items' ↦*□ items ∗
    [∗list] it;p ∈ items;b, msgRO it.msg' p.1 ∗ ⌜sint.Z it.count' = (p.2 : Int)⌝)

/-! ## States -/

/-- A Go `Config` holding `c`. -/
def configRO (g : G.Config) (c : Config) : IProp GF :=
  iprop(∃ a b : GoSlice, ⌜g.Joint'.arr = [a, b]⌝ ∗ setRO a c.incoming ∗ setRO b c.outgoing ∗
    setRO g.Learners' c.learners)

/-- A Go `Durable` holding `d`. -/
def durableRO (g : G.Durable) (d : Durable) : IProp GF :=
  iprop(⌜sint.Z g.CurrentTerm' = d.currentTerm ∧ uint.nat g.VotedFor' = d.votedFor ∧
      sint.Z g.Log' = d.log ∧ sint.Z g.CommitIndex' = d.commitIndex⌝ ∗ configRO g.Config' d.config)

/-- A Go `*Server` holding `v`, its `matchIndex` at every id (a missing key is 0: both sides read
the members of a configuration, which may name a node that never logs; review round 1 of layer C,
S3). -/
def serverRO (p : Loc) (v : Server) : IProp GF :=
  iprop(∃ (g : G.Server) (mm : GMap w64 w64), p ↦□ g ∗
    ⌜sint.Z g.CurrentTerm' = v.currentTerm ∧ g.State' = stringToGoString v.state ∧
      uint.nat g.VotedFor' = v.votedFor ∧ sint.Z g.CommitIndex' = v.commitIndex ∧
      sint.Z g.PendingConfChangeIndex' = v.pendingConfChangeIndex⌝ ∗
    logRO g.Log' v.log ∗ setRO g.VotesResponded' v.votesResponded ∗
    setRO g.VotesGranted' v.votesGranted ∗
    g.MatchIndex' ↦$□ mm ∗
    ⌜∀ j : w64, sint.Z ((mm !! j).getD (W64 0)) = v.matchIndex (uint.nat j)⌝ ∗
    configRO g.Config' v.config ∗ durableRO g.Durable' v.durable)

/-- A Go `*State` holding `st`. -/
def stateRO (p : Loc) (st : State) : IProp GF :=
  iprop(∃ (g : G.State) (sm : GMap w64 Loc), p ↦□ g ∗ setRO g.Server' st.server ∗
    g.S' ↦$□ sm ∗
    ([∗list] i ∈ st.server, ∃ q : Loc, ⌜sm !! (W64 (Int.ofNat i)) = some q⌝ ∗ serverRO q (st.s i)) ∗
    bagRO g.Messages' st.messages ∗ bagRO g.PendingMessages' st.pendingMessages ∗
    ⌜sint.Z g.ReconfigCount' = st.reconfigCount⌝)

/-! ## Events and traces -/

/-- A Go `EventChange` holding `c`. -/
def changeRel (g : G.EventChange) (c : EventChange) : Prop :=
  g.NID' = stringToGoString c.nid ∧ g.Action' = stringToGoString c.action

/-- A Go `*[]T` holding `o`: nil for `none`. -/
def optSliceRO {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {A : Type} (p : Loc)
    (o : Option (List A)) (rel : V → A → Prop) : IProp GF :=
  match o with
  | none => iprop(⌜p = null⌝)
  | some xs => iprop(∃ (sl : GoSlice) (vs : List V), p ↦□ sl ∗ sl ↦*□ vs ∗ ⌜List.Forall₂ rel vs xs⌝)

/-- A Go `*EventConfChange` holding `cc`. -/
def confChangeRO (p : Loc) (cc : EventConfChange) : IProp GF :=
  iprop(∃ g : G.EventConfChange, p ↦□ g ∗
    optSliceRO (V := G.EventChange) g.Changes' cc.changes changeRel ∗
    optSliceRO (V := GoString) g.NewConf' cc.newconf (fun s t => s = stringToGoString t))

/-- A Go `*EventProps` holding `o`: nil for `none`. -/
def propsRO (p : Loc) (o : Option EventProps) : IProp GF :=
  match o with
  | none => iprop(⌜p = null⌝)
  | some pr => iprop(∃ g : G.EventProps, p ↦□ g ∗
      match pr.cc with
      | none => iprop(⌜g.CC' = null⌝)
      | some cc => confChangeRO g.CC' cc)

/-- A Go `EventMsg` holding `m`. -/
def eventMsgRel (g : G.EventMsg) (m : EventMsg) : Prop :=
  g.Type' = stringToGoString m.type ∧ sint.Z g.Term' = m.term ∧
  g.From' = stringToGoString m.«from» ∧ g.To' = stringToGoString m.to ∧
  sint.Z g.Entries' = m.entries ∧ sint.Z g.LogTerm' = m.logTerm ∧ sint.Z g.Index' = m.index ∧
  sint.Z g.Commit' = m.commit ∧ g.Vote' = stringToGoString m.vote ∧ g.Reject' = m.reject ∧
  sint.Z g.RejectHint' = m.rejectHint

/-- A Go `Event` value holding `e` (its pointers' targets read-only). -/
def eventRO (g : G.Event) (e : Event) : IProp GF :=
  iprop(⌜g.Name' = stringToGoString e.name ∧ g.NID' = stringToGoString e.nid ∧
      sint.Z g.State'.Term' = e.state.term ∧ g.State'.Vote' = stringToGoString e.state.vote ∧
      sint.Z g.State'.Commit' = e.state.commit ∧ g.Role' = stringToGoString e.role ∧
      sint.Z g.Log' = e.log⌝ ∗
    (∃ a b : GoSlice, ⌜g.Conf'.arr = [a, b]⌝ ∗
      (∃ xs : List GoString, a ↦*□ xs ∗ ⌜xs = e.conf.1.map stringToGoString⌝) ∗
      (∃ ys : List GoString, b ↦*□ ys ∗ ⌜ys = e.conf.2.map stringToGoString⌝)) ∗
    (match e.msg with
     | none => iprop(⌜g.Msg' = null⌝)
     | some m => iprop(∃ gm : G.EventMsg, g.Msg' ↦□ gm ∗ ⌜eventMsgRel gm m⌝)) ∗
    propsRO g.Prop' e.prop)

/-- A Go `[]Event` holding `evs`, read-only: what `NewTrace` reads (and keeps pointers into). Its
strings are the UTF-8 encodings of the Lean's (`stringToGoString`): raft's events are ASCII. -/
def eventsRO (sl : GoSlice) (evs : List Event) : IProp GF :=
  iprop(∃ gs : List G.Event, sl ↦*□ gs ∗ [∗list] g;e ∈ gs;evs, eventRO g e)

/-- A Go `line` holding `x`. -/
def lineRO (g : G.line) (x : Line) : IProp GF :=
  iprop((∃ ge : G.Event, g.ev' ↦□ ge ∗ eventRO ge x.ev) ∗
    ⌜uint.nat g.nid' = x.nid ∧ uint.nat g.vote' = x.vote ∧ g.role' = stringToGoString x.role ∧
      uint.nat g.from' = x.«from» ∧ uint.nat g.to' = x.to⌝ ∗
    (∃ a b : GoSlice, ⌜g.conf'.arr = [a, b]⌝ ∗ setRO a x.conf.1 ∗ setRO b x.conf.2))

/-- `tr` is a trace `NewTrace` builds: `newTrace`'s of bounded events (what the Go's search relies
on: every server's state in the initial state, `bootstrap` as long as the lines; review round 1 of
layer C, F1). -/
def Trace.Valid (tr : Trace) : Prop :=
  ∃ evs : List Event, (∀ e ∈ evs, e.Bounded) ∧ (evs.length : Int) < numBound ∧ newTrace evs = .ok tr

/-- A Go `*Trace` holding `tr`, read-only: what `NewTrace` returns and `CheckTrace` reads; it
carries `Trace.Valid tr`, which only `NewTrace` produces. -/
def traceRO (t : Loc) (tr : Trace) : IProp GF :=
  iprop(⌜Trace.Valid tr⌝ ∗ ∃ g : G.Trace, t ↦□ g ∗
    (∃ lns : List G.line, g.lines' ↦*□ lns ∗ [∗list] ln;x ∈ lns;tr.lines, lineRO ln x) ∗
    setRO g.Server' tr.server ∗ setRO g.InitSrv' tr.initSrv ∗ g.bootstrap' ↦*□ tr.bootstrap ∗
    stateRO g.init' tr.init)

/-- A Go `Result` holding what the Lean `Result` records (its debugging fields, `Bad`, `Eval`'s
numbers, `MaxStates`, `Before`, unconstrained). -/
def resultRel (g : G.Result) (r : Result) : Prop :=
  g.OK' = r.ok ∧ uint.nat g.Branched' = r.branched ∧ uint.nat g.Line' = r.line ∧
  g.Violation' = stringToGoString (r.violation.getD "") ∧ uint.nat g.ViolLine' = r.violLine ∧
  g.EvalError' = stringToGoString ((r.evalError.map EvalError.what).getD "") ∧
  uint.nat g.ErrLine' = r.errLine

/-! ## Laws -/

/-- Every predicate here is persistent (a trace and its initial state are never written). -/
instance optSliceRO_persistent {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {A : Type}
    (p : Loc) (o : Option (List A)) (rel : V → A → Prop) :
    Persistent (optSliceRO (GF := GF) (V := V) p o rel) := by
  cases o <;> unfold optSliceRO <;> infer_instance

instance setRO_persistent (sl : GoSlice) (s : SetIds) : Persistent (setRO (GF := GF) sl s) := by
  unfold setRO; infer_instance

instance valueRO_persistent (v : G.Value) (w : Value) : Persistent (valueRO (GF := GF) v w) := by
  cases w <;> unfold valueRO <;> infer_instance

instance entryRO_persistent (e : G.Entry) (x : Entry) : Persistent (entryRO (GF := GF) e x) := by
  unfold entryRO; infer_instance

instance logRO_persistent (sl : GoSlice) (l : List Entry) : Persistent (logRO (GF := GF) sl l) := by
  unfold logRO; infer_instance

instance msgRO_persistent (p : Loc) (m : Msg) : Persistent (msgRO (GF := GF) p m) := by
  unfold msgRO; infer_instance

instance bagRO_persistent (g : G.Bag) (b : Bag) : Persistent (bagRO (GF := GF) g b) := by
  unfold bagRO; infer_instance

instance configRO_persistent (g : G.Config) (c : Config) : Persistent (configRO (GF := GF) g c) := by
  unfold configRO; infer_instance

instance durableRO_persistent (g : G.Durable) (d : Durable) : Persistent (durableRO (GF := GF) g d) := by
  unfold durableRO; infer_instance

instance serverRO_persistent (p : Loc) (v : Server) : Persistent (serverRO (GF := GF) p v) := by
  unfold serverRO; infer_instance

instance stateRO_persistent (p : Loc) (st : State) : Persistent (stateRO (GF := GF) p st) := by
  unfold stateRO; infer_instance

instance confChangeRO_persistent (p : Loc) (cc : EventConfChange) : Persistent (confChangeRO (GF := GF) p cc) := by
  unfold confChangeRO; infer_instance

instance propsRO_persistent (p : Loc) (o : Option EventProps) : Persistent (propsRO (GF := GF) p o) := by
  rcases o with _ | ⟨⟨_ | cc⟩⟩ <;> simp only [propsRO] <;> infer_instance

instance eventRO_persistent (g : G.Event) (e : Event) : Persistent (eventRO (GF := GF) g e) := by
  cases hm : e.msg <;> simp only [eventRO, hm] <;> infer_instance

instance eventsRO_persistent (sl : GoSlice) (evs : List Event) : Persistent (eventsRO (GF := GF) sl evs) := by
  unfold eventsRO; infer_instance

instance lineRO_persistent (g : G.line) (x : Line) : Persistent (lineRO (GF := GF) g x) := by
  unfold lineRO; infer_instance

instance traceRO_persistent (t : Loc) (tr : Trace) : Persistent (traceRO (GF := GF) t tr) := by
  unfold traceRO; infer_instance

end defs

end Etcdraft
end EtcdGrove
end Perennial
