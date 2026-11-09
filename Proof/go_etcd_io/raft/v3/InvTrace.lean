/-
Lean-first (no Rocq counterpart). Trace-check's Q6, increment 2 of the trace hooks' specs
(`notes/trace-validation-sim.md`, "Increment 2"; `notes/trace-validation-q6.md`): the vocabulary of
a traced cluster on raft's side, written in raft's own values (`GoString`, `w64`), naming nothing of
the TLA+ transcription.

- `TraceEv`: the abstract value of a `TracingEvent` (`state_trace.go`), field by field, its
  `Properties` map by the three keys raft writes (`cc`, `match`, `next`);
- `tracingEventRep p e`: the event at `p` and everything it points to, read-only (`↦□`: raft never
  touches an event after handing it to the logger);
- `traceAuth γt L`: the trace so far, `L`, half of a ghost variable (the other half, `traceFrag`,
  is the simulation's, which steps the TLA+ state in lockstep);
- `isTraceLogger γt tl`: the logger's contract, generic (it fires the caller's atomic update and
  names nothing of the specification): nil, or a `TraceEvent` method that, handed an event's
  representation, appends the event to the trace atomically.
-/
module

public import Proof.go_etcd_io.raft.v3.InvLogger

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

/-! ## The abstract event -/

section vocab
variable [GooseExts]

/-- A `TracingMessage`'s value. -/
structure TraceMsg where
  typ : GoString
  term : w64
  frm : GoString
  to : GoString
  entries : w64
  logTerm : w64
  index : w64
  commit : w64
  vote : GoString
  reject : Bool
  rejectHint : w64

/-- A `TracingConfChange`'s value: its changes (node, action) and its new configuration. -/
structure TraceCC where
  changes : List (GoString × GoString)
  newconf : List GoString

/-- A `TracingEvent`'s value. `cc` is its `ConfChange` field; `propCC`, `propMatch`, `propNext` its
`Properties` map at `cc`, `match`, `next` (raft writes no other key; `none` where it has none, the
map nil when all three are). -/
structure TraceEv where
  name : GoString
  nid : GoString
  term : w64
  vote : GoString
  commit : w64
  role : GoString
  logSize : w64
  conf : List GoString × List GoString
  msg : Option TraceMsg
  cc : Option TraceCC
  propCC : Option TraceCC
  propMatch : Option w64
  propNext : Option w64

instance traceMsg_countable : Pos.Countable TraceMsg :=
  countableOfLeftInverse
    (fun m : TraceMsg => (m.typ, m.term, m.frm, m.to, m.entries, m.logTerm, m.index, m.commit, m.vote,
      m.reject, m.rejectHint))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2⟩)
    (fun _ => rfl)

instance traceCC_countable : Pos.Countable TraceCC :=
  countableOfLeftInverse (fun c : TraceCC => (c.changes, c.newconf)) (fun p => ⟨p.1, p.2⟩)
    (fun _ => rfl)

instance traceEv_countable : Pos.Countable TraceEv :=
  countableOfLeftInverse
    (fun e : TraceEv => (e.name, e.nid, e.term, e.vote, e.commit, e.role, e.logSize, e.conf, e.msg,
      e.cc, e.propCC, e.propMatch, e.propNext))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2⟩)
    (fun _ => rfl)

end vocab

section trace
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-! ## The event's representation -/

/-- A `*TracingMessage` holding `o` (nil for `none`). -/
def tracingMsgRep (p : Loc) (o : Option TraceMsg) : IProp GF :=
  match o with
  | none => iprop(⌜p = null⌝)
  | some m => iprop(∃ g : TracingMessage, p ↦□ g ∗
      ⌜g.Type' = m.typ ∧ g.Term' = m.term ∧ g.From' = m.frm ∧ g.To' = m.to ∧ g.EntryLength' = m.entries ∧
        g.LogTerm' = m.logTerm ∧ g.Index' = m.index ∧ g.Commit' = m.commit ∧ g.Vote' = m.vote ∧
        g.Reject' = m.reject ∧ g.RejectHint' = m.rejectHint⌝)

/-- A `*TracingConfChange` holding `o` (nil for `none`). -/
def tracingCCRep (p : Loc) (o : Option TraceCC) : IProp GF :=
  match o with
  | none => iprop(⌜p = null⌝)
  | some c => iprop(∃ (g : TracingConfChange) (chs : List SingleConfChange), p ↦□ g ∗
      g.Changes' ↦*□ chs ∗ ⌜chs.map (fun x => (x.NodeID', x.Action')) = c.changes⌝ ∗
      g.NewConf' ↦*□ c.newconf)

/-- The `Properties` map holding the event's three properties: nil when it has none, else a map
whose `cc` holds a `*TracingConfChange`, and `match` and `next` `uint64`s, where the event has them. -/
def tracingPropsRep (m : GoMap) (e : TraceEv) : IProp GF :=
  iprop((⌜m = null⌝ ∗ ⌜e.propCC = none ∧ e.propMatch = none ∧ e.propNext = none⌝) ∨
    ∃ (pm : GMap GoString GoInterface) (pc : Loc), m ↦$□ pm ∗
      ⌜(e.propCC.isSome ↔ pm !! go!"cc" = some (interface.mkOk (go.GoType.PointerType TracingConfChange.ty) #pc)) ∧
        (e.propCC.isNone → pm !! go!"cc" = none) ∧
        (∀ w, e.propMatch = some w ↔ pm !! go!"match" = some (interface.mkOk go.uint64 #w)) ∧
        (e.propMatch = none → pm !! go!"match" = none) ∧
        (∀ w, e.propNext = some w ↔ pm !! go!"next" = some (interface.mkOk go.uint64 #w)) ∧
        (e.propNext = none → pm !! go!"next" = none) ∧
        (∀ k, k ∉ [go!"cc", go!"match", go!"next"] → pm !! k = none)⌝ ∗
      tracingCCRep pc e.propCC)

/-- The `TracingEvent` at `p` holding `e`, with everything it points to, read-only. -/
def tracingEventRep (p : Loc) (e : TraceEv) : IProp GF :=
  iprop(∃ (g : TracingEvent) (a b : GoSlice), p ↦□ g ∗
    ⌜g.Name' = e.name ∧ g.NodeID' = e.nid ∧ g.State'.Term' = e.term ∧ g.State'.Vote' = e.vote ∧
      g.State'.Commit' = e.commit ∧ g.Role' = e.role ∧ g.LogSize' = e.logSize ∧ g.Conf'.arr = [a, b]⌝ ∗
    a ↦*□ e.conf.1 ∗ b ↦*□ e.conf.2 ∗
    tracingMsgRep g.Message' e.msg ∗ tracingCCRep g.ConfChange' e.cc ∗ tracingPropsRep g.Properties' e)

instance tracingMsgRep_persistent (p : Loc) (o : Option TraceMsg) :
    Persistent (tracingMsgRep (GF := GF) p o) := by
  cases o <;> unfold tracingMsgRep <;> infer_instance

instance tracingCCRep_persistent (p : Loc) (o : Option TraceCC) :
    Persistent (tracingCCRep (GF := GF) p o) := by
  cases o <;> unfold tracingCCRep <;> infer_instance

instance tracingPropsRep_persistent (m : GoMap) (e : TraceEv) :
    Persistent (tracingPropsRep (GF := GF) m e) := by
  unfold tracingPropsRep; infer_instance

instance tracingEventRep_persistent (p : Loc) (e : TraceEv) :
    Persistent (tracingEventRep (GF := GF) p e) := by
  unfold tracingEventRep; infer_instance

/-! ## The trace -/

/-- The trace so far, the logger's half (in the harness's recorder's lock invariant). -/
def traceAuth (γt : GName) (L : List TraceEv) : IProp GF := ghostVar γt (1 : Qp).half L

/-- The trace so far, the simulation's half (in `simInv`, stepped in lockstep with the
specification's state). -/
def traceFrag (γt : GName) (L : List TraceEv) : IProp GF := ghostVar γt (1 : Qp).half L

/-- A fresh trace, empty, both halves. -/
theorem trace_alloc : ⊢ |==> ∃ γt, traceAuth (GF := GF) γt [] ∗ traceFrag γt [] := by
  iintro
  imod ghostVar_alloc (GF := GF) ([] : List TraceEv) with ⟨%γt, H⟩
  iexists γt
  unfold traceAuth traceFrag
  icases ghostVar_split_half (GF := GF) γt 1 ([] : List TraceEv) $$ H with ⟨H1, H2⟩
  iframe

/-- The two halves agree. -/
theorem trace_agree (γt : GName) (L1 L2 : List TraceEv) :
    traceAuth (GF := GF) γt L1 -∗ traceFrag γt L2 -∗ ⌜L1 = L2⌝ := by
  unfold traceAuth traceFrag
  iintro H1 H2
  iapply ghostVar_agree (GF := GF) γt L1 (1 : Qp).half L2 (1 : Qp).half $$ H1 H2

/-- Both halves together append an event. -/
theorem trace_append (γt : GName) (L : List TraceEv) (e : TraceEv) :
    traceAuth (GF := GF) γt L -∗ traceFrag γt L ==∗ traceAuth γt (L ++ [e]) ∗ traceFrag γt (L ++ [e]) := by
  unfold traceAuth traceFrag
  iintro H1 H2
  iapply ghostVar_update_halves (GF := GF) (L ++ [e]) γt L L $$ H1 H2

/-! ## The logger's contract -/

/-- The trace logger's contract (increment 2; replaces increment 1's `TraceLoggerOk`, nil only):
nil, or a logger whose `TraceEvent`, handed the representation of an event `e`, performs the
caller's atomic update appending `e` to the trace (its linearization point, under the recorder's
lock), and returns (`#()`: until 2026-11-09, Q8 stage 1 slice 2, any value, a panic's included,
which left the traced `traceEvent`'s continuation unprovable). Generic: it names nothing of the TLA+
specification. -/
def isTraceLogger (γt : GName) (tl : GoInterface) : IProp GF :=
  iprop(⌜tl = interface.nil⌝ ∨
    ∃ l : GoInterfaceOk, ⌜tl = GoInterface.ok l⌝ ∗
      □ ∀ (p : Loc) (e : TraceEv) (Q : IProp GF), tracingEventRep p e -∗
        (AU <{ ∃∃ L, traceAuth γt L }> @ ⊤, ∅ <{ traceAuth γt (L ++ [e]), COMM Q }>) -∗
        WP (App (Val #(methods l.ty go!"TraceEvent" l.v)) (Val #p)) {{ fun v => iprop(⌜v = #()⌝ ∗ Q) }})

instance isTraceLogger_persistent (γt : GName) (tl : GoInterface) :
    Persistent (isTraceLogger (GF := GF) γt tl) := by
  unfold isTraceLogger; infer_instance

/-- A nil logger meets the contract, for any trace. -/
theorem isTraceLogger_nil (γt : GName) : ⊢ isTraceLogger (GF := GF) γt interface.nil := by
  unfold isTraceLogger
  ileft
  ipureintro; rfl

end trace

end EtcdGrove
end Perennial
