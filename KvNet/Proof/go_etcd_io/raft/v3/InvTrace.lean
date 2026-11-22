-- The copy for the part `KvNet/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/InvTrace.lean` (etc/copy-part.py; rerun it, do not edit).
/-
Lean-first (no Rocq counterpart). Trace-check's Q6, increment 2 of the trace hooks' specs
(`notes/trace-validation-sim.md`, "Increment 2"; `notes/trace-validation-q6.md`): the vocabulary of
a traced cluster on raft's side, written in raft's own values (`GoString`, `w64`), naming nothing of
the TLA+ transcription.

- `TraceEv`: the abstract value of a `TracingEvent` (`state_trace.go`), field by field, its
  `Properties` map by the three keys raft writes (`cc`, `match`, `next`);
- `traceAuth γt L`: the trace so far, `L`, half of a ghost variable (the other half, `traceFrag`,
  is the simulation's, which steps the TLA+ state in lockstep);

The logger's contract `isTraceLogger γt tl` depends on raft's build and is in `InvTraceLogger.lean`
(this tree's: the build without `with_tla`; `RaftTla/`'s: the build with it, with the event's
representation `tracingEventRep`).
-/
module

public import KvNet.Proof.go_etcd_io.raft.v3.InvLogger

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

end trace

end EtcdGrove
end Perennial
