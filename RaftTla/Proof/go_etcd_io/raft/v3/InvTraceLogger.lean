/-
Lean-first (no Rocq counterpart). **The trace logger's contract, in raft's `with_tla` build**
(`state_trace.go`; until the two builds were separated, part of `InvTrace.lean`).

- `tracingEventRep p e`: the `TracingEvent` at `p` and everything it points to, read-only (`↦□`:
  raft never touches an event after handing it to the logger);
- `isTraceLogger γt tl`: the logger's contract, generic (it fires the caller's atomic update and
  names nothing of the specification): nil, or a `TraceEvent` method that, handed an event's
  representation, appends the event to the trace atomically.

The main tree's module of the same name states the contract for the build without the tag, where
`TraceLogger` is `interface{}` and the hooks are empty: nil only.
-/
module

public import RaftTla.Proof.go_etcd_io.raft.v3.InvTrace

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

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

/-! ## The logger's contract -/

/-- The trace logger's contract (increment 2; replaces increment 1's `TraceLoggerOk`, nil only):
nil, or a logger whose `TraceEvent`, handed the representation of an event `e`, performs the
caller's atomic update appending `e` to the trace (its linearization point, under the recorder's
lock), and returns (`#()`: until 2026-11-09, Q8 stage 1 slice 2, any value, a panic's included,
which left the traced `traceEvent`'s continuation unprovable). Generic: it names nothing of the TLA+
specification. (2026-11-21, the crash invariant: `notes/raft-crash-law-design.md` (f)) The update
lends the generation's `notCrashed` at its commit (and gets it back): the logger commits at one of
its own steps, where the token is at hand (`wp_ncfupd`), and the caller's commit (`FxPresU`) runs a
ghost step of raft's that needs it. -/
def isTraceLogger (γt : GName) (tl : GoInterface) : IProp GF :=
  iprop(⌜tl = interface.nil⌝ ∨
    ∃ l : GoInterfaceOk, ⌜tl = GoInterface.ok l⌝ ∗
      □ ∀ (p : Loc) (e : TraceEv) (Q : IProp GF), tracingEventRep p e -∗
        (AU <{ ∃∃ L, traceAuth γt L }> @ ⊤, ∅ <{ traceAuth γt (L ++ [e]) ∗ notCrashed, COMM notCrashed ∗ Q }>) -∗
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
