/-
Lean-first (no Rocq counterpart).

# The harness's trace recorder (2026-11-09)

Trace-check's layer D (`notes/trace-validation-plan.md`): the closed program's `SyncRecorder`
(`examples/raft/tracecheck/concurrent.go`) is the trace logger every replica of the concurrent
cluster reports to. Raft's side of the contract is `isTraceLogger γt` (`InvTrace.lean`): its
`TraceEvent`, handed an event's representation, fires the caller's atomic update appending the event
to the trace. This file is the recorder's side:

- `tracingEventVal g e`: a `TracingEvent` *value* `g` holding `e` (what `tracingEventRep` says of
  the struct its pointer points to): the recorder copies `*ev` into its slice, so it keeps values,
  whose pointers' targets are read-only;
- `traceEventsRep sl L`: a `[]TracingEvent` holding the trace `L`, read-only (what `Events`
  returns and `ConvertEvents` reads);
- `isSyncRecorder γt r`: the recorder at `r`, its mutex guarding the recorded slice, which holds
  the trace, the logger's half of the trace, `traceAuth γt L` (the simulation holds the other,
  `traceFrag γt L`), and one time receipt per event (`⧗ L.length`, taken by `TraceEvent` at a step
  of its own: S7 (part 1), 2026-11-11), which bounds the event count by the adequacy theorem's
  step bound (`Events`' post, `L.length < receiptBound GF`);
- the ghost steps: `traceAuth_commit` (the linearization point of `TraceEvent`: the caller's
  update fired against the lock's half), `syncRecorder_alloc` (a fresh recorder and a fresh trace).

`isTraceLogger`'s atomic update is over `traceAuth`, the same ghost half as `traceFrag` (both are
`ghostVar γt ½`): the client's half, which the simulation names `traceFrag`, is what the update
hands over; the lock holds the other half (named `traceAuth`, as `InvTrace.lean` documents).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Base
public import Proof.go_etcd_io.raft.v3.InvTrace

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace TraceCheck

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section types
variable [GooseExts]

/-- The harness's types, by their short names. -/
abbrev G.SyncRecorder := github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.SyncRecorder

end types

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Assumptions]

/-- A `TracingEvent` value holding `e`, its pointers' targets read-only: `tracingEventRep`'s
statement about the struct its pointer points to. -/
def tracingEventVal (g : TracingEvent) (e : TraceEv) : IProp GF :=
  iprop(∃ (a b : GoSlice),
    ⌜g.Name' = e.name ∧ g.NodeID' = e.nid ∧ g.State'.Term' = e.term ∧ g.State'.Vote' = e.vote ∧
      g.State'.Commit' = e.commit ∧ g.Role' = e.role ∧ g.LogSize' = e.logSize ∧ g.Conf'.arr = [a, b]⌝ ∗
    a ↦*□ e.conf.1 ∗ b ↦*□ e.conf.2 ∗
    tracingMsgRep g.Message' e.msg ∗ tracingCCRep g.ConfChange' e.cc ∗ tracingPropsRep g.Properties' e)

instance tracingEventVal_persistent (g : TracingEvent) (e : TraceEv) :
    Persistent (tracingEventVal (GF := GF) g e) := by
  unfold tracingEventVal; infer_instance

/-- An event's representation is a read-only pointer to a value holding it. -/
theorem tracingEventRep_val (p : Loc) (e : TraceEv) :
    tracingEventRep (GF := GF) p e ⊢ ∃ g, p ↦□ g ∗ tracingEventVal g e := by
  unfold tracingEventRep tracingEventVal
  iintro ⟨%g, %a, %b, #Hp, %Hf, #Ha, #Hb, #Hm, #Hc, #Hpr⟩
  iexists g
  iframe Hp
  iexists a, b
  isplitr
  · ipureintro; exact Hf
  isplitr; · iexact Ha
  isplitr; · iexact Hb
  isplitr; · iexact Hm
  isplitr; · iexact Hc
  iexact Hpr

/-- A `[]TracingEvent` holding the trace `L`, read-only. -/
def traceEventsRep (sl : GoSlice) (L : List TraceEv) : IProp GF :=
  iprop(∃ gs : List TracingEvent, sl ↦*□ gs ∗ [∗list] g;e ∈ gs;L, tracingEventVal g e)

instance traceEventsRep_persistent (sl : GoSlice) (L : List TraceEv) :
    Persistent (traceEventsRep (GF := GF) sl L) := by
  unfold traceEventsRep; infer_instance

/-- The recorder's lock invariant: its slice (and its capacity) holding the trace `L`, the
logger's half of the trace, and a time receipt per event (the event count's bound, S7 (part 1)). -/
def recLockInv (γt : GName) (r : Loc) : IProp GF :=
  iprop(∃ (sl : GoSlice) (L : List TraceEv),
    r.[github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.SyncRecorder, go!"events"] ↦ sl ∗
    traceEventsRep sl L ∗ ownSliceCap TracingEvent sl (DFrac.own 1) ∗ traceAuth γt L ∗ ⧗ L.length)

/-- The recorder at `r`, logging the trace `γt`. -/
def isSyncRecorder (γt : GName) (r : Loc) : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck ∗
    sync.isMutex (r.[github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.SyncRecorder, go!"mu"])
      (recLockInv γt r))

instance isSyncRecorder_persistent (γt : GName) (r : Loc) :
    Persistent (isSyncRecorder (GF := GF) γt r) := by
  unfold isSyncRecorder; infer_instance

/-! ## Ghost steps -/

/-- `n` time receipts bound `n`, kept. -/
theorem receipt_lt_keep (n : Nat) : ⧗ n ⊢@{IProp GF} ⌜n < receiptBound GF⌝ ∗ ⧗ n :=
  (persistent_entails_left (receipt_lt n)).trans sep_comm.1

/-- **The linearization point of `TraceEvent`**: the caller's atomic update fired against the
lock's half of the trace, both halves appended `e`. -/
theorem traceAuth_commit (γt : GName) (L : List TraceEv) (e : TraceEv) (Q : IProp GF) :
    traceAuth (GF := GF) γt L -∗
      (AU <{ ∃∃ L', traceAuth (GF := GF) γt L' }> @ ⊤, ∅ <{ traceAuth γt (L' ++ [e]), COMM Q }>) ={⊤}=∗
      traceAuth γt (L ++ [e]) ∗ Q := by
  iintro Hl Hau
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil, tforall_nil, Std.Tele.app, ULift.down] at Hacc
  icases Hacc with ⟨%L', Hc, Hclose⟩
  unfold traceAuth
  ihave %Heq := ghostVar_agree (GF := GF) γt L (1 : Qp).half L' (1 : Qp).half $$ Hl Hc
  subst Heq
  imod ghostVar_update_halves (GF := GF) (L ++ [e]) γt L L $$ Hl Hc with ⟨Hl, Hc⟩
  icases Hclose with ⟨-, Hcom⟩
  imod Hcom $$ Hc with HQ
  imodintro
  iframe

/-- The lock's half and the client's agree. -/
theorem traceAuth_frag_agree (γt : GName) (L1 L2 : List TraceEv) :
    traceAuth (GF := GF) γt L1 -∗ traceFrag γt L2 -∗ ⌜L1 = L2⌝ :=
  trace_agree γt L1 L2

/-- **A fresh recorder** (`&SyncRecorder{}`, as `RunConcurrent` builds it) and a fresh trace:
the recorder logging it, and the simulation's half, empty. -/
theorem syncRecorder_alloc (r : Loc) (E : CoPset) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck -∗
      r ↦ (zero_val G.SyncRecorder) ={E}=∗ ∃ γt, isSyncRecorder γt r ∗ traceFrag γt [] := by
  iintro #Hinit Hr
  iStructNamed Hr
  imod trace_alloc (GF := GF) with ⟨%γt, Ha, Hf⟩
  imod receipt_zero (GF := GF) with Hr0
  ihave Hsl := ownSlice_nil (V := TracingEvent) (GF := GF) DFrac.discard
  ihave Hcap := ownSliceCap_nil (V := TracingEvent) (GF := GF)
  imod sync.init_Mutex (recLockInv (GF := GF) γt r) E _ $$ mu [events Ha Hsl Hcap Hr0] with #Hm
  · inext
    unfold recLockInv traceEventsRep
    iexists slice.nil, []
    iframe
    isplitl []
    · iexists []
      isplitr
      · iexact Hsl
      iapply (BigSepL2.bigSepL2_nil (PROP := IProp GF)).mpr; iempintro
    iexact Hcap
  imodintro
  iexists γt
  iframe Hf
  unfold isSyncRecorder
  iframe Hinit Hm

end defs

end TraceCheck
end EtcdGrove
end Perennial
