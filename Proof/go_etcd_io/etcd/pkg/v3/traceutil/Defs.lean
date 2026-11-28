/-
The traces of `pkg/v3/traceutil` (unit P1b, 2026-10-14; `notes/decisions.md`, "Traces on the
request path"). Lean-first (no Rocq counterpart).

* `ownTrace t e`: the trace `t`, owned exclusively (a `*Trace`'s fields, its fields slice and its
  steps slice, each step's own fields slice, with their capacities): every method of `*Trace`
  reads or writes `t`'s fields, so two goroutines may not both use one trace. A request's trace
  is owned by the goroutine serving the request; the apply thread's (`txn.Put`'s, ...) is handed
  to the request goroutine with the apply result.
* `ownFields sl`: a slice of `Field`s owned with its capacity (what `Step`, `StartSubTrace`, ...,
  `newTrace` keep in the trace), its values formattable by Perennial's `fmt` model
  (`fieldsWf`: `nil` or of a predeclared basic type; the trace's logger formats them with `%v`).
* `ctxTraceIs ctx o` (persistent): what `ctx.Value(TraceKey{})` returns: the trace `t`
  (`o = some t`, not nil) or no trace (`o = none`: anything but a non-nil `*Trace`). The context
  describes its trace's value only; its owner holds `ownTrace t e` separately. No trace: `nil`, a
  value of another type, or a nil `*Trace`.
-/
module

public import GeneratedProof.go_etcd_io.etcd.pkg.v3.traceutil
public import Perennial.Proof.fmt
public import Proof.fmt.SprintfPure
public import Spec.go_uber_org.zap.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode _root_.Perennial.go_etcd_io.etcd.pkg.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.traceutil.Assumptions]

/-- The fields' values are `nil`, `bool`s, `string`s or of a predeclared integer type
(`fmt.PureArgsWf`), as the trace's logger formats them with `%v` (the real `fmt.Sprintf`'s
verified subset; until 2026-11-24 `fmt.ArgsWf`, the trusted model's premise, which also admitted
floats and method-less named types: `notes/specs-only/ledger.md`). -/
def traceutil.fieldsWf [GoLocalContext] [GoSemanticsFunctions] (fs : List traceutil.Field) : Prop :=
  fmt.PureArgsWf (fs.map traceutil.Field.Value')

/-- A slice of fields, owned with its capacity, its values formattable. -/
def traceutil.ownFields (sl : GoSlice) : IProp GF :=
  iprop(∃ fs : List traceutil.Field, sl ↦* fs ∗ ownSliceCap traceutil.Field sl (DFrac.own 1) ∗
    ⌜traceutil.fieldsWf fs⌝)

/-- **The trace `t`, owned** (see the file header), empty (`TODO()`'s) or not as `e` says (its
`isEmpty` field, written only at its creation: what `IsEmpty` reads; `EnsureTrace` keeps a
context's trace that is not empty). Its logger is nil (`TODO()`'s) or a zap logger
(`zapLoggerOrNil`; premise fixes 6: `LogWithStepThreshold` logs through it when not nil). -/
def traceutil.ownTrace (t : Loc) (e : Bool) : IProp GF :=
  iprop(∃ (v : traceutil.Trace) (ss : List traceutil.step),
    t ↦ v ∗ traceutil.ownFields v.fields' ∗
    v.steps' ↦* ss ∗ ownSliceCap traceutil.step v.steps' (DFrac.own 1) ∗
    ([∗list] st ∈ ss, traceutil.ownFields st.fields') ∗ ⌜v.isEmpty' = e⌝ ∗ zapLoggerOrNil v.lg')

/-- The trace's ownership (at emptiness `e`), if the context carries one. -/
def traceutil.ownTraceOpt : Option Loc → Bool → IProp GF
  | some t, e => traceutil.ownTrace t e
  | none, _ => iprop(True)

/-- What a context's `Value(TraceKey{})` may return, for its trace `o`. -/
def traceutil.traceValIs (v : GoInterface) : Option Loc → Prop
  | some t => t ≠ null ∧
      v = interface.mkOk (go.GoType.PointerType traceutil.Trace.ty) #t
  | none => v = GoInterface.nil ∨ ∃ ii : GoInterfaceOk, v = GoInterface.ok ii ∧
      (ii.ty ≠ go.GoType.PointerType traceutil.Trace.ty ∨ ii.v = #(null : Loc))

/-- The key `TraceKey{}`, as an `any`. -/
abbrev traceutil.traceKeyVal : GoInterface :=
  interface.mkOk traceutil.TraceKey.ty #(zero_val traceutil.TraceKey)

/-- **The context `ctx` carries the trace `o`** (persistent): its `Value(TraceKey{})`, from any
goroutine, returns it (`traceValIs`). -/
def traceutil.ctxTraceIs (ctx : GoInterfaceOk) (o : Option Loc) : IProp GF :=
  iprop(□ ∀ Φ : val → IProp GF,
    ▷ (∀ v : GoInterface, ⌜traceutil.traceValIs v o⌝ -∗ Φ #v) -∗
      WP (App (Val #(methods ctx.ty go!"Value" ctx.v)) (Val #traceutil.traceKeyVal)) {{ Φ }})

instance traceutil.ctxTraceIs_persistent (ctx : GoInterfaceOk) (o : Option Loc) :
    Persistent (traceutil.ctxTraceIs (GF := GF) ctx o) := by
  unfold traceutil.ctxTraceIs; infer_instance

end defs

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.traceutil.Assumptions]

/-- No fields: the `nil` slice (a variadic call without arguments). -/
theorem traceutil.ownFields_nil : ⊢ traceutil.ownFields (GF := GF) slice.nil := by
  unfold traceutil.ownFields
  iexists []
  isplitl []
  · iapply ownSlice_nil
  isplitl []
  · iapply ownSliceCap_nil
  ipureintro
  intro ii h
  simp at h

theorem traceutil.fieldsWf_append [GoLocalContext] [GoSemanticsFunctions] {l1 l2 : List traceutil.Field} (h1 : traceutil.fieldsWf l1)
    (h2 : traceutil.fieldsWf l2) : traceutil.fieldsWf (l1 ++ l2) := by
  unfold traceutil.fieldsWf fmt.PureArgsWf at *
  intro ii h
  rw [List.map_append, List.mem_append] at h
  rcases h with h | h
  · exact h1 ii h
  · exact h2 ii h

theorem traceutil.fieldsWf_of_mem [GoLocalContext] [GoSemanticsFunctions] {l : List traceutil.Field} {f : traceutil.Field}
    (h : traceutil.fieldsWf l) (hm : f ∈ l) : traceutil.fieldsWf [f] := by
  unfold traceutil.fieldsWf fmt.PureArgsWf at *
  intro ii hi
  simp only [List.map_cons, List.map_nil, List.mem_singleton] at hi
  exact h ii (by rw [hi]; exact List.mem_map_of_mem hm)

theorem traceutil.fieldsWf_set [GoLocalContext] [GoSemanticsFunctions] {l : List traceutil.Field}
    {f : traceutil.Field} (i : Nat) (h : traceutil.fieldsWf l) (hf : traceutil.fieldsWf [f]) :
    traceutil.fieldsWf (l.set i f) := by
  unfold traceutil.fieldsWf fmt.PureArgsWf at *
  intro ii hi
  rw [List.mem_map] at hi
  obtain ⟨g, hg, he⟩ := hi
  rcases List.mem_or_eq_of_mem_set hg with hg | hg
  · exact h ii (by rw [← he]; exact List.mem_map_of_mem hg)
  · subst hg
    exact hf ii (by rw [← he]; simp)

theorem traceutil.fieldsWf_nil [GoLocalContext] [GoSemanticsFunctions] : traceutil.fieldsWf [] := by
  intro ii h; simp at h

theorem traceutil.fieldsWf_cons_string [GoLocalContext] [GoSemanticsFunctions]
    (k x : GoString) (fs : List traceutil.Field) (h : traceutil.fieldsWf fs) :
    traceutil.fieldsWf ({ Key' := k, Value' := interface.mkOk go.string #x } :: fs) := by
  intro ii hi
  rcases List.mem_cons.1 hi with hi | hi
  · rw [hi]; exact ⟨_, .str _ _ _ .nil⟩
  · exact h ii hi

theorem traceutil.fieldsWf_cons_int [GoLocalContext] [GoSemanticsFunctions]
    (k : GoString) (x : GoInterface) (z : Int) (hz : _root_.Perennial.fmt.IntArg x z)
    (fs : List traceutil.Field) (h : traceutil.fieldsWf fs) :
    traceutil.fieldsWf ({ Key' := k, Value' := x } :: fs) := by
  intro ii hi
  rcases List.mem_cons.1 hi with hi | hi
  · rw [hi]; exact ⟨_, .int _ _ _ _ hz .nil⟩
  · exact h ii hi

theorem traceutil.fieldsWf_cons_bool [GoLocalContext] [GoSemanticsFunctions] (k : GoString)
    (b : Bool) (fs : List traceutil.Field) (h : traceutil.fieldsWf fs) :
    traceutil.fieldsWf ({ Key' := k, Value' := interface.mkOk go.bool #b } :: fs) := by
  intro ii hi
  rcases List.mem_cons.1 hi with hi | hi
  · rw [hi]; exact ⟨_, .bool _ _ _ .nil⟩
  · exact h ii hi

/-- **`context.TODO()` carries no trace**: its `Value` (`emptyCtx`'s) returns `nil`. -/
theorem traceutil.ctxTraceIs_todo :
    ⊢ traceutil.ctxTraceIs (GF := GF) (interface.mk context.todoCtx.ty #(zero_val context.todoCtx))
      none := by
  iunfold traceutil.ctxTraceIs
  imodintro
  iintro %Φ HΦ
  wp_method_call
  wp_auto
  wp_method_call
  wp_auto
  iapply HΦ
  ipureintro; left; rfl

/-- **`context.Background()` carries no trace**: its `Value` (`emptyCtx`'s) returns `nil`. -/
theorem traceutil.ctxTraceIs_background :
    ⊢ traceutil.ctxTraceIs (GF := GF)
      (interface.mk context.backgroundCtx.ty #(zero_val context.backgroundCtx)) none := by
  iunfold traceutil.ctxTraceIs
  imodintro
  iintro %Φ HΦ
  wp_method_call
  wp_auto
  wp_method_call
  wp_auto
  iapply HΦ
  ipureintro; left; rfl

end lemmas

end EtcdGrove
end Perennial
