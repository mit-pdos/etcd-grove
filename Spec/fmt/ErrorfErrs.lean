/-
`fmt.Errorf(format, args...)` with error arguments (`%w`, `%v`, `%s`): proved from Perennial's
`fmt.wp_Errorf` in `Proof/fmt/ErrorfErrs.lean` (fmtmodel, 2026-11-20: Perennial's model calls the error
arguments' `Error()` as Go does, and its premise `fmt.argsOk` admits them; until then proved over the
previous model, `errors.New(format)`, which ignored the arguments), and the base of the WAL's hypotheses
`fmt.ErrorfErrsNot.spec`/`fmt.ErrorfErrsTerm.spec`. The decoder wraps
`io.ErrUnexpectedEOF` and `Record.Validate`'s error (decoder.go:112, :147-149), `Validate` wraps
`walpb.ErrCRCMismatch` (record.go:26-30), `Create` wraps the cleanup's error and the parent directory's.

**The premise (fmt soundness, 2026-11-18, the attack's `fmtr`/`noterr`/`nested`).** Every argument is
`nil`, of a basic or method-less named type (`fmt.ArgWf`: Go calls no method, under any verb), or one of
`errs`, each `errOk` (= `fmtErrorOk`: its dynamic type has `Error() string` and no `Format`, and its
`Error()` returns some string needing nothing), and then only under `%v`, `%s` or `%w` without `#`
(`fmt.errArgsWf`), and the format has no `#` (so neither `%#v` nor `%#w`, under which Go calls
`GoString()` or reflects: the second attack, 2026-11-18). Go's `printArg` -> `handleMethods` then calls
that `Error()` and nothing else of it (no `Format`: excluded; no `GoString`/reflection: no `#`; no
reflection into its fields: other verbs excluded), so the call touches no memory the caller owns and
raises no panic of its own (`Error()`'s WP rules out a panic in it, the only method called). Until 2026-11-18 `errOk` was the `Error()`
WP alone, with no type facts, and any verb was admitted: a `Format` method ran (`fmtr`), an `Error() int`
was not `fmt`'s error (`noterr`). The post, `errOk err`, is true of Go (`*fmt.wrapError`,
`*fmt.wrapErrors`, `*errors.errorString`: `Error() string`, no `Format`) and of the model.

The post says nothing of what the error wraps (Perennial's `fmt.errorfErr` does): the decoder's specs say
only that such an error is not `nil`.
W3a of `notes/wal-fsext-plan.md`; Lean-first.
-/
module

public import Perennial.Proof.fmt.Base
public import Spec.fmt.ErrorOk

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section args
variable [GooseExts] [GoGlobalContext] [GoLocalContext] [GoSemanticsFunctions]

/-- The verbs under which these specs admit an error argument: `%v`, `%s`, `%w`. -/
def fmt.errArgVerbs : List w8 := [W8 118, W8 115, W8 119]

/-- One argument under its directive `d`: `nil`; `fmt.ArgWf` (a basic or method-less named type: Go
calls no method of it, under any verb); or one of `errs` under `%v`/`%s`/`%w` without `#`. -/
def fmt.errArgAt (errs : List GoInterfaceOk) (d : fmt.Directive) : GoInterface → Prop
  | .nil => True
  | .ok ii => fmt.ArgWf ii ∨ (ii ∈ errs ∧ d.verb ∈ fmt.errArgVerbs ∧ d.sharpV = false)

/-- The arguments under the directives, in order; those left over are printed under `%v` (`EXTRA`). -/
def fmt.errArgsAt (errs : List GoInterfaceOk) : List fmt.Directive → List GoInterface → Prop
  | _, [] => True
  | d :: ds, a :: xs => fmt.errArgAt errs d a ∧ fmt.errArgsAt errs ds xs
  | [], a :: xs => fmt.errArgAt errs ⟨W8 118, false⟩ a ∧ fmt.errArgsAt errs [] xs

/-- **The arguments `args` of `format`, with the error arguments `errs`**: the format has no `#` at all
(byte 35: Go's `doPrintf` sets `sharpV` for `%#w` as for `%#v`, `case 'w'` falling through to `case 'v'`,
and then calls `GoString()` or reflects: the second attack's `%#w`, 2026-11-18,
`/shared/tmp/fmtfix-attack2/sharpw`, `notes/fmt-sharpw.md`; `fmt.Directive.sharpV` records `%#w` too since
then, and the byte check is kept as the plain statement of what the WAL's formats are); its directives parse
(`fmt.fmtDirectives`: no `*`, no `[n]`, digit runs Go accepts) and each argument is `fmt.errArgAt` its
directive. -/
def fmt.errArgsWf (errs : List GoInterfaceOk) (format : GoString) (args : List GoInterface) : Prop :=
  W8 35 ∉ format ∧ ∃ ds, fmt.fmtDirectives format = some ds ∧ fmt.errArgsAt errs ds args

/-- `fmt.errArgsWf` from the format's directives. -/
theorem fmt.errArgsWf_intro {errs : List GoInterfaceOk} {format : GoString} {args : List GoInterface}
    {ds : List fmt.Directive} (h0 : W8 35 ∉ format) (h : fmt.fmtDirectives format = some ds)
    (h2 : fmt.errArgsAt errs ds args) : fmt.errArgsWf errs format args := ⟨h0, ds, h, h2⟩

example : fmt.fmtDirectives go!"%w (after: %v)" = some [⟨W8 119, false⟩, ⟨W8 118, false⟩] := by rfl

end args

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **An error `fmt` formats by its `Error()`, which returns some string needing nothing**
(persistent): its dynamic type has `Error() string` and no `Format`, and `Error()` returns some string
needing nothing; `fmtErrorOk`'s text (`errOk_iff`), stated here without `fmt.Assumptions`. Until
2026-11-18 only the `Error()` WP, without the type facts: see the file header. -/
def errOk (e : GoInterfaceOk) : IProp GF :=
  iprop(⌜methodSet e.ty !! go!"Format" = none ∧ methodSet e.ty !! go!"Error" = some noArgStringSig⌝ ∗
    □ ∀ Φ : val → IProp GF, ▷ (∀ str : GoString, Φ #str) -∗
      WP (App (Val #(methods e.ty go!"Error" e.v)) (Val #())) {{ Φ }})

instance errOk_persistent (e : GoInterfaceOk) : Persistent (errOk (GF := GF) e) := by
  unfold errOk; infer_instance

/-- `errOk`'s `Error()` WP. -/
theorem errOk_wp (e : GoInterfaceOk) : errOk (GF := GF) e ⊢
    □ ∀ Φ : val → IProp GF, ▷ (∀ str : GoString, Φ #str) -∗
      WP (App (Val #(methods e.ty go!"Error" e.v)) (Val #())) {{ Φ }} := by
  unfold errOk
  iintro ⟨-, H⟩
  iexact H

/-- `errOk` is `fmtErrorOk`. -/
theorem errOk_iff (e : GoInterfaceOk) :
    errOk (GF := GF) e ⊣⊢ fmtErrorOk (.ok e) := by
  simp only [errOk, fmtErrorOk, fmt.stringMethodSpec_unfold]
  exact .rfl

theorem errOk_of_fmtErrorOk (e : GoInterfaceOk) :
    fmtErrorOk (GF := GF) (.ok e) ⊢ errOk e := (errOk_iff e).2

theorem errOk_of_fmtErrorOkOrNil (e : GoInterfaceOk) :
    fmtErrorOkOrNil (GF := GF) (.ok e) ⊢ errOk e := (errOk_iff e).2

theorem fmtErrorOk_of_errOk (e : GoInterfaceOk) :
    errOk (GF := GF) e ⊢ fmtErrorOk (.ok e) := (errOk_iff e).1

/-- **`err` is `nil` or `errOk`** (persistent; 2026-11-18): what the writer contract `io.writerStreamP`
says of a failed `Write`'s error, and what the page writer and the encoder pass on. -/
def errOkOrNil : GoInterface → IProp GF
  | .nil => iprop(True)
  | .ok e => errOk e

instance errOkOrNil_persistent (err : GoInterface) : Persistent (errOkOrNil (GF := GF) err) := by
  cases err <;> unfold errOkOrNil <;> infer_instance

theorem errOkOrNil_ne (e : GoInterfaceOk) : errOkOrNil (GF := GF) (.ok e) ⊢ errOk e := .rfl

theorem errOkOrNil_of_fmtErrorOkOrNil (err : GoInterface) :
    fmtErrorOkOrNil (GF := GF) err ⊢ errOkOrNil err := by
  cases err with
  | nil => unfold errOkOrNil; iintro -; itrivial
  | ok e => exact (errOk_iff e).2

theorem errOkOrNil_of_fmtErrorOk (err : GoInterface) :
    fmtErrorOk (GF := GF) err ⊢ errOkOrNil err := by
  cases err with
  | nil => unfold errOkOrNil; iintro -; itrivial
  | ok e => exact (errOk_iff e).2

theorem fmtErrorOk_of_errOkOrNil (err : GoInterface)
    (h : err ≠ GoInterface.nil) : errOkOrNil (GF := GF) err ⊢ fmtErrorOk err := by
  cases err with
  | nil => exact absurd rfl h
  | ok e => exact (errOk_iff e).1

/-- See the file header. -/
abbrev fmt.ErrorfErrs.spec : Prop :=
  ∀ (format : GoString) (args_sl : GoSlice) (args : List GoAny) (errs : List GoInterfaceOk),
  fmt.errArgsWf errs format args →
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦* args ∗ [∗list] e ∈ errs, errOk e }}
      (App (App (Val (@! _root_.Perennial.fmt.Errorf)) (Val #format)) (Val #args_sl))
    {{ (err : GoInterfaceOk), RET #(interface.ok err); errOk err }}


theorem argWf_uint32 (v : w32) : fmt.ArgWf (interface.mk go.uint32 #v) :=
  ⟨fun h => by simp [go.uint32, go.string] at h, fun _ => ⟨_, .uint32 v⟩,
    Or.inl (Or.inr (Or.inr (Or.inl (by simp [fmt.IsIntType]))))⟩

theorem argWf_int64 (v : w64) : fmt.ArgWf (interface.mk go.int64 #v) :=
  ⟨fun h => by simp [go.int64, go.string] at h, fun _ => ⟨_, .int64 v⟩,
    Or.inl (Or.inr (Or.inr (Or.inl (by simp [fmt.IsIntType]))))⟩

theorem argWf_uint64 (v : w64) :
    fmt.ArgWf (interface.mk go.uint64 #v) :=
  ⟨fun h => by simp [go.uint64, go.string] at h, fun _ => ⟨_, .uint64 v⟩,
    Or.inl (Or.inr (Or.inr (Or.inl (by simp [fmt.IsIntType]))))⟩

theorem argWf_int (v : w64) :
    fmt.ArgWf (interface.mk go.int #v) :=
  ⟨fun h => by simp [go.int, go.string] at h, fun _ => ⟨_, .int v⟩,
    Or.inl (Or.inr (Or.inr (Or.inl (by simp [fmt.IsIntType]))))⟩

theorem argWf_string (x : GoString) : fmt.ArgWf (interface.mk go.string #x) := by
  have hu : underlying go.string = go.string := go.IsUnderlying.is_underlying
  refine ⟨fun _ => ⟨x, rfl⟩, fun h => ?_, Or.inl (Or.inl rfl)⟩
  exfalso
  simp only [fmt.IsIntArgType, hu] at h
  rcases h with h | ⟨h, _⟩ <;>
    simp [fmt.IsIntType, go.string, go.int, go.int64, go.int32, go.int16, go.int8, go.uint,
      go.uint64, go.uint32, go.uint16, go.uint8] at h

end spec

/-- **`fmt.errArgsWf` of a call with a literal format** (2026-11-18): the directives by `rfl`, then each
argument either basic (`argWf_*`) or one of the error arguments under `%v`/`%s`/`%w`. -/
macro "errargs_wf" : tactic => `(tactic| (
  refine fmt.errArgsWf_intro (by decide) (by rfl) ?_
  simp only [fmt.errArgsAt, fmt.errArgAt, fmt.errArgVerbs, interface.mkOk]
  repeat' first
    | exact True.intro
    | refine ⟨?_, ?_⟩
    | exact Or.inl (argWf_uint32 _)
    | exact Or.inl (argWf_uint64 _)
    | exact Or.inl (argWf_int64 _)
    | exact Or.inl (argWf_int _)
    | exact Or.inl (argWf_string _)
    | (apply Or.inr; refine ⟨?_, ?_, ?_⟩
       · simp only [List.mem_cons, List.not_mem_nil, _root_.or_false, _root_.true_or, _root_.or_true]
       · decide
       · first | rfl | exact True.intro)))


end EtcdGrove
end Perennial
