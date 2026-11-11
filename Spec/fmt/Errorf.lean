/-
`fmt.Errorf`: the trust boundary, for arguments that are not all of predeclared basic types.
Perennial's `fmt.wp_Errorf` covers only arguments of predeclared basic types (`fmt.ArgsWf`: Go
calls the `Error()`/`String()` methods of other arguments, which Perennial's model does not);
etcd's callers pass errors (`%w` of `ErrUnsupportedRequest`) and `time.Duration`s (`%v`).
Lean-first (no Rocq counterpart). Also defines `fmt.argsOk`, the arguments' condition shared
with `fmt.Printf` (`Spec/fmt/Printf.lean`).
-/
module

public import Perennial.Proof.fmt
public import Perennial.Proof.errors.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

/-! ## A format's directives (premise fixes 6, D)

Bytes are `w8`: `%` is 37, `#` 35, `+` 43, `-` 45, `0` 48, space 32, `.` 46, `*` 42, `[` 91,
digits 48 to 57, `v` 118, `s` 115, `x` 120, `X` 88, `q` 113, `w` 119. -/

/-- One directive of a format string that consumes an argument: its verb and whether it is `%#v`
(Go syntax: `GoString()` if the argument has one, else reflection; premise fixes 6, D). -/
structure fmt.Directive where
  verb : w8
  sharpV : Bool
  deriving DecidableEq, Repr

/-- Where `fmt.fmtDirectivesAux` is inside a directive, after its `%`: reading the flags, the
width, or the precision (after the `.`). -/
inductive fmt.DirPhase where
  | flags | width | prec
  deriving DecidableEq, Repr

/-- `fmt.fmtDirectives`' parser, structurally recursive over the bytes: `st = none` in literal
text, `st = some (sharp, ph)` inside a directive, `sharp` saying whether the `#` flag was read and
`ph` what is being read (Go's `doPrintf`). -/
def fmt.fmtDirectivesAux : Option (Bool × fmt.DirPhase) → GoString → Option (List fmt.Directive)
  | _, [] => some []
  | none, b :: bs =>
    if b = W8 37 then fmt.fmtDirectivesAux (some (false, .flags)) bs
    else fmt.fmtDirectivesAux none bs
  | some (sharp, ph), b :: bs =>
    -- `b` as the verb: `*` or `[` (a `*` width or precision, an argument index) is not admitted;
    -- `%%` consumes no argument; any other verb consumes one.
    let verb : Option (List fmt.Directive) :=
      if b = W8 42 ∨ b = W8 91 then none
      else if b = W8 37 then fmt.fmtDirectivesAux none bs
      else (⟨b, sharp && decide (b = W8 118)⟩ :: ·) <$> fmt.fmtDirectivesAux none bs
    let digit : Prop := 48 ≤ b.toNat ∧ b.toNat ≤ 57
    match ph with
    | .flags =>
      if b = W8 35 then fmt.fmtDirectivesAux (some (true, .flags)) bs
      else if b = W8 43 ∨ b = W8 45 ∨ b = W8 48 ∨ b = W8 32 then
        fmt.fmtDirectivesAux (some (sharp, .flags)) bs
      else if digit then fmt.fmtDirectivesAux (some (sharp, .width)) bs
      else if b = W8 46 then fmt.fmtDirectivesAux (some (sharp, .prec)) bs
      else verb
    | .width =>
      if digit then fmt.fmtDirectivesAux (some (sharp, .width)) bs
      else if b = W8 46 then fmt.fmtDirectivesAux (some (sharp, .prec)) bs
      else verb
    | .prec =>
      if digit then fmt.fmtDirectivesAux (some (sharp, .prec)) bs
      else verb

/-- The directives of a format string that consume an argument, in order (premise fixes 6, D):
each `%`, then flags among `+ - # 0 space`, then decimal width, then `.` and decimal precision,
then the verb; `%%` (after any flags, width, precision) and a trailing `%` consume none. `none`
when a directive has a `*` width or precision or an argument index `[n]`, which these specs do not
admit. Decidable: the callers' formats are literals. -/
def fmt.fmtDirectives (format : GoString) : Option (List fmt.Directive) :=
  fmt.fmtDirectivesAux none format

/-! Tests of `fmt.fmtDirectives`. -/

example : fmt.fmtDirectives go!"%w: Limit(%d) not supported" =
    some [⟨W8 119, false⟩, ⟨W8 100, false⟩] := by decide
example : fmt.fmtDirectives go!"%%d %5.2f %#v" = some [⟨W8 102, false⟩, ⟨W8 118, true⟩] := by
  decide
example : fmt.fmtDirectives go!"%#x %+v %-08.3s %.q % d" =
    some [⟨W8 120, false⟩, ⟨W8 118, false⟩, ⟨W8 115, false⟩, ⟨W8 113, false⟩,
      ⟨W8 100, false⟩] := by decide
example : fmt.fmtDirectives go!"%*d" = none := by decide
example : fmt.fmtDirectives go!"%5.*d" = none := by decide
example : fmt.fmtDirectives go!"%[1]d" = none := by decide
example : fmt.fmtDirectives go!"abc%" = some [] := by decide
example : fmt.fmtDirectives go!"%5%%s" = some [⟨W8 115, false⟩] := by decide
example : fmt.fmtDirectives go!"unexpected conf type %d" = some [⟨W8 100, false⟩] := by rfl

/-- The verbs under which `fmt` calls an argument's `Error()`/`String()` (`handleMethods`):
`v s x X q`. -/
def fmt.methodVerbs : List w8 := [W8 118, W8 115, W8 120, W8 88, W8 113]

/-- `Errorf`'s: the method verbs and `w` (`%w` of an `error` is formatted as `%v`). -/
def fmt.errorfVerbs : List w8 := fmt.methodVerbs ++ [W8 119]

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.fmt.Assumptions]

/-- Method `m` of the interface value `ii`, called with no arguments, returns some string,
needing nothing (persistently: `fmt` may call it any number of times). For `Error()` this is
what Perennial's `errors.wp_New` and `fmt.wp_Errorf` give of the errors they return. -/
def fmt.stringMethodSpec (ii : GoInterfaceOk) (m : GoString) : IProp GF :=
  iprop(□ ∀ Φ : val → IProp GF, ▷ (∀ s : GoString, Φ #s) -∗
    WP (App (Val #(methods ii.ty m ii.v)) (Val #())) {{ Φ }})

theorem fmt.stringMethodSpec_unfold (ii : GoInterfaceOk) (m : GoString) :
    fmt.stringMethodSpec (GF := GF) ii m = iprop(□ ∀ Φ : val → IProp GF, ▷ (∀ s : GoString, Φ #s) -∗
      WP (App (Val #(methods ii.ty m ii.v)) (Val #())) {{ Φ }}) := rfl

instance fmt.stringMethodSpec_persistent (ii : GoInterfaceOk) (m : GoString) :
    Persistent (fmt.stringMethodSpec (GF := GF) ii m) := by
  unfold fmt.stringMethodSpec; infer_instance

/-- One argument of `Errorf`/`Printf` that Go formats without panicking or touching memory the
caller owns: `nil`; a value of a predeclared basic type (`fmt.ArgWf`: Go calls no method of
it); a value without a `Format` method whose `Error()` has `fmt.stringMethodSpec`; or a value with
neither a `Format` nor an `Error` method whose `String()` has it (Go calls `Error()` for `%w`, and
`Error()` or `String()` for `%v`/`%s` of an `error`/`Stringer`, but `Format` in place of either
when the type has one, and `Error()` in place of `String()` for an `error`: premise-fixes-4,
2026-11-10, the round-2 premise attack's `fmt-argOk-error-over-string-and-formatter`,
`examples/premisefix/fmtarg`; until then the disjuncts did not exclude `Format` and `Error`; a
panic in the method would be recovered by `fmt`, but the method's effects are what the spec rules
out). What `fmt` needs of an argument under a method verb (`v s x X q`, and `w` in `Errorf`) other
than `%#v`; `fmt.argOkAt` asks it only there (premise fixes 6, D). -/
def fmt.argOk : GoInterface → IProp GF
  | .nil => iprop(True)
  | .ok ii => iprop(⌜_root_.Perennial.fmt.ArgWf ii⌝ ∨
      (fmt.stringMethodSpec ii go!"Error" ∗ ⌜methodSet ii.ty !! go!"Format" = none⌝) ∨
      (fmt.stringMethodSpec ii go!"String" ∗
        ⌜methodSet ii.ty !! go!"Format" = none ∧ methodSet ii.ty !! go!"Error" = none⌝))

/-- **One argument under the directive `d`**, the method verbs being `mv`: `nil` or `fmt.ArgWf`
under any directive; under a verb that is not a method verb, also a value of a type whose
underlying type is an integer type and that has no `Format` method (Go prints it as an integer by
reflection, calling no method: `%d` of raft's `ConfChangeType`, which has `String()`); and
`fmt.argOk` (its `Error()`/`String()` disjuncts) only under a method verb that is not `%#v`. -/
def fmt.argOkAt (mv : List w8) (d : fmt.Directive) : GoInterface → IProp GF
  | .nil => iprop(True)
  | .ok ii => iprop(⌜_root_.Perennial.fmt.ArgWf ii⌝ ∨
      ⌜d.verb ∉ mv ∧ _root_.Perennial.fmt.IsIntType (underlying ii.ty) ∧
        methodSet ii.ty !! go!"Format" = none⌝ ∨
      (⌜d.verb ∈ mv ∧ d.sharpV = false⌝ ∗ fmt.argOk (.ok ii)))

/-- The arguments under the directives: one each, in order; those left over are printed under
`%v` (`EXTRA`). -/
def fmt.argsOkAt (mv : List w8) : List fmt.Directive → List GoInterface → IProp GF
  | _, [] => iprop(True)
  | d :: ds, a :: xs => iprop(fmt.argOkAt mv d a ∗ fmt.argsOkAt mv ds xs)
  | [], a :: xs => iprop(fmt.argOkAt mv ⟨W8 118, false⟩ a ∗ fmt.argsOkAt mv [] xs)

/-- **The arguments `xs` of the format `format`**, the method verbs being `mv` (premise fixes 6,
D: until then every argument was `fmt.argOk`, whatever its verb): the format's directives parse
(`fmt.fmtDirectives`), and each argument is `fmt.argOkAt` its directive. -/
def fmt.argsOk (mv : List w8) (format : GoString) (xs : List GoInterface) : IProp GF :=
  iprop(∃ ds : List fmt.Directive, ⌜fmt.fmtDirectives format = some ds⌝ ∗ fmt.argsOkAt mv ds xs)

/-- `fmt.argsOk` from the format's directives (premise fixes 6, D). -/
theorem fmt.argsOk_intro {mv : List w8} {format : GoString} {ds : List fmt.Directive}
    {xs : List GoInterface} (h : fmt.fmtDirectives format = some ds) :
    fmt.argsOkAt (GF := GF) mv ds xs ⊢ fmt.argsOk mv format xs := by
  unfold fmt.argsOk
  iintro H
  iexists ds
  isplitr
  · ipureintro; exact h
  · iexact H

/-- An argument that is `fmt.argOk` is `fmt.argOkAt` a method-verb directive other than `%#v`
(premise fixes 6, D). -/
theorem fmt.argOkAt_of_argOk {mv : List w8} {d : fmt.Directive} {a : GoInterface} :
    ⌜d.verb ∈ mv ∧ d.sharpV = false⌝ ∗ fmt.argOk (GF := GF) a ⊢ fmt.argOkAt mv d a := by
  cases a with
  | nil => unfold fmt.argOkAt; iintro _; itrivial
  | ok ii =>
    unfold fmt.argOkAt
    iintro ⟨%h, H⟩
    iright; iright
    isplitr
    · ipureintro; exact h
    · iexact H

/-- An integer argument of a named type without `Format` is `fmt.argOkAt` a directive whose verb
is not a method verb (premise fixes 6, D). -/
theorem fmt.argOkAt_int {mv : List w8} {d : fmt.Directive} {ii : GoInterfaceOk} :
    ⌜d.verb ∉ mv ∧ _root_.Perennial.fmt.IsIntType (underlying ii.ty) ∧
      methodSet ii.ty !! go!"Format" = none⌝ ⊢ fmt.argOkAt (GF := GF) mv d (.ok ii) := by
  unfold fmt.argOkAt
  iintro %h
  iright; ileft; ipureintro; exact h

/-- No argument is `fmt.argsOkAt` any directives (premise fixes 6, D). -/
theorem fmt.argsOkAt_nil {mv : List w8} {ds : List fmt.Directive} :
    ⊢ fmt.argsOkAt (GF := GF) mv ds [] := by
  cases ds <;> (unfold fmt.argsOkAt; itrivial)

/-- The argument of a one-element `fmt.ArgsWf` list is `fmt.ArgWf`. -/
theorem fmt.argWf_of_argsWf {ii : GoInterfaceOk}
    (h : _root_.Perennial.fmt.ArgsWf [interface.ok ii]) : _root_.Perennial.fmt.ArgWf ii :=
  h ii (List.mem_singleton_self _)

/-- **`fmt.Errorf(format, args...)`** returns a non-nil error whose `Error()` returns some
string, for arguments that are `fmt.argsOk` under the format's verbs; the arguments' slice comes
back. (2026-11-04) Its
dynamic type has `Error() string` and no `Format` method (Go's `*fmt.wrapError`,
`*fmt.wrapErrors` and `*errors.errorString`: `Error` and `Unwrap`, or `Error` alone), so that
the error is one `fmt` formats by its `Error()` (`fmtErrorOk`, `fmtErrorOk_of_errorf`); (batch 37.9,
user-approved 2026-11-04) it is a pointer error (`IsPointerError`: all three types are pointers to
structs, and Go returns a fresh one). -/
abbrev fmt.Errorf.spec : Prop :=
  ∀ (format : GoString) (args_sl : GoSlice) (xs : List GoInterface) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦*{dq} xs ∗ fmt.argsOk fmt.errorfVerbs format xs }}
    (App (App (Val (@! _root_.Perennial.fmt.Errorf)) (Val #format)) (Val #args_sl))
  {{ (err : GoInterfaceOk), RET #(interface.ok err);
      args_sl ↦*{dq} xs ∗ fmt.stringMethodSpec err go!"Error" ∗
      ⌜methodSet err.ty !! go!"Format" = none ∧
        methodSet err.ty !! go!"Error" = some (go.signature.Signature [] false [go.string])⌝ ∗
      ⌜_root_.Perennial.errors.IsPointerError err⌝ }}

end spec

section methods
variable [GooseExts] [GoSemanticsFunctions]

/-- A method absent from a type's method set, from the type's `go.MethodSetIs` (premise-fixes-4: for
`fmt.argOk`'s method facts). -/
theorem fmt.methodSet_none (t : go.GoType) {ms : List (GoString × Option go.signature)}
    [go.MethodSetIs t ms] (m : GoString) (h : go.methodSetLookup ms m = none) :
    methodSet t !! m = none := by
  have := go.MethodSetIs.method_set_is (t := t) m
  rw [h] at this
  exact this

end methods

/-- Proves `methodSet t !! m = none` (or a conjunction of such) for a type `t` with a
`go.MethodSetIs` instance (premise-fixes-4). -/
macro "fmt_method_none" : tactic => `(tactic| (
  repeat' apply And.intro
  all_goals (apply Perennial.EtcdGrove.fmt.methodSet_none; first | rfl | decide |
    simp [go.methodSetLookup])))

/-- Turns a goal `fmt.argsOk mv format xs` of a literal format into `fmt.argsOkAt` its directives,
unfolded over the argument list: one `fmt.argOkAt mv d a` per argument (premise fixes 6, D). -/
macro "fmt_args_intro" : tactic => `(tactic| (
  try rw [show sint.nat (W64 (0 + 1)) = 1 by rfl]
  try simp only [List.set_cons_succ, List.set_cons_zero]
  iapply Perennial.EtcdGrove.fmt.argsOk_intro (by rfl)
  try simp only [Perennial.EtcdGrove.fmt.argsOkAt]))

/-- Turns a goal `fmt.argOkAt mv d a`, `d` a method verb of `mv` other than `%#v`, into
`fmt.argOk a`, or the same goal with `fmt.argOkAt` unfolded into its `fmt.argOk` disjunct
(premise fixes 6, D). -/
macro "fmt_arg_method" : tactic => `(tactic| (
  first
    | (iapply Perennial.EtcdGrove.fmt.argOkAt_of_argOk; isplitr; (ipureintro; decide))
    | (iright; iright; isplitr; (ipureintro; decide))))

/-- Proves `fmt.argsOk mv format xs` of a literal format and a literal argument list (as
`wp_slice_literal` builds it): the format's directives by evaluation (premise fixes 6, D), then
each argument: `nil`, a `string` or an `int`/`int64`/`uint64` by `fmt.ArgWf`; under a verb that is
not a method verb, an integer of a named type without `Format` (its underlying type from a
`go.IsUnderlying` instance); under a method verb other than `%#v`, any other argument by a
hypothesis in the context giving its `Error()` or `String()` method's `fmt.stringMethodSpec`, and
a pure one its method facts (no `Format`; for `String()`, no `Error` either; premise-fixes-4), or
by a hypothesis `fmt.argOk a`. -/
macro "fmt_args_ok" : tactic => `(tactic| (
  fmt_args_intro
  try simp only [Perennial.EtcdGrove.fmt.argOkAt, Perennial.EtcdGrove.fmt.argOk]
  repeat' (first
    | isplitr
    | itrivial
    | (ileft; ipureintro; apply Perennial.EtcdGrove.fmt.argWf_of_argsWf
       first
        | exact .cons_string _ _ .nil
        | exact .cons_int _ _ _ (.int64 _) .nil
        | exact .cons_int _ _ _ (.int _) .nil
        | exact .cons_int _ _ _ (.uint64 _) .nil)
    | (iright; ileft; ipureintro
       refine ⟨by decide, ?_, by fmt_method_none⟩
       rw [go.is_underlying]; simp [_root_.Perennial.fmt.IsIntType])
    | (iright; iright; isplitr; (ipureintro; decide))
    | (iapply Perennial.EtcdGrove.fmt.argOkAt_of_argOk; isplitr; (ipureintro; decide); iassumption)
    | (iright; ileft; isplitr; iassumption; ipureintro; assumption)
    | (iright; ileft; isplitr; iassumption; ipureintro; exact (‹_ ∧ _›).1)
    | (iright; ileft; isplitr; iassumption; ipureintro; fmt_method_none)
    | (iright; iright; isplitr; iassumption; ipureintro; assumption)
    | (iright; iright; isplitr; iassumption; ipureintro; fmt_method_none))))

end EtcdGrove
end Perennial
