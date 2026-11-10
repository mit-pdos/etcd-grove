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
out). The types are assumed not to implement `fmt.GoStringer` under `%#v`; the callers' are
`errors.New`'s `*errorString`, `fmt.Errorf`'s errors and `time.Duration`, which do not. -/
def fmt.argOk : GoInterface → IProp GF
  | .nil => iprop(True)
  | .ok ii => iprop(⌜_root_.Perennial.fmt.ArgWf ii⌝ ∨
      (fmt.stringMethodSpec ii go!"Error" ∗ ⌜methodSet ii.ty !! go!"Format" = none⌝) ∨
      (fmt.stringMethodSpec ii go!"String" ∗
        ⌜methodSet ii.ty !! go!"Format" = none ∧ methodSet ii.ty !! go!"Error" = none⌝))

/-- Every argument is `fmt.argOk`. -/
def fmt.argsOk : List GoInterface → IProp GF
  | [] => iprop(True)
  | a :: xs => iprop(fmt.argOk a ∗ fmt.argsOk xs)

/-- The argument of a one-element `fmt.ArgsWf` list is `fmt.ArgWf`. -/
theorem fmt.argWf_of_argsWf {ii : GoInterfaceOk}
    (h : _root_.Perennial.fmt.ArgsWf [interface.ok ii]) : _root_.Perennial.fmt.ArgWf ii :=
  h ii (List.mem_singleton_self _)

/-- **`fmt.Errorf(format, args...)`** returns a non-nil error whose `Error()` returns some
string, for arguments that are `fmt.argsOk`; the arguments' slice comes back. (2026-11-04) Its
dynamic type has `Error() string` and no `Format` method (Go's `*fmt.wrapError`,
`*fmt.wrapErrors` and `*errors.errorString`: `Error` and `Unwrap`, or `Error` alone), so that
the error is one `fmt` formats by its `Error()` (`fmtErrorOk`, `fmtErrorOk_of_errorf`); (batch 37.9,
user-approved 2026-11-04) it is a pointer error (`IsPointerError`: all three types are pointers to
structs, and Go returns a fresh one). -/
abbrev fmt.Errorf.spec : Prop :=
  ∀ (format : GoString) (args_sl : GoSlice) (xs : List GoInterface) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦*{dq} xs ∗ fmt.argsOk xs }}
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

/-- Proves `fmt.argsOk xs` of a literal argument list (as `wp_slice_literal` builds it): `nil`,
a `string` or an `int`/`int64`/`uint64` by `fmt.ArgWf`, any other argument by a hypothesis in
the context giving its `Error()` or `String()` method's `fmt.stringMethodSpec`, and a pure one
its method facts (no `Format`; for `String()`, no `Error` either; premise-fixes-4). -/
macro "fmt_args_ok" : tactic => `(tactic| (
  try rw [show sint.nat (W64 (0 + 1)) = 1 by rfl]
  try simp only [List.set_cons_succ, List.set_cons_zero]
  try simp only [Perennial.EtcdGrove.fmt.argsOk, Perennial.EtcdGrove.fmt.argOk]
  repeat' (first
    | isplitr
    | itrivial
    | (ileft; ipureintro; apply Perennial.EtcdGrove.fmt.argWf_of_argsWf
       first
        | exact .cons_string _ _ .nil
        | exact .cons_int _ _ _ (.int64 _) .nil
        | exact .cons_int _ _ _ (.int _) .nil
        | exact .cons_int _ _ _ (.uint64 _) .nil)
    | (iright; ileft; isplitr; iassumption; ipureintro; assumption)
    | (iright; ileft; isplitr; iassumption; ipureintro; exact (‹_ ∧ _›).1)
    | (iright; ileft; isplitr; iassumption; ipureintro; fmt_method_none)
    | (iright; iright; isplitr; iassumption; ipureintro; assumption)
    | (iright; iright; isplitr; iassumption; ipureintro; fmt_method_none))))

end EtcdGrove
end Perennial
