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

/-! Tests of `fmt.fmtDirectives`. -/

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

end spec

section methods
variable [GooseExts] [GoSemanticsFunctions]

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
