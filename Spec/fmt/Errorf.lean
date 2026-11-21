/-
`fmt.Errorf`, for arguments whose `Error()`/`String()` Go calls: proved from Perennial's
`fmt.wp_Errorf` (fmtmodel, 2026-11-20: Perennial's model of `fmt` formats, calls the arguments'
formatting methods as Go does and wraps `%w`; until then an axiom here). The vocabulary of the
premise moved to Perennial with it (`Perennial/Proof/fmt/{Directives,Args}.lean`: `fmt.Directive`,
`fmt.fmtDirectives`, `fmt.methodVerbs`, `fmt.errorfVerbs`, `fmt.stringMethodSpec`, `fmt.argOk`,
`fmt.argOkAt`, `fmt.argsOkAt`, `fmt.argsOk`, the names used here before). What stays here: the
slice arguments Perennial's model does not follow (`fmt.sliceArgOk`, `fmt.argOkAtSl`, `fmt.argsOkSl`:
`fmt.ErrorfSlice`, `fmt.SprintfSlice`, klog's formatting), lemmas and tactics. Lean-first.
-/
module

public import Perennial.Proof.fmt
public import Perennial.Proof.errors.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

/-- The signature `() string` of `Error` and `String`, as goose writes it in method sets
(Perennial's `fmt.noArgStringSig`). -/
abbrev noArgStringSig : go.signature := _root_.Perennial.fmt.noArgStringSig

attribute [simp] _root_.Perennial.fmt.noArgStringSig

section spec_defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **One argument under the directive `d`**, without `%T`/`%p` (what klog's formatting and the
slices' elements admit): `nil` or `fmt.ArgWf` under any directive; under a verb that is not a method
verb, a value of integer kind with `Error() string` or `String() string` and no `Format` (Go prints
it as an integer by reflection, calling no method: `%d` of raft's `ConfChangeType`; since fmtmodel,
2026-11-20, the method is required, as in Perennial's `fmt.argOkAt`); and `fmt.argOk` under a method
verb other than `%#v`/`%#w` (under `w` only for a type with `Error() string`). The first three
disjuncts of Perennial's `fmt.argOkAt` (`fmt.argOkAt_of_base`). -/
def fmt.argOkAtBase (mv : List w8) (d : fmt.Directive) : GoInterface → IProp GF
  | .nil => iprop(True)
  | .ok ii => iprop(⌜_root_.Perennial.fmt.ArgWf ii⌝ ∨
      ⌜d.verb ∉ mv ∧ _root_.Perennial.fmt.IsIntType (underlying ii.ty) ∧
        methodSet ii.ty !! go!"Format" = none ∧
        (methodSet ii.ty !! go!"Error" = some noArgStringSig ∨
          methodSet ii.ty !! go!"String" = some noArgStringSig)⌝ ∨
      (⌜d.verb ∈ mv ∧ d.sharpV = false ∧
        (d.verb = W8 119 → methodSet ii.ty !! go!"Error" = some noArgStringSig)⌝ ∗
        fmt.argOk (.ok ii)))

/-- An argument `fmt.argOkAtBase` its directive is `fmt.argOkAt` it (Perennial's). -/
theorem fmt.argOkAt_of_base {mv : List w8} {d : fmt.Directive} {a : GoInterface} :
    fmt.argOkAtBase (GF := GF) mv d a ⊢ fmt.argOkAt mv d a := by
  cases a with
  | nil => unfold _root_.Perennial.fmt.argOkAt; iintro _; itrivial
  | ok ii =>
    unfold fmt.argOkAtBase _root_.Perennial.fmt.argOkAt
    iintro (H | H | H)
    · ileft; iexact H
    · iright; ileft; iexact H
    · iright; iright; ileft; iexact H

/-- **A slice argument** under `%v` or `%s` (no `#`), the method verbs being `mv` (2026-11-20, the
user's request: `fmt.Errorf("... %v ...", sets.List(decisions))` of conditional authorization's
union authorizer, and `Sprintf` of the same; until then no slice was admitted): the argument's
dynamic type is an unnamed slice type `[]T` of a non-interface element type `T` (so the slice type
has no methods), its value a slice `sl` read-only for good (`sl ↦*□ xs`: nothing writes it any more,
so formatting it touches nothing the caller owns), and every element, as a value of type `T`, is
`fmt.argOkAtBase` the same directive (no nesting).

Why Go then calls nothing but the elements' admitted methods (go1.27.3, `src/fmt/print.go`):
`printArg` (line 674) finds no simple case for a slice other than `[]byte`, so it calls
`handleMethods` on it (line 746), which finds nothing (an unnamed slice type has no methods: no
`Formatter`, `error`, `Stringer`), then `printValue(reflect.ValueOf(arg), verb, 0)` (line 749).
`printValue`'s `reflect.Slice` case (line 856): under `%s` a slice of a `uint8`-kind element type is
printed as bytes (line 861, no method called); otherwise it writes `[`, then for each element
`p.printValue(f.Index(i), verb, depth+1)` (line 889), then `]` (`%#v` takes the other branch,
line 878, excluded here). At depth 1 `printValue` (line 756; its check, line 758) takes `value.Interface()` (the element,
of dynamic type `T`: `T` is no interface type, so no `reflect.Interface` indirection) and calls
`handleMethods(arg, value, verb)` (line 760) with the same verb: exactly what `fmt.argOkAtBase`
admits of a top-level argument under that verb (`Format` excluded, `Error()`/`String()` with their
WPs; an `fmt.ArgWf` value has no method and is printed by kind, line 764 on). A `nil` slice prints
`[]`. A method's panic is recovered by `catchPanic`, but the WPs admitted rule it out anyway.
Perennial's model of `fmt` does not follow this (it is stuck on reflection into a slice): the calls
with such an argument rest on `fmt.ErrorfSlice`/`fmt.SprintfSlice`. -/
def fmt.sliceArgOk (mv : List w8) (d : fmt.Directive) (ii : GoInterfaceOk) : IProp GF :=
  iprop(⌜d.verb ∈ mv ∧ (d.verb = W8 118 ∨ d.verb = W8 115) ∧ d.sharpV = false⌝ ∗
    ∃ (T : go.GoType) (V : Type) (_ : ZeroVal V) (_ : TypedPointsto (GF := GF) V)
      (_ : IntoValTyped (GF := GF) V T) (sl : GoSlice) (xs : List V),
      ⌜ii.ty = go.GoType.SliceType T ∧ ii.v = #sl ∧ go.isInterfaceType (underlying T) = false⌝ ∗
      sl ↦*□ xs ∗ [∗list] x ∈ xs, fmt.argOkAtBase mv d (interface.mkOk T #x))

/-- **One argument under the directive `d`, slices included**: `fmt.argOkAtBase`, or a slice of
such arguments under `%v`/`%s` (`fmt.sliceArgOk`). -/
def fmt.argOkAtSl (mv : List w8) (d : fmt.Directive) : GoInterface → IProp GF
  | .nil => iprop(True)
  | .ok ii => iprop(fmt.argOkAtBase mv d (.ok ii) ∨ fmt.sliceArgOk mv d ii)

/-- An argument `fmt.argOkAtBase` its directive is `fmt.argOkAtSl` it. -/
theorem fmt.argOkAtSl_of_base {mv : List w8} {d : fmt.Directive} {a : GoInterface} :
    fmt.argOkAtBase (GF := GF) mv d a ⊢ fmt.argOkAtSl mv d a := by
  cases a with
  | nil => unfold fmt.argOkAtSl; iintro _; itrivial
  | ok ii => unfold fmt.argOkAtSl; iintro H; ileft; iexact H

/-- A read-only slice of arguments each `fmt.argOkAtBase` a `%v`/`%s` directive is `fmt.argOkAtSl`
it (`fmt.sliceArgOk`). -/
theorem fmt.argOkAt_slice {mv : List w8} {d : fmt.Directive} {T : go.GoType} {V : Type}
    [ZeroVal V] [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V T]
    (sl : GoSlice) (xs : List V)
    (hd : d.verb ∈ mv ∧ (d.verb = W8 118 ∨ d.verb = W8 115) ∧ d.sharpV = false)
    (hT : go.isInterfaceType (underlying T) = false) :
    sl ↦*□ xs ∗ ([∗list] x ∈ xs, fmt.argOkAtBase (GF := GF) mv d (interface.mkOk T #x)) ⊢
      fmt.argOkAtSl mv d (interface.mkOk (go.GoType.SliceType T) #sl) := by
  iintro ⟨#Hs, Hxs⟩
  unfold fmt.argOkAtSl fmt.sliceArgOk
  iright
  isplitr
  · ipureintro; exact hd
  · iexists T, V, inferInstance, inferInstance, inferInstance, sl, xs
    isplitr
    · ipureintro; exact ⟨rfl, rfl, hT⟩
    isplitr
    · iexact Hs
    · iexact Hxs

/-- The arguments under the directives, slices included: one each, in order; those left over are
printed under `%v` (`EXTRA`). -/
def fmt.argsOkAtSl (mv : List w8) : List fmt.Directive → List GoInterface → IProp GF
  | _, [] => iprop(True)
  | d :: ds, a :: xs => iprop(fmt.argOkAtSl mv d a ∗ fmt.argsOkAtSl mv ds xs)
  | [], a :: xs => iprop(fmt.argOkAtSl mv ⟨W8 118, false⟩ a ∗ fmt.argsOkAtSl mv [] xs)

/-- **The arguments `xs` of the format `format`, slices included**: the format's directives parse
(`fmt.fmtDirectives`) and each argument is `fmt.argOkAtSl` its directive. -/
def fmt.argsOkSl (mv : List w8) (format : GoString) (xs : List GoInterface) : IProp GF :=
  iprop(∃ ds : List fmt.Directive, ⌜fmt.fmtDirectives format = some ds⌝ ∗ fmt.argsOkAtSl mv ds xs)

/-- `fmt.argsOkSl` from the format's directives. -/
theorem fmt.argsOkSl_intro {mv : List w8} {format : GoString} {ds : List fmt.Directive}
    {xs : List GoInterface} (h : fmt.fmtDirectives format = some ds) :
    fmt.argsOkAtSl (GF := GF) mv ds xs ⊢ fmt.argsOkSl mv format xs := by
  unfold fmt.argsOkSl
  iintro H
  iexists ds
  isplitr
  · ipureintro; exact h
  · iexact H

/-- A read-only `[]string` is `fmt.argOkAtSl` a `%v`/`%s` directive (`fmt.sliceArgOk`: strings have
no methods). -/
theorem fmt.argOkAt_strSlice {mv : List w8} {d : fmt.Directive} (sl : GoSlice) (ss : List GoString)
    (hd : d.verb ∈ mv ∧ (d.verb = W8 118 ∨ d.verb = W8 115) ∧ d.sharpV = false) :
    sl ↦*□ ss ⊢ fmt.argOkAtSl (GF := GF) mv d (interface.mkOk (go.GoType.SliceType go.string) #sl) := by
  iintro #Hs
  iapply (fmt.argOkAt_slice (T := go.string) (V := GoString) sl ss hd (by
    rw [go.is_underlying]; rfl))
  isplitr; · iexact Hs
  have key : ∀ (i : Nat) (x : GoString), ss[i]? = some x →
      iprop(□ (True : IProp GF)) ⊢ fmt.argOkAtBase mv d (interface.mkOk go.string #x) := by
    intro i x _
    iintro -
    unfold fmt.argOkAtBase
    ileft
    ipureintro
    exact (show _root_.Perennial.fmt.ArgsWf [interface.mkOk go.string #x] from
      .cons_string _ _ .nil) _ (List.mem_singleton_self _)
  iapply (BigSepL.bigSepL_intro (P := iprop(□ (True : IProp GF))) key)
  imodintro; itrivial

/-- An argument that is `fmt.argOk` is `fmt.argOkAt` a method-verb directive other than `%#v`/`%#w`
and `%w` (premise fixes 6, D; `%w` excluded since fmt soundness 2: under it, `fmt.argOkAt_of_error`). -/
theorem fmt.argOkAt_of_argOk {mv : List w8} {d : fmt.Directive} {a : GoInterface} :
    ⌜d.verb ∈ mv ∧ d.sharpV = false ∧ d.verb ≠ W8 119⌝ ∗ fmt.argOk (GF := GF) a ⊢
      fmt.argOkAt mv d a := by
  cases a with
  | nil => unfold _root_.Perennial.fmt.argOkAt; iintro _; itrivial
  | ok ii =>
    unfold _root_.Perennial.fmt.argOkAt
    iintro ⟨%h, H⟩
    iright; iright; ileft
    isplitr
    · ipureintro; exact ⟨h.1, h.2.1, fun hw => absurd hw h.2.2⟩
    · iexact H

/-- An argument whose `Error()` has `fmt.stringMethodSpec`, of a type with `Error() string` and no
`Format`, is `fmt.argOkAt` any method-verb directive other than `%#v`/`%#w`, `%w` included (fmt
soundness 2, 2026-11-18). -/
theorem fmt.argOkAt_of_error {mv : List w8} {d : fmt.Directive} {ii : GoInterfaceOk} :
    ⌜d.verb ∈ mv ∧ d.sharpV = false⌝ ∗ fmt.stringMethodSpec (GF := GF) ii go!"Error" ∗
      ⌜methodSet ii.ty !! go!"Format" = none ∧ methodSet ii.ty !! go!"Error" = some noArgStringSig⌝ ⊢
      fmt.argOkAt mv d (.ok ii) := by
  unfold _root_.Perennial.fmt.argOkAt _root_.Perennial.fmt.argOk
  iintro ⟨%h, #H, %hm⟩
  iright; iright; ileft
  isplitr
  · ipureintro; exact ⟨h.1, h.2, fun _ => hm.2⟩
  · iright; ileft
    isplitr
    · iexact H
    · ipureintro; exact hm

/-- An integer argument of a type with `Error() string` or `String() string` and no `Format` is
`fmt.argOkAt` a directive whose verb is not a method verb (premise fixes 6, D). -/
theorem fmt.argOkAt_int {mv : List w8} {d : fmt.Directive} {ii : GoInterfaceOk} :
    ⌜d.verb ∉ mv ∧ _root_.Perennial.fmt.IsIntType (underlying ii.ty) ∧
      methodSet ii.ty !! go!"Format" = none ∧
      (methodSet ii.ty !! go!"Error" = some noArgStringSig ∨
        methodSet ii.ty !! go!"String" = some noArgStringSig)⌝ ⊢
      fmt.argOkAt (GF := GF) mv d (.ok ii) := by
  unfold _root_.Perennial.fmt.argOkAt
  iintro %h
  iright; ileft; ipureintro; exact h

/-- No argument is `fmt.argsOkAt` any directives (premise fixes 6, D). -/
theorem fmt.argsOkAt_nil {mv : List w8} {ds : List fmt.Directive} :
    ⊢ fmt.argsOkAt (GF := GF) mv ds [] := by
  cases ds <;> (unfold _root_.Perennial.fmt.argsOkAt; itrivial)

/-- The argument of a one-element `fmt.ArgsWf` list is `fmt.ArgWf`. -/
theorem fmt.argWf_of_argsWf {ii : GoInterfaceOk}
    (h : _root_.Perennial.fmt.ArgsWf [interface.ok ii]) : _root_.Perennial.fmt.ArgWf ii :=
  h ii (List.mem_singleton_self _)

end spec_defs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.fmt.Assumptions]

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

/-- A method's signature in a type's method set, from the type's `go.MethodSetIs` (fmt soundness 2:
for `fmt.argOk`'s `noArgStringSig` facts). -/
theorem fmt.methodSet_some (t : go.GoType) {ms : List (GoString × Option go.signature)}
    [go.MethodSetIs t ms] (m : GoString) (sig : go.signature)
    (h : go.methodSetLookup ms m = some sig) : methodSet t !! m = some sig := by
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

/-- Proves a conjunction of `methodSet t !! m = none` and `methodSet t !! m = some noArgStringSig`
facts for a type `t` with a `go.MethodSetIs` instance (fmt soundness 2). -/
macro "fmt_method_facts" : tactic => `(tactic| (
  repeat' apply And.intro
  all_goals (first
    | (apply Perennial.EtcdGrove.fmt.methodSet_none; first | rfl | decide |
        simp [go.methodSetLookup])
    | (apply Perennial.EtcdGrove.fmt.methodSet_some; first | rfl | decide |
        simp [go.methodSetLookup, Perennial.EtcdGrove.noArgStringSig, _root_.Perennial.fmt.noArgStringSig]))))

/-- Proves the pure part of `fmt.argOkAt`'s method-verb disjunct, `d.verb ∈ mv ∧ d.sharpV = false ∧
(d.verb = W8 119 → methodSet t !! "Error" = some noArgStringSig)`, for a literal directive: under a
verb other than `w` by evaluation, under `w` from a hypothesis or the type's method set (fmt
soundness 2). -/
macro "fmt_verb_ok" : tactic => `(tactic| (
  refine ⟨by decide, by decide, ?_⟩
  first
    | (intro hw; exact absurd hw (by decide))
    | (intro _; first | assumption | (apply And.right; assumption) | fmt_method_facts)))

/-- Turns a goal `fmt.argsOk mv format xs` of a literal format into `fmt.argsOkAt` its directives,
unfolded over the argument list: one `fmt.argOkAt mv d a` per argument (premise fixes 6, D). -/
macro "fmt_args_intro" : tactic => `(tactic| (
  try rw [show sint.nat (W64 (0 + 1)) = 1 by rfl]
  try simp only [List.set_cons_succ, List.set_cons_zero]
  iapply Perennial.fmt.argsOk_intro (by rfl)
  try simp only [Perennial.fmt.argsOkAt]))

/-- `fmt_args_intro` for `fmt.argsOkSl` (slices among the arguments). -/
macro "fmt_args_intro_sl" : tactic => `(tactic| (
  try rw [show sint.nat (W64 (0 + 1)) = 1 by rfl]
  try simp only [List.set_cons_succ, List.set_cons_zero]
  iapply Perennial.EtcdGrove.fmt.argsOkSl_intro (by rfl)
  try simp only [Perennial.EtcdGrove.fmt.argsOkAtSl]))

/-- Turns a goal `fmt.argOkAt mv d a`, `d` a method verb of `mv` other than `%#v`/`%#w`, into
`fmt.argOk a`, or the same goal with `fmt.argOkAt` unfolded into its `fmt.argOk` disjunct
(premise fixes 6, D). -/
macro "fmt_arg_method" : tactic => `(tactic| (
  first
    | (iapply Perennial.EtcdGrove.fmt.argOkAt_of_argOk; isplitr; (ipureintro; decide))
    | (iright; iright; ileft; isplitr; (ipureintro; fmt_verb_ok))))

/-- Proves `fmt.argsOk mv format xs` of a literal format and a literal argument list (as
`wp_slice_literal` builds it): the format's directives by evaluation (premise fixes 6, D), then
each argument: `nil`, a `string` or an `int`/`int64`/`uint64` by `fmt.ArgWf`; under a verb that is
not a method verb, an integer of a named type without `Format` (its underlying type from a
`go.IsUnderlying` instance); under a method verb other than `%#v`/`%#w`, any other argument by a
hypothesis in the context giving its `Error()` or `String()` method's `fmt.stringMethodSpec`, and
a pure one (or the type's method set) its method facts (no `Format`, the method `() string`; for
`String()`, no `Error` either; premise-fixes-4, fmt soundness 2), or by a hypothesis `fmt.argOk a`
(not under `%w`). -/
macro "fmt_args_ok" : tactic => `(tactic| (
  fmt_args_intro
  try simp only [Perennial.fmt.argOkAt, Perennial.fmt.argOk]
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
       refine ⟨?_, ?_, ?_, ?_⟩
       · decide
       · rw [go.is_underlying]; simp [_root_.Perennial.fmt.IsIntType]
       · fmt_method_none
       · first | (left; fmt_method_facts; done) | (right; fmt_method_facts; done))
    | (iright; iright; ileft; isplitr; (ipureintro; fmt_verb_ok))
    | (iapply Perennial.EtcdGrove.fmt.argOkAt_of_argOk; isplitr; (ipureintro; decide); iassumption)
    | (iright; ileft; isplitr; iassumption; ipureintro; assumption)
    | (iright; ileft; isplitr; iassumption; ipureintro; exact ‹_ ∧ _›)
    | (iright; ileft; isplitr; iassumption; ipureintro; fmt_method_facts)
    | (iright; iright; isplitr; iassumption; ipureintro; assumption)
    | (iright; iright; isplitr; iassumption; ipureintro; fmt_method_facts))))

end EtcdGrove
end Perennial
