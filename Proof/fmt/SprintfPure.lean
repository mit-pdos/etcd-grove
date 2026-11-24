/-
`fmt.Sprintf` of arguments that call no method (`nil`, a `bool`, a value of a predeclared integer
type, a `string`): Perennial's spec of the real `Sprintf` (`fmt.Sprintf.spec`, real `fmt` stage 1,
perennial#671) with the arguments given as a pure list (`fmt.PureArgs`) and the output computed
(`fmt.render`), and the tactics that discharge its side conditions on a literal format
(Perennial's `fmt_encode`, `fmt_fits`, `fmt_pure`, `fmt_noquote`; this file's own copies of `PureArgs` and the tactics went to Perennial with `fmt-stage15`). For the callers that format only such values (2026-11-24; until then
they used `fmt.wp_Sprintf_argsWf`, over the trusted model of `Sprintf`).
-/
module

public import Perennial.Spec.fmt.Sprintf
public import Perennial.Proof.fmt.OutLemmas
public import Perennial.Proof.fmt.PureArgs
public import Perennial.Proof.fmt.Args
public import Perennial.Golang.Theory.TypeSet

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section defs
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

theorem fmt.PureArgs.cons_of {x : GoInterface} {a : _root_.Perennial.fmt.Arg}
    {xs : List GoInterface} {args : List _root_.Perennial.fmt.Arg}
    (h1 : _root_.Perennial.fmt.PureArgs [x] [a]) (h2 : _root_.Perennial.fmt.PureArgs xs args) :
    _root_.Perennial.fmt.PureArgs (x :: xs) (a :: args) := by
  cases h1 with
  | nil_ _ _ _ => exact .nil_ _ _ h2
  | bool b _ _ _ => exact .bool b _ _ h2
  | int x z _ _ hx _ => exact .int x z _ _ hx h2
  | str s _ _ _ => exact .str s _ _ h2

/-- Every argument is `nil` or one that calls no method (`fmt.PureArgs`), as `fmt.ArgsWf` has it
for the trusted model's premise. -/
def fmt.PureArgsWf (xs : List GoInterface) : Prop :=
  ∀ ii, interface.ok ii ∈ xs → ∃ a, _root_.Perennial.fmt.PureArgs [interface.ok ii] [a]

theorem fmt.PureArgsWf.toPureArgs {xs : List GoInterface} (h : fmt.PureArgsWf xs) :
    ∃ args, _root_.Perennial.fmt.PureArgs xs args := by
  induction xs with
  | nil => exact ⟨[], .nil⟩
  | cons x xs ih =>
    obtain ⟨args, hargs⟩ := ih (fun ii hi => h ii (List.mem_cons_of_mem _ hi))
    cases x with
    | nil => exact ⟨_, .nil_ _ _ hargs⟩
    | ok ii =>
      obtain ⟨a, ha⟩ := h ii (List.mem_cons_self ..)
      exact ⟨_, fmt.PureArgs.cons_of ha hargs⟩

/-- `%v` formats every argument that calls no method. -/
theorem fmt.PureArgs.dirOk_v {xs : List GoInterface} {args : List _root_.Perennial.fmt.Arg}
    (h : _root_.Perennial.fmt.PureArgs xs args) :
    ∀ a ∈ args, _root_.Perennial.fmt.DirOk none _root_.Perennial.fmt.verb_v a := by
  induction h with
  | nil => simp
  | nil_ _ _ _ ih | bool _ _ _ _ ih | int _ _ _ _ _ _ ih | str _ _ _ _ ih =>
    simp only [List.mem_cons, forall_eq_or_imp]
    refine ⟨?_, ih⟩
    simp [_root_.Perennial.fmt.DirOk, _root_.Perennial.fmt.ZeroWidthOk]

/-! What `fmt.render` writes for each directive of an argument without methods (simp lemmas). -/

@[simp] theorem fmt.dirOutFn_int_d (zw : Option Nat) (z : Int) :
    _root_.Perennial.fmt.dirOutFn zw _root_.Perennial.fmt.verb_d (.int z) =
      _root_.Perennial.fmt.decimalPad (zw.getD 0) z := by
  simp (config := { decide := true }) [_root_.Perennial.fmt.dirOutFn]

@[simp] theorem fmt.dirOutFn_int_v (zw : Option Nat) (z : Int) :
    _root_.Perennial.fmt.dirOutFn zw _root_.Perennial.fmt.verb_v (.int z) =
      _root_.Perennial.fmt.decimalPad (zw.getD 0) z := by
  simp (config := { decide := true }) [_root_.Perennial.fmt.dirOutFn]

@[simp] theorem fmt.dirOutFn_int_x (zw : Option Nat) (z : Int) :
    _root_.Perennial.fmt.dirOutFn zw _root_.Perennial.fmt.verb_x (.int z) =
      _root_.Perennial.fmt.hexPad (zw.getD 0) z := by
  simp (config := { decide := true }) [_root_.Perennial.fmt.dirOutFn]

@[simp] theorem fmt.dirOutFn_str_s (zw : Option Nat) (s : GoString) :
    _root_.Perennial.fmt.dirOutFn zw _root_.Perennial.fmt.verb_s (.str s) = s := by
  simp (config := { decide := true }) [_root_.Perennial.fmt.dirOutFn]

@[simp] theorem fmt.dirOutFn_str_v (zw : Option Nat) (s : GoString) :
    _root_.Perennial.fmt.dirOutFn zw _root_.Perennial.fmt.verb_v (.str s) = s := by
  simp (config := { decide := true }) [_root_.Perennial.fmt.dirOutFn]

@[simp] theorem fmt.dirOutFn_bool_v (zw : Option Nat) (b : Bool) :
    _root_.Perennial.fmt.dirOutFn zw _root_.Perennial.fmt.verb_v (.bool b) =
      if b then go!"true" else go!"false" := rfl

/-- `%x` of an integer of magnitude below `2^64` (any value of Go's integer types) writes at most
17 bytes (16 digits and a sign). -/
theorem fmt.length_hexPad_zero_le (z : Int) (h : z.natAbs < 2 ^ 64) :
    (_root_.Perennial.fmt.hexPad 0 z).length ≤ 17 := by
  have := _root_.Perennial.fmt.length_hexadecimal_le z h
  unfold _root_.Perennial.fmt.hexadecimal at this
  unfold _root_.Perennial.fmt.hexPad
  split <;> simp_all [_root_.Perennial.fmt.padZeros]

end defs

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **`fmt.Sprintf(format, args...)` of arguments that call no method** (`fmt.PureArgs`), the format
`fmt.encode ps` in the verified subset (`fmt.Fits`): returns `fmt.render ps args`, and gives the
arguments' slice back. From Perennial's spec of the real `Sprintf`. -/
theorem fmt.wp_Sprintf_pure (wp_Sprintf : _root_.Perennial.fmt.Sprintf.spec (GF := GF) (hG := hG))
    (format : GoString) (ps : List _root_.Perennial.fmt.Piece) (args_sl : GoSlice)
    (xs : List GoInterface) (args : List _root_.Perennial.fmt.Arg) (dq : DFrac)
    (he : format = _root_.Perennial.fmt.encode ps) (hf : _root_.Perennial.fmt.Fits ps args)
    (hp : _root_.Perennial.fmt.PureArgs xs args)
    (hq : _root_.Perennial.fmt.NoQuote ps := by fmt_noquote) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦*{dq} xs }}
      (App (App (Val (@! _root_.Perennial.fmt.Sprintf)) (Val #format)) (Val #args_sl))
    {{ (s : GoString), RET #s; args_sl ↦*{dq} xs ∗ ⌜s = _root_.Perennial.fmt.render ps args⌝ }} := by
  iintro %Φ Hpre HΦ
  iapply (_root_.Perennial.fmt.Sprintf_pure_of wp_Sprintf format ps args_sl xs args dq he hf hp) $$ Hpre
  inext
  iintro %s ⟨Hsl, %Hout⟩
  iapply HΦ
  iframe
  ipureintro
  exact Hout.2 hq

section methods
variable [package_sem : _root_.Perennial.fmt.Assumptions]

/-! Arguments that `fmt` formats by calling their `Error()` or `String()` (`fmt.Arg.method`),
from the method-set facts the trusted model's premise `fmt.argOk` asked for. -/

theorem fmt.methodSet_none_of_is {t : go.GoType} {ms : List (GoString × Option go.signature)}
    [go.MethodSetIs t ms] (m : GoString) (h : go.methodSetLookup ms m = none) :
    methodSet t !! m = none := by
  have := go.MethodSetIs.method_set_is (t := t) (ms := ms) m
  rw [h] at this; exact this

/-- A type with a method `m`, other than `reflect.Value`, is not one of the types `printArg`'s
type switch formats itself (the predeclared ones have no methods). -/
theorem fmt.not_switchType_of_method {t : go.GoType} (m : GoString) (sig : go.signature)
    (hm : methodSet t !! m = some sig) (hr : t ≠ _root_.Perennial.reflect.Value.ty) :
    ¬ _root_.Perennial.fmt.SwitchType t := by
  intro h
  unfold _root_.Perennial.fmt.SwitchType at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    first
      | exact hr h
      | (subst h; rw [fmt.methodSet_none_of_is m (by rfl)] at hm; cases hm)

/-- `reflect.Value` has no `Error` method. -/
theorem fmt.ne_reflectValue_of_error {t : go.GoType} {sig : go.signature}
    (h : methodSet t !! go!"Error" = some sig) : t ≠ _root_.Perennial.reflect.Value.ty := by
  rintro rfl
  rw [fmt.methodSet_none_of_is go!"Error" (by simp [go.methodSetLookup_cons, go.methodSetLookup_nil])] at h
  cases h

/-- `reflect.Value` has a `CanInterface` method. -/
theorem fmt.ne_reflectValue_of_canInterface {t : go.GoType}
    (h : methodSet t !! go!"CanInterface" = none) : t ≠ _root_.Perennial.reflect.Value.ty := by
  rintro rfl
  have := go.MethodSetIs.method_set_is (t := _root_.Perennial.reflect.Value.ty) go!"CanInterface"
  simp [go.methodSetLookup_cons] at this
  simp_all

/-- An `error` without `Format`: `fmt` calls its `Error()`. -/
theorem fmt.methodArg_error (ii : GoInterfaceOk)
    (hF : methodSet ii.ty !! go!"Format" = none)
    (hE : methodSet ii.ty !! go!"Error" = some _root_.Perennial.fmt.noArgStringSig) :
    _root_.Perennial.fmt.MethodArg ii go!"Error" := by
  refine ⟨fmt.not_switchType_of_method _ _ hE (fmt.ne_reflectValue_of_error hE), ?_,
    Or.inl ⟨rfl, ?_⟩⟩
  · go_type_set
    simp [go.typeSetElemContains, hF]
  · go_type_set
    simp [go.typeSetElemContains, hE, _root_.Perennial.fmt.noArgStringSig]

/-- `isArg` of an `error` without `Format` whose `Error()` returns some string, needing nothing
(`fmt.stringMethodSpec`: what the trusted model's `fmt.argOk` asked of it). -/
theorem fmt.isArg_error (ii : GoInterfaceOk)
    (hF : methodSet ii.ty !! go!"Format" = none)
    (hE : methodSet ii.ty !! go!"Error" = some _root_.Perennial.fmt.noArgStringSig) :
    _root_.Perennial.fmt.stringMethodSpec (GF := GF) ii go!"Error" ⊢
      _root_.Perennial.fmt.isArg (.ok ii) (.method fun _ => True) := by
  iintro #HE
  unfold _root_.Perennial.fmt.isArg
  iexists ii, go!"Error"
  isplitr
  · ipureintro; exact ⟨rfl, fmt.methodArg_error ii hF hE⟩
  unfold _root_.Perennial.fmt.methodSpec
  imodintro
  iintro %Φ HΦ
  unfold _root_.Perennial.fmt.stringMethodSpec
  iapply HE
  inext
  iintro %s
  iapply HΦ
  ipureintro; trivial

/-- A `Stringer` that is not an `error`, without `Format` or `CanInterface`: `fmt` calls its
`String()`. -/
theorem fmt.methodArg_stringer (ii : GoInterfaceOk)
    (hF : methodSet ii.ty !! go!"Format" = none) (hE : methodSet ii.ty !! go!"Error" = none)
    (hS : methodSet ii.ty !! go!"String" = some _root_.Perennial.fmt.noArgStringSig)
    (hC : methodSet ii.ty !! go!"CanInterface" = none) :
    _root_.Perennial.fmt.MethodArg ii go!"String" := by
  refine ⟨fmt.not_switchType_of_method _ _ hS (fmt.ne_reflectValue_of_canInterface hC), ?_,
    Or.inr ⟨rfl, ?_, ?_⟩⟩
  · go_type_set
    simp [go.typeSetElemContains, hF]
  · go_type_set
    simp [go.typeSetElemContains, hE]
  · go_type_set
    simp [go.typeSetElemContains, hS, _root_.Perennial.fmt.noArgStringSig]

/-- `isArg` of such a `Stringer` whose `String()` returns some string, needing nothing. -/
theorem fmt.isArg_stringer (ii : GoInterfaceOk)
    (hF : methodSet ii.ty !! go!"Format" = none) (hE : methodSet ii.ty !! go!"Error" = none)
    (hS : methodSet ii.ty !! go!"String" = some _root_.Perennial.fmt.noArgStringSig)
    (hC : methodSet ii.ty !! go!"CanInterface" = none) :
    _root_.Perennial.fmt.stringMethodSpec (GF := GF) ii go!"String" ⊢
      _root_.Perennial.fmt.isArg (.ok ii) (.method fun _ => True) := by
  iintro #HS
  unfold _root_.Perennial.fmt.isArg
  iexists ii, go!"String"
  isplitr
  · ipureintro; exact ⟨rfl, fmt.methodArg_stringer ii hF hE hS hC⟩
  unfold _root_.Perennial.fmt.methodSpec
  imodintro
  iintro %Φ HΦ
  unfold _root_.Perennial.fmt.stringMethodSpec
  iapply HS
  inext
  iintro %s
  iapply HΦ
  ipureintro; trivial

end methods

end wps

end EtcdGrove
end Perennial
