/-
Facts of Perennial's `fmt` vocabulary that the proofs of this directory's `Errorf` specs share: the
formatted string begins with the format's literal text (`fmt.SprintfOut_litPrefix`), directives
without `w` wrap nothing, the directives of `pre ++ "%w"`, and an `error` from its method set.
-/
module

public import Spec.fmt.ErrorfPlain
public import Perennial.Proof.fmt
public import Proof.errors.NewVarCell
public import Proof.fmt.SprintfPure

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

/-- The output of `Sprintf` begins with the format's literal text before its first `%`. -/
theorem fmt.SprintfOut_litPrefix [GooseExts] [GoGlobalContext] [GoLocalContext] [GoSemanticsFunctions]
    {format : GoString} {xs : List GoInterface} {s : GoString}
    (h : _root_.Perennial.fmt.SprintfOut format xs s) : fmt.litPrefix format <+: s := by
  induction h with
  | done => simp [fmt.litPrefix]
  | extra => simp [fmt.litPrefix]
  | byte c f args out hc _ ih =>
    simp only [fmt.litPrefix, List.takeWhile_cons, ne_eq, hc, not_false_eq_true, decide_true,
      ↓reduceIte]
    exact (List.cons_prefix_cons.mpr ⟨rfl, ih⟩)
  | _ => simp [fmt.litPrefix]

/-- Directives none of whose verbs is `w` have no `%w` arguments. -/
theorem fmt.wrapArgsFrom_noW {k n : Nat} {ds : List _root_.Perennial.fmt.Directive}
    (h : ∀ d ∈ ds, d.verb ≠ W8 119) : _root_.Perennial.fmt.wrapArgsFrom k ds n = [] := by
  induction ds generalizing k with
  | nil => rfl
  | cons d ds ih =>
    rw [_root_.Perennial.fmt.wrapArgsFrom_cons_ne _ _ (h d (by simp))]
    exact ih (fun e he => h e (by simp [he]))

/-- The literal text before the first `%` of a format without `%` is all of it. -/
theorem fmt.litPrefix_append_pct (pre f : GoString) (h : (W8 37 : w8) ∉ pre) :
    fmt.litPrefix (pre ++ W8 37 :: f) = pre := by
  induction pre with
  | nil => simp [fmt.litPrefix]
  | cons c pre ih =>
    have hc : c ≠ W8 37 := fun e => h (e ▸ List.mem_cons_self ..)
    have ih' := ih (fun e => h (List.mem_cons_of_mem _ e))
    simp only [fmt.litPrefix, List.cons_append, List.takeWhile_cons, ne_eq, hc, not_false_eq_true,
      decide_true, ↓reduceIte] at ih' ⊢
    rw [ih']

/-- `Sprintf` of a format without `%` and no arguments is the format. -/
theorem fmt.SprintfOut_noPct [GooseExts] [GoGlobalContext] [GoLocalContext] [GoSemanticsFunctions]
    {f s : GoString} (hf : (W8 37 : w8) ∉ f) (h : _root_.Perennial.fmt.SprintfOut f [] s) : s = f := by
  induction f generalizing s with
  | nil => cases h; rfl
  | cons c f ih =>
    have hc : c ≠ W8 37 := fun e => hf (e ▸ List.mem_cons_self ..)
    cases h with
    | byte _ _ _ out _ h' => rw [ih (fun e => hf (List.mem_cons_of_mem _ e)) h']
    | _ => first | exact absurd rfl hc | simp_all

/-- A format without `%` has no directives. -/
theorem fmt.fmtDirectives_noPct (f : GoString) (h : (W8 37 : w8) ∉ f) :
    _root_.Perennial.fmt.fmtDirectives f = some [] := by
  unfold _root_.Perennial.fmt.fmtDirectives
  induction f with
  | nil => rfl
  | cons c f ih =>
    have hc : c ≠ W8 37 := fun e => h (e ▸ List.mem_cons_self ..)
    rw [_root_.Perennial.fmt.fmtDirectivesAux_lit _ hc]
    exact ih (fun e => h (List.mem_cons_of_mem _ e))

/-- The directives of `pre ++ "%w"`, `pre` without `%`: one `%w`. -/
theorem fmt.fmtDirectives_pre_w (pre : GoString) (h : (W8 37 : w8) ∉ pre) :
    _root_.Perennial.fmt.fmtDirectives (pre ++ go!"%w") = some [⟨W8 119, false⟩] := by
  unfold _root_.Perennial.fmt.fmtDirectives
  induction pre with
  | nil => decide
  | cons c pre ih =>
    have hc : c ≠ W8 37 := fun e => h (e ▸ List.mem_cons_self ..)
    rw [List.cons_append, _root_.Perennial.fmt.fmtDirectivesAux_lit _ hc]
    exact ih (fun e => h (List.mem_cons_of_mem _ e))


section sprintf
open Iris Iris.BI Iris.ProofMode
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.fmt.Assumptions]

/-- **`fmt.Errorf(format)`, no `%` and no argument**: `errors.New(format)` (Go's fast path,
`fmt/errors.go`), from Perennial's `fmt.wp_Errorf`: an `*errors.errorString` holding the format for
good, whose `Error()` returns it. What the generated package initializers of `var X =
fmt.Errorf("...")` use (`etc/gen-init.py`, `newvar_steps`). -/
theorem fmt.wp_Errorf_noPct (format : GoString) (args_sl : GoSlice) (hf : (W8 37 : w8) ∉ format) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦* ([] : List GoInterface) }}
      (App (App (Val (@! _root_.Perennial.fmt.Errorf)) (Val #format)) (Val #args_sl))
    {{ (x : Loc), RET #(interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x);
        (□ ∀ Φ : val → IProp GF, ▷ Φ #format -∗
          WP (App (Val #(methods (go.GoType.PointerType _root_.Perennial.errors.errorString.ty)
            go!"Error" #x)) (Val #())) {{ Φ }}) ∗ errStrCell x format }} := by
  iintro %Φ ⟨#Hpkg, Hsl⟩ HΦ
  ihave Hok := _root_.Perennial.fmt.argsOk_of_argsWf (GF := GF)
    (mv := _root_.Perennial.fmt.errorfVerbs) (format := format) (xs := []) (fun _ h => nomatch h)
  wp_apply (_root_.Perennial.fmt.wp_Errorf format args_sl [] (DFrac.own 1)) $$ [$Hpkg $Hsl $Hok]
    as %err ⟨-, %s, %Hs, Herr⟩
  have hs := fmt.SprintfOut_noPct hf Hs
  subst hs
  iunfold _root_.Perennial.fmt.errorfErr at Herr
  icases Herr with ⟨%-, #HE, Hcase⟩
  simp only [fmt.fmtDirectives_noPct _ hf, _root_.Perennial.fmt.wrapArgs,
    _root_.Perennial.fmt.wrapArgsFrom]
  icases Hcase with ⟨%x, %hx, #Hc⟩
  subst hx
  iapply HΦ
  isplitr
  · iexact HE
  · unfold errStrCell; iexact Hc

end sprintf

end EtcdGrove
end Perennial
