/-
**Hypothesis H6** (notes/dsv-craq.md, "Hypotheses"; `notes/perennial-changes.md`, 2026-11-23):
the `log` calls go-craq makes that Perennial's `log` model does not specify. Perennial proves
`log.Printf` on `fmt.ArgsWf` arguments only (`log.Printf.wp_proof`, used where it suffices);
go-craq's node logs through a `*log.Logger` (`log.Default()`, its `Printf` and `Println`: no
body in the model, the hypothesis), the coordinator calls `log.Println` (proved: a body in the
model), and both the node and the coordinator pass errors (Go calls their `Error()`) and values without formatting methods (`%+v`, `%#v`: no
method called). The specs are the lab's (`Harness/Proof/log.lean`, whose `log` model was its own),
with the arguments `argOk` allows. They are the class `LogHyp` (a `Prop`), taken as an instance by
the proofs that log, up to the kit's statement; never an axiom.
-/
module

public import Perennial.Proof.log
public import Perennial.Proof.log.Printf
public import Perennial.Proof.fmt.Base
public import Net.Proof.models_lab.Errors

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

namespace github_com.despreston.go_craq

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- A `log` argument go-craq passes: `nil` or one `fmt` formats without a method (`fmt.ArgWf`), a
value of a type with neither `Error` nor `String`, or an error with an `Error()` method
(`errAny`). -/
def argOk (v : GoInterface) : IProp GF :=
  iprop(⌜∀ ii, v = interface.ok ii → fmt.ArgWf ii ∨
      (go.typeSetContains ii.ty go.error = false ∧ go.typeSetContains ii.ty fmt.Stringer.ty = false)⌝ ∨
    models_lab.errAny v)

instance argOk_persistent (v : GoInterface) : Persistent (argOk (GF := GF) v) := by
  unfold argOk; infer_instance

/-- Arguments `fmt` formats without a method are `argOk`. -/
theorem argOks_of_wf (xs : List GoInterface) (h : fmt.ArgsWf xs) :
    ⊢ [∗list] x ∈ xs, argOk (GF := GF) x := by
  induction xs with
  | nil => exact BI.BigSepL.bigSepL_nil_intro (P := iprop(emp))
  | cons a l ih =>
    have ha : ⊢ argOk (GF := GF) a := by
      unfold argOk; ileft; ipureintro
      intro ii h'; subst h'; exact Or.inl (h ii List.mem_cons_self)
    have hl := ih (fun ii hi => h ii (List.mem_cons_of_mem _ hi))
    refine Entails.trans ?_ (BI.BigSepL.bigSepL_cons (Φ := fun _ x => argOk (GF := GF) x)).2
    iintro -
    isplitl []
    · iapply ha
    · iapply hl

end defs

/-- **H6** (the file header): the `log` functions Perennial's trusted model leaves without a body
(`log.Default` reads `std`, not allocated in the model; `*Logger`'s methods are not translated),
with Go's preconditions: `Default` returns the standard logger (never nil); a `*Logger`'s
`Printf`/`Println` need a non-nil logger (a nil one panics); a `Logger` is safe for concurrent
use, so the calls need no ownership of it. -/
class LogHyp [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext] {hlc : HasLC}
    (GF : BundledGFunctors) [HeapGS hlc GF] [go.Semantics] [log.Assumptions] : Prop where
  /-- `log.Default()` returns the standard logger, not nil. -/
  wp_Default :
    {{ isPkgInit (PROP := IProp GF) pkg_id.log }}
      (App (Val (@! log.Default)) (Val #()))
    {{ (l : Loc), RET #l; ⌜l ≠ null⌝ }}
  /-- `l.Printf(format, args...)` on a non-nil `*Logger`. -/
  wp_Logger_Printf : ∀ (l : Loc) (msg : GoString) (arg : GoSlice) (xs : List GoInterface)
      (dq : DFrac), l ≠ null →
    {{ isPkgInit (PROP := IProp GF) pkg_id.log ∗ arg ↦*{dq} xs ∗ [∗list] x ∈ xs, argOk x }}
      (App (App (Val (l @!! go.GoType.PointerType log.Logger.ty @!! go!"Printf")) (Val #msg))
        (Val #arg))
    {{ RET #(); arg ↦*{dq} xs }}
  /-- `l.Println(args...)` on a non-nil `*Logger`. -/
  wp_Logger_Println : ∀ (l : Loc) (arg : GoSlice) (xs : List GoInterface) (dq : DFrac),
      l ≠ null →
    {{ isPkgInit (PROP := IProp GF) pkg_id.log ∗ arg ↦*{dq} xs ∗ [∗list] x ∈ xs, argOk x }}
      (App (Val (l @!! go.GoType.PointerType log.Logger.ty @!! go!"Println")) (Val #arg))
    {{ RET #(); arg ↦*{dq} xs }}

/-! `log.Printf` and `log.Println` have bodies in Perennial's trusted model
(`Perennial/TrustedCode/log.lean`: they do nothing), so their specs are proved, not assumed. -/

section printf
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [package_sem : log.Assumptions]

/-- `log.Printf(format, args...)` on arguments `argOk` allows. -/
theorem LogHyp.wp_Printf (msg : GoString) (arg : GoSlice) (xs : List GoInterface) (dq : DFrac) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.log ∗ arg ↦*{dq} xs ∗ [∗list] x ∈ xs, argOk x }}
      (App (App (Val (@! log.Printf)) (Val #msg)) (Val #arg))
    {{ RET #(); arg ↦*{dq} xs }} := by
  wp_start as ⟨Hsl, -⟩
  wp_end

/-- `log.Println(args...)` on arguments `argOk` allows. -/
theorem LogHyp.wp_Println (arg : GoSlice) (xs : List GoInterface) (dq : DFrac) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.log ∗ arg ↦*{dq} xs ∗ [∗list] x ∈ xs, argOk x }}
      (App (Val (@! log.Println)) (Val #arg))
    {{ RET #(); arg ↦*{dq} xs }} := by
  wp_start as ⟨Hsl, -⟩
  wp_end

end printf

end github_com.despreston.go_craq

end Perennial
