/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Server/LogErr.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

`log.Printf` and `log.Println` with error arguments (U2): an argument is either one Go's formatting
calls no method of (`fmt.ArgWf`) or an error with an `Error()` (`models_lab.errAny`, the lab's
`net.rpc.errAny`), whose method Go's formatting calls.

Perennial `7b2259a12` models both as trusted no-ops (`TrustedCode/log.lean`) and specifies only
`Printf` with arguments Go calls no method of (`log.Printf.spec`, `fmt.ArgsWf`); the two statements
below are proved from those bodies, with `logArg` (an error argument's `Error()` runs) as the
condition Go's formatting needs. No hypothesis.
-/
module

public import Net.Proof.models_lab.Errors
public import Perennial.Proof.log.Base
public import Perennial.Proof.fmt.Base

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section logerr
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- An argument `log` may format: no formatting method, or an error. -/
def logArg (v : GoInterface) : IProp GF :=
  iprop(⌜∀ ii, v = interface.ok ii → fmt.ArgWf ii⌝ ∨ models_lab.errAny v)

instance logArg_persistent (v : GoInterface) : Persistent (logArg (GF := GF) v) := by
  unfold logArg; infer_instance

variable [package_sem : log.Assumptions]

/-- `log.Printf` with `logArg` arguments (the lab's `log.wp_Printf_logArg`): proved from Perennial's
model (`TrustedCode/log.lean`'s `Printf.impl`, which returns); `logArg` is the condition under
which Go's formatting, calling each error argument's `Error()`, does not panic. -/
theorem log.wp_Printf_logArg (msg : GoString) (arg : GoSlice) (xs : List GoInterface)
    (dq : DFrac) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.log ∗ arg ↦*{dq} xs ∗
        □ ([∗list] x ∈ xs, logArg (GF := GF) x) }}
      (App (App (Val (@! log.Printf)) (Val #msg)) (Val #arg))
    {{ RET #(); arg ↦*{dq} xs }} := by
  wp_start as ⟨Hsl, -⟩
  wp_end

/-- `log.Println` with `logArg` arguments (the lab's `log.wp_Println_logArg`), as `Printf`. -/
theorem log.wp_Println_logArg (arg : GoSlice) (xs : List GoInterface) (dq : DFrac) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.log ∗ arg ↦*{dq} xs ∗
        □ ([∗list] x ∈ xs, logArg (GF := GF) x) }}
      (App (Val (@! log.Println)) (Val #arg))
    {{ RET #(); arg ↦*{dq} xs }} := by
  wp_start as ⟨Hsl, -⟩
  wp_end

theorem logArg_wf (v : GoInterface) (h : ∀ ii, v = interface.ok ii → fmt.ArgWf ii) :
    ⊢ logArg (GF := GF) v := by
  unfold logArg; iintro; ileft; ipureintro; exact h

theorem logArg_string (s : GoString) [go.string ↓u go.string] :
    ⊢ logArg (GF := GF) (interface.mkOk go.string #s) := by
  apply logArg_wf
  intro ii h
  exact fmt.ArgsWf.cons_string s [] fmt.ArgsWf.nil ii (by rw [h]; simp)

theorem logArg_err (v : GoInterface) : models_lab.errAny (GF := GF) v ⊢ logArg v := by
  unfold logArg; iintro H; iright; iexact H

end logerr

end Perennial
