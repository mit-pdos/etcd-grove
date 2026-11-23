/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Server/LogErr.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

`log.Printf` and `log.Println` with error arguments (U2): an argument is either one Go's formatting
calls no method of (`fmt.ArgWf`) or an error with an `Error()` (`models_lab.errAny`, the lab's
`net.rpc.errAny`), whose method Go's formatting calls.

**A hypothesis** (notes/dsv-gryff.md, "Hypotheses"): Perennial `7b2259a12` models `log.Printf` and
`log.Println` as trusted no-ops, and specifies only `Printf` with arguments Go calls no method of
(`log.Printf.spec`, `fmt.ArgsWf`); `Println` has no spec. The lab proved the two statements below
over its own model of `log` (which ran `Error()` through `touch`/`touchAll`). Here they are the
fields of `LogHyps GF`, a premise of the kit's statement (never an instance).
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

/-- `log.Printf` / `log.Println` with `logArg` arguments (the lab's `log.wp_Printf_logArg`,
`log.wp_Println_logArg`): see the file header. -/
class LogHyps [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
    (GF : BundledGFunctors) [HeapGS HasLC.hasLC GF] [go.Semantics] [log.Assumptions] : Prop where
  wp_Printf_logArg : ∀ (msg : GoString) (arg : GoSlice) (xs : List GoInterface) (dq : DFrac),
    {{ isPkgInit (PROP := IProp GF) pkg_id.log ∗ arg ↦*{dq} xs ∗
        □ ([∗list] x ∈ xs, logArg (GF := GF) x) }}
      (App (App (Val (@! log.Printf)) (Val #msg)) (Val #arg))
    {{ RET #(); arg ↦*{dq} xs }}
  wp_Println_logArg : ∀ (arg : GoSlice) (xs : List GoInterface) (dq : DFrac),
    {{ isPkgInit (PROP := IProp GF) pkg_id.log ∗ arg ↦*{dq} xs ∗
        □ ([∗list] x ∈ xs, logArg (GF := GF) x) }}
      (App (Val (@! log.Println)) (Val #arg))
    {{ RET #(); arg ↦*{dq} xs }}

variable [package_sem : log.Assumptions] [LogHyps GF]

theorem log.wp_Printf_logArg (msg : GoString) (arg : GoSlice) (xs : List GoInterface)
    (dq : DFrac) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.log ∗ arg ↦*{dq} xs ∗
        □ ([∗list] x ∈ xs, logArg (GF := GF) x) }}
      (App (App (Val (@! log.Printf)) (Val #msg)) (Val #arg))
    {{ RET #(); arg ↦*{dq} xs }} :=
  LogHyps.wp_Printf_logArg msg arg xs dq

theorem log.wp_Println_logArg (arg : GoSlice) (xs : List GoInterface) (dq : DFrac) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.log ∗ arg ↦*{dq} xs ∗
        □ ([∗list] x ∈ xs, logArg (GF := GF) x) }}
      (App (Val (@! log.Println)) (Val #arg))
    {{ RET #(); arg ↦*{dq} xs }} :=
  LogHyps.wp_Println_logArg arg xs dq

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
