/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureLb/RInv.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit L-b: **`RInv` holds along every run** (`rinv`).
-/
module

public import Dsverify.Proof.gryff.PureLb.Steps6

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure

open model kahn proto dsverify_lab.harness

/-- **`RInv` is kept by every step.** -/
theorem rinv_step {l : List Label} {c c' : Cfg gNet} {i : Fin 3} {e : Ev} {x : List Ext}
    (h : GRun (Cfg.init gNet) l c) (hi : RInv l c) (hs : GStep c i e c' x) :
    RInv (l ++ [(i, e)]) c' := by
  obtain ⟨s', o, hst⟩ := StepAt.of h hs
  have hW := winv h
  cases e with
  | read => exact rinv_read hst hW hi
  | write => exact rinv_write hst hW hi
  | rmw => exact rinv_rmw hst hW hi
  | msg m =>
    cases m with
    | read1 => exact rinv_read1 hst hi
    | read2 m => exact (hi.1 i _ (hst.recv _ rfl)).elim
    | write1 => exact rinv_write1 hst hi
    | write2 => exact rinv_write2 hst hi
    | read1Reply => exact rinv_read1Reply hst hi
    | read2Reply m => exact (hi.1 i _ (hst.recv _ rfl)).elim
    | write1Reply => exact rinv_write1Reply hst hW hi
    | write2Reply => exact rinv_write2Reply hst hW hi
    | _ => exact rinv_other hst rfl hi
  | _ => exact rinv_other hst rfl hi

/-- **The read-record invariant holds along every run.** -/
theorem rinv {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) : RInv l c :=
  grun_inv RInv rinv_init (fun _ _ _ _ _ _ h hi hs => rinv_step h hi hs) l c h

end Perennial.gryff.pure

