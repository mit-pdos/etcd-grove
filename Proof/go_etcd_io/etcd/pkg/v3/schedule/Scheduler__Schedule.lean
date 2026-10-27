/-
`Scheduler.Schedule` on the scheduler `NewFIFOScheduler` returns: the interface call is
`(*fifo).Schedule` (`isFifo`: the value is a `*fifo`). Lean-first (2026-10-22; until then a
trust-boundary axiom).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.schedule.Scheduler__Schedule
public import Spec.go_etcd_io.etcd.pkg.v3.schedule.fifo__Schedule

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3 schedule

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.schedule.Assumptions]

theorem schedule.Scheduler.Schedule.wp_proof
    (wp_fifo_Schedule : schedule.fifo.Schedule.spec (GF := GF) (hG := hG)) :
    schedule.Scheduler.Schedule.spec (GF := GF) (hG := hG) := by
  intro fi γ j Pre Prev Post tr
  iintro %Φ ⟨#Hpkg, #Hf, #Hjob, HPre, Htr⟩ HΦ
  iunfold isFifo at Hf
  icases Hf with ⟨-, -, #Hof⟩
  iunfold isFifoOf at Hof
  iunfold fifoOf at Hof
  icases Hof with ⟨%l, %F, %Hfi, #Hfifo⟩
  cases fi
  simp only [interface.mkOk, GoInterface.ok.injEq] at Hfi
  obtain ⟨rfl, rfl⟩ := Hfi
  wp_apply wp_fifo_Schedule l γ F j Pre Prev Post tr $$ [HPre Htr] as Hpost
  · iframe; iframe #
  iapply HΦ $$ Hpost

end proof

end EtcdGrove
end Perennial
