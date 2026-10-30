/-
`Scheduler.Stop` on the scheduler `NewFIFOScheduler` returns: the interface call is `(*fifo).Stop`
(`isFifo`: the value is a `*fifo`). Lean-first (2026-10-22; until then a trust-boundary axiom).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.schedule.Scheduler__Stop
public import Spec.go_etcd_io.etcd.pkg.v3.schedule.fifo__Stop

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

theorem schedule.Scheduler.Stop.wp_proof
    (wp_fifo_Stop : schedule.fifo.Stop.spec (GF := GF) (hG := hG)) :
    schedule.Scheduler.Stop.spec (GF := GF) (hG := hG) := by
  intro fi γ Ps
  iintro %Φ ⟨#Hpkg, #Hf, Htok, Hq⟩ HΦ
  iunfold isFifo at Hf
  icases Hf with ⟨-, -, #Hof⟩
  iunfold isFifoOf at Hof
  iunfold fifoOf at Hof
  icases Hof with ⟨%l, %F, %Hfi, #Hfifo⟩
  cases fi
  simp only [interface.mkOk, GoInterface.ok.injEq] at Hfi
  obtain ⟨rfl, rfl⟩ := Hfi
  wp_apply wp_fifo_Stop l γ F Ps $$ [Htok Hq] as HP
  · iframe; iframe #
  iapply HΦ
  iexact HP

end proof

end EtcdGrove
end Perennial
