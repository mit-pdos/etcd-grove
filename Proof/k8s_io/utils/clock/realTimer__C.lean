/-
`clock.realTimer.C`, verified: k8s.io/utils/clock's code as released (translated with its body,
`Code/k8s_io/utils/clock.toml`) over Perennial's verified `time`. Until 2026-11-18 a trust-boundary
axiom (its reference implementation, mit-pdos/etcd-refimpl, was this same code).
-/
module

public import Spec.k8s_io.utils.clock.realTimer__C
public import Perennial.Proof.time

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.utils.clock.Assumptions]

theorem clock.realTimer.C.wp_proof : clock.realTimer.C.spec (GF := GF) (hG := hG) := by
  intro p
  wp_start as Hok
  unfold clock.realTimerOk
  icases Hok with ⟨%t, %ch, %γ, #Hf, #Ht⟩
  unfold time.isTimer
  icases Ht with ⟨#HC, -, -, #Hbag⟩
  wp_auto
  iapply HΦ
  iexact Hbag

end proof

end EtcdGrove
end Perennial
