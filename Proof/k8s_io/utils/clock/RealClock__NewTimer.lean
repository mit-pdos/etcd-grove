/-
`clock.RealClock.NewTimer`, verified: k8s.io/utils/clock's code as released (translated with its body,
`Code/k8s_io/utils/clock.toml`) over Perennial's verified `time`. Until 2026-11-18 a trust-boundary
axiom (its reference implementation, mit-pdos/etcd-refimpl, was this same code).
-/
module

public import Spec.k8s_io.utils.clock.RealClock__NewTimer
public import Perennial.Proof.time
public import Perennial.Proof.time.Link

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

theorem clock.RealClock.NewTimer.wp_proof : clock.RealClock.NewTimer.spec (GF := GF) (hG := hG) := by
  intro c d
  wp_start
  wp_alloc res as Hres
  wp_auto
  wp_apply time.wp_NewTimer as %t %ch %γ #Ht
  wp_alloc p as Hp
  icases typedPointsto_split _ _ _ $$ Hp with Hp
  simp only [TypedPointsto.typedPointstoDef]
  icases Hp with ⟨Hf, -⟩
  imod (typedPointsto_dfractional (GF := GF) _ t).dfractional_persist _ $$ Hf with #Hf
  wp_auto
  iapply HΦ
  unfold clock.realTimerOk
  iexists t, ch, γ
  iframe #

end proof

end EtcdGrove
end Perennial
