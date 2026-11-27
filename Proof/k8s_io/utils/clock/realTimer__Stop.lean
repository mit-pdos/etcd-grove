/-
`clock.realTimer.Stop`, verified: k8s.io/utils/clock's code as released (translated with its body,
`Code/k8s_io/utils/clock.toml`) over Perennial's verified `time`. Until 2026-11-18 a trust-boundary
axiom (its reference implementation, mit-pdos/etcd-refimpl, was this same code).
-/
module

public import Spec.k8s_io.utils.clock.realTimer__Stop
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

theorem clock.realTimer.Stop.wp_proof : clock.realTimer.Stop.spec (GF := GF) (hG := hG) := by
  intro p
  wp_start as Hok
  unfold clock.realTimerOk
  icases Hok with ⟨%t, %ch, %γ, #Hf, #Ht⟩
  wp_auto
  wp_apply time.Timer.wp_Stop $$ [Ht] as %b -
  · ileft; iexists ch, γ; iexact Ht
  iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
