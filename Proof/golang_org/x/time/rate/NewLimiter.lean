/-
Proof of `Spec/golang_org/x/time/rate/NewLimiter.lean` over the real code (x/time/rate v0.16.0,
`rate.go:100-106`; prove-smalllibs, 2026-11-20: until then a trust-boundary axiom): the composite
literal's mutex guards its other fields (`limiterRaw`).
-/
module

public import Spec.golang_org.x.time.rate.NewLimiter

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : golang_org.x.time.rate.Assumptions]

theorem rate.NewLimiter.wp_proof : rate.NewLimiter.spec (GF := GF) (hG := hG) := by
  intro r b
  wp_start as -
  iapply wp_fupd
  wp_auto
  iStructNamed «$r0»
  imod _root_.Perennial.sync.init_Mutex (rate.limiterFields (GF := GF) «$r0_ptr») ⊤
    («$r0_ptr».[golang_org.x.time.rate.Limiter, go!"mu"]) $$ mu [limit burst tokens last lastEvent]
    with #Hmu
  · inext
    unfold rate.limiterFields
    iexists _, _, _, _, _
    iframe limit burst tokens last lastEvent
  imodintro
  iapply HΦ
  unfold rate.limiterOk rate.limiterRaw
  imodintro
  iexact Hmu

end proof

end EtcdGrove
end Perennial
