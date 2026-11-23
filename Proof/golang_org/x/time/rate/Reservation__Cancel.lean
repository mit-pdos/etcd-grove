/-
Proof of `Spec/golang_org/x/time/rate/Reservation__Cancel.lean` over the real code (x/time/rate
v0.16.0, `rate.go:160-163`: `CancelAt(time.Now())`; rate-wait, 2026-11-23).
-/
module

public import Spec.golang_org.x.time.rate.Reservation__Cancel
public import Spec.golang_org.x.time.rate.Reservation__CancelAt
public import Perennial.Spec.time.Now

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode golang_org.x.time

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : golang_org.x.time.rate.Assumptions]

theorem rate.Reservation.Cancel.wp_proof
    (wp_Now : _root_.Perennial.time.Now.spec (GF := GF) (hG := hG))
    (wp_CancelAt : rate.Reservation.CancelAt.spec (GF := GF) (hG := hG)) :
    rate.Reservation.Cancel.spec (GF := GF) (hG := hG) := by
  intro r rv dq
  wp_start as ⟨Hr, #Hl⟩
  wp_auto
  wp_apply wp_Now as %now -
  wp_apply wp_CancelAt $$ [$Hpkg $Hr $Hl] as Hr
  iapply HΦ
  iexact Hr

end proof

end EtcdGrove
end Perennial
