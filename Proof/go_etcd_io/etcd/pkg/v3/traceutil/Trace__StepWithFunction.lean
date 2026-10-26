/-
Proof of `Spec/go_etcd_io/etcd/pkg/v3/traceutil/Trace__StepWithFunction.lean`. Lean-first (no Rocq counterpart); unit P1b (2026-10-14).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__StepWithFunction
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__disableStep
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__enableStep
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__Step

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.traceutil.Assumptions]

theorem traceutil.Trace.StepWithFunction.wp_proof
    (hDis : traceutil.Trace.disableStep.spec (GF := GF) (hG := hG))
    (hEn : traceutil.Trace.enableStep.spec (GF := GF) (hG := hG))
    (hStep : traceutil.Trace.Step.spec (GF := GF) (hG := hG)) :
    traceutil.Trace.StepWithFunction.spec (GF := GF) (hG := hG) := by
  intro t e f msg fields Q
  wp_start as ⟨Ht, Hf, Hwp⟩
  (try wp_auto)
  wp_apply hDis t e $$ [Ht] as Ht
  · iframe #; iframe Ht
  (try wp_auto)
  wp_bind (App (Val #f) (Val #()))
  iapply wp_wand $$ [Hwp Ht]
  · iapply Hwp $$ Ht
  iintro %v ⟨%Hv, HQ, %e', Ht⟩
  subst Hv
  (try wp_auto)
  wp_apply hEn t e' $$ [Ht] as Ht
  · iframe #; iframe Ht
  (try wp_auto)
  wp_apply hStep t e' msg fields $$ [Ht Hf] as Ht
  · iframe #; iframe
  (try wp_auto)
  iapply HΦ
  iframe HQ
  iexists e'
  iexact Ht

end proof

end EtcdGrove
end Perennial
