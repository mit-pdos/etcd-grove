/-
The proof of `klog.loggingT.output.spec` (`Spec/k8s_io/klog/v2/loggingT__output.lean`), over the
trusted model `loggingT.output.impl` (`TrustedCode/k8s_io/klog/v2.lean`): with no logger and a
severity 0..3, it returns. klog-printf, 2026-11-23, etcd-grove#25. Lean-first.
-/
module

public import Spec.k8s_io.klog.v2.loggingT__output

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.klog.v2.Assumptions]

theorem klog.loggingT.output.wp_proof : klog.loggingT.output.spec (GF := GF) (hG := hG) := by
  intro l s logger buf depth file line also
  wp_start as %h
  obtain ⟨rfl, hs⟩ := h
  have hty : (k8s_io.klog.v2.model.logWriter : go.GoType) = k8s_io.klog.v2.logWriter.ty := by
    with_unfolding_all rfl
  simp only [hty]
  wp_auto
  rcases hs with rfl | rfl | rfl | rfl <;> (wp_auto; iapply HΦ; itrivial)

end proof

end EtcdGrove
end Perennial
