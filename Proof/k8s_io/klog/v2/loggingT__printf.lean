/-
The proof of `klog.loggingT.printf.spec` (`Spec/k8s_io/klog/v2/loggingT__printf.lean`), over klog's
translated `printf` (`klog.go:760-762`): `printfDepth` at depth 1. klog-printf, 2026-11-23,
etcd-grove#25. Lean-first.
-/
module

public import Spec.k8s_io.klog.v2.loggingT__printf
public import Spec.k8s_io.klog.v2.loggingT__printfDepth

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

theorem klog.loggingT.printf.wp_proof
    (wp_printfDepth : klog.loggingT.printfDepth.spec (GF := GF) (hG := hG)) :
    klog.loggingT.printf.spec (GF := GF) (hG := hG) := by
  intro s logger filter f args xs dq
  wp_start as ⟨%h, Hargs, Hok⟩
  wp_auto
  wp_apply wp_printfDepth s logger filter (W64 1) f args xs dq $$ [$Hargs $Hok] as ⟨Hargs, Hok⟩
  · iframe #
    ipureintro
    exact h
  try wp_auto
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
