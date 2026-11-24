/-
The proof of `klog.loggingT.infoS.spec` (`Spec/k8s_io/klog/v2/loggingT__infoS.lean`), over its
translated body (`klog.go:822-831`; klog-infos, 2026-11-23, etcd-grove#25): no filter, no logger, so
`printS(nil, InfoLog, depth+1, msg, keysAndValues...)`. Lean-first.
-/
module

public import Spec.k8s_io.klog.v2.loggingT__infoS
public import Spec.k8s_io.klog.v2.loggingT__printS

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

theorem klog.loggingT.infoS.wp_proof
    (wp_printS : klog.loggingT.printS.spec (GF := GF) (hG := hG)) :
    klog.loggingT.infoS.spec (GF := GF) (hG := hG) := by
  intro logger filter depth msg args xs dq hok hmsg
  wp_start as ⟨%h, Hargs⟩
  obtain ⟨rfl, rfl⟩ := h
  wp_auto
  wp_apply wp_printS _ _ _ _ _ _ _ hok hmsg $$ [$Hargs] as Hargs
  · iframe #
    ipureintro
    exact ⟨rfl, Or.inl rfl⟩
  try wp_auto
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
