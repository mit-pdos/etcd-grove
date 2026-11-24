/-
The proof of `klog.loggingT.printDepth.spec` (`Spec/k8s_io/klog/v2/loggingT__printDepth.lean`), over its
translated body (`klog.go:733-740`; klog-infos, 2026-11-23, etcd-grove#25): the dead `if false`
branch, `header`, then `printWithInfos` of the header's buffer. Lean-first.
-/
module

public import Spec.k8s_io.klog.v2.loggingT__printDepth
public import Spec.k8s_io.klog.v2.loggingT__header
public import Spec.k8s_io.klog.v2.loggingT__printWithInfos

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

theorem klog.loggingT.printDepth.wp_proof
    (wp_header : klog.loggingT.header.spec (GF := GF) (hG := hG))
    (wp_printWithInfos : klog.loggingT.printWithInfos.spec (GF := GF) (hG := hG)) :
    klog.loggingT.printDepth.spec (GF := GF) (hG := hG) := by
  intro s logger filter depth args dq lb bs
  wp_start as ⟨%h, Hargs, Hlb⟩
  wp_auto
  wp_apply wp_header as %b %file %line ⟨%hdr, %hh, Hbuf⟩
  try wp_auto
  wp_apply wp_printWithInfos $$ [$Hbuf $Hargs $Hlb] as ⟨Hargs, Hlb⟩
  · iframe #
    ipureintro; exact h
  try wp_auto
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
