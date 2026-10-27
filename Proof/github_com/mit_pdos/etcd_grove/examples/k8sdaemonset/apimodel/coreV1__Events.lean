/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8sdaemonset/apimodel/coreV1__Events.lean`. Lean-first.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.coreV1__Events

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apimodel

open Iris Iris.BI Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8sdaemonset

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : apimodel.Assumptions]

theorem coreV1.Events.wp_proof : coreV1.Events.spec (GF := GF) (hG := hG) := by
  intro _ l γ cfg admin ns
  wp_start as Hl
  wp_auto
  wp_apply wp_alloc as %c Hc
  iapply HΦ
  unfold isEventClient
  iexists c
  isplitr
  · ipureintro; rfl
  itrivial

end proof

end apimodel
end EtcdGrove
end Perennial
