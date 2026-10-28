/-
Proof of `Spec/k8s_io/client_go/tools/cache/newStoreMetrics.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.newStoreMetrics
public import Spec.k8s_io.client_go.tools.cache.noopMetric__Set
public import Spec.k8s_io.client_go.tools.cache.InformerNameAndResource__Reserved

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.tools.cache

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

theorem newStoreMetrics.wp_proof
    (wp_Set : noopMetric.Set.spec (GF := GF) (hG := hG))
    (wp_Reserved : InformerNameAndResource.Reserved.spec (GF := GF) (hG := hG)) :
    newStoreMetrics.spec (GF := GF) (hG := hG) := by
  intro id p
  wp_start as %hpre
  obtain ⟨hres, hp⟩ := hpre
  cases p with
  | nil => exact absurd rfl hp
  | ok pi =>
  wp_auto
  wp_method_call
  wp_call
  (try wp_auto)
  iStructNamed «$r0»
  ipersist storeResourceVersion
  wp_apply wp_Reserved
  · ipureintro; exact hres
  (try wp_auto)
  iapply HΦ
  iexists interface.mkOk noopMetric.ty #(zero_val noopMetric)
  iframe #
  iunfold gaugeOk
  iintro %x
  imodintro
  iintro %Φ' - HΦ'
  iapply (wp_Set (zero_val noopMetric) x) $$ [] HΦ'
  itrivial

end proof

end cache
end EtcdGrove
end Perennial
