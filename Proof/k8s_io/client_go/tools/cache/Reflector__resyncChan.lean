/-
Proof of `Spec/k8s_io/client_go/tools/cache/Reflector__resyncChan.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.Reflector__resyncChan

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.tools.cache apimodel informer

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

theorem Reflector.resyncChan.wp_proof : Reflector.resyncChan.spec (GF := GF) (hG := hG) := by
  intro r
  wp_start as #Hrp
  wp_auto
  iapply HΦ
  unfold cleanupOk
  imodintro
  iintro %Φ' HΦ'
  wp_auto
  iexact HΦ'

end proof

end cache
end EtcdGrove
end Perennial
