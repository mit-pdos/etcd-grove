/-
Proof of `Spec/k8s_io/client_go/tools/cache/RealFIFO__hasSynced_locked.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.RealFIFO__hasSynced_locked

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.iris.dupNamespace false

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

theorem RealFIFO.hasSynced_locked.wp_proof :
    RealFIFO.hasSynced_locked.spec (GF := GF) (hG := hG) := by
  intro f b
  wp_start as Hs
  (try wp_auto)
  iapply HΦ; iframe

end proof

end cache
end EtcdGrove
end Perennial
