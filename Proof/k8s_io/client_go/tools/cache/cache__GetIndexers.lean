/-
Proof of `Spec/k8s_io/client_go/tools/cache/cache__GetIndexers.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.cache__GetIndexers
public import Spec.k8s_io.client_go.tools.cache.threadSafeMap__GetIndexers

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.tools.cache

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

theorem cache.GetIndexers.wp_proof
    (wp_inner : threadSafeMap.GetIndexers.spec (GF := GF) (hG := hG)) :
    cache.GetIndexers.spec (GF := GF) (hG := hG) := by
  intro ca ts γ OK Fam KF
  wp_start as #Hca
  iunfold isCache at Hca
  icases Hca with ⟨%kf, #Hcs, #Hkf, #Htr, #Hkey, #Hts⟩
  wp_auto
  wp_apply (wp_inner ts γ OK Fam) $$ [$Hts]
  iapply HΦ; itrivial

end proof

end cache
end EtcdGrove
end Perennial
