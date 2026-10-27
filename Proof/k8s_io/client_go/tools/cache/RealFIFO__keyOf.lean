/-
Proof of `Spec/k8s_io/client_go/tools/cache/RealFIFO__keyOf.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.RealFIFO__keyOf

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.iris.dupNamespace false

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

theorem RealFIFO.keyOf.wp_proof :
    RealFIFO.keyOf.spec (GF := GF) (hG := hG) := by
  intro f OK KF kf obj t v
  wp_start as ⟨#Hkf, #Hkey, #HOK, %hobj⟩
  iunfold keyOk at Hkey
  subst hobj
  (try wp_auto)
  wp_apply Hkey $$ [$HOK]
  iintro %k %err %hk
  obtain ⟨rfl, rfl⟩ := hk
  (try wp_auto)
  iapply HΦ; itrivial

end proof

end cache
end EtcdGrove
end Perennial
