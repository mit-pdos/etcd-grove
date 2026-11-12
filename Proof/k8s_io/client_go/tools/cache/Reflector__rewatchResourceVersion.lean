/-
Proof of `Spec/k8s_io/client_go/tools/cache/Reflector__rewatchResourceVersion.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.Reflector__rewatchResourceVersion

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

theorem Reflector.rewatchResourceVersion.wp_proof : Reflector.rewatchResourceVersion.spec (GF := GF) (hG := hG) := by
  intro r v u
  wp_start as Hown
  iunfold reflOwn at Hown
  icases Hown with ⟨Hv, Hu, Hmu⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply (sync.RWMutex.wp_RLock _ (fun _ => iprop(True))) $$ [$Hsync $Hmu] as ⟨Hl, -⟩
  (try wp_auto)
  cases u
  · (try wp_auto)
    wp_apply (sync.RWMutex.wp_RUnlock _ (fun _ => iprop(True))) $$ [$Hsync $Hl] as Hmu
    (try wp_auto)
    simp only [rewatchRV, Bool.false_eq_true, ↓reduceIte]
    iapply HΦ
    iunfold reflOwn
    iframe
  · (try wp_auto)
    wp_apply (sync.RWMutex.wp_RUnlock _ (fun _ => iprop(True))) $$ [$Hsync $Hl] as Hmu
    (try wp_auto)
    simp only [rewatchRV, ↓reduceIte]
    iapply HΦ
    iunfold reflOwn
    iframe

end proof

end cache
end EtcdGrove
end Perennial
