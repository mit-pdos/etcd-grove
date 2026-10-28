/-
Proof of `Spec/k8s_io/client_go/tools/cache/Reflector__setLastSyncResourceVersion.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.Reflector__setLastSyncResourceVersion

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

theorem Reflector.setLastSyncResourceVersion.wp_proof : Reflector.setLastSyncResourceVersion.spec (GF := GF) (hG := hG) := by
  intro r v u v'
  wp_start as Hown
  iunfold reflOwn at Hown
  icases Hown with ⟨Hv, Hu, Hmu⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply (sync.RWMutex.wp_Lock _ (fun _ => iprop(True))) $$ [$Hsync $Hmu] as ⟨Hl, -⟩
  (try wp_auto)
  wp_apply (sync.RWMutex.wp_Unlock _ (fun _ => iprop(True))) $$ [$Hsync $Hl] as Hmu
  (try wp_auto)
  iapply HΦ
  iunfold reflOwn
  iframe

end proof

end cache
end EtcdGrove
end Perennial
