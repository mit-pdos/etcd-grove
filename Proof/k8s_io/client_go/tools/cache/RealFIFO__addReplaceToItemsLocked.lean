/-
Proof of `Spec/k8s_io/client_go/tools/cache/RealFIFO__addReplaceToItemsLocked.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.RealFIFO__addReplaceToItemsLocked

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

theorem RealFIFO.addReplaceToItemsLocked.wp_proof :
    RealFIFO.addReplaceToItemsLocked.spec (GF := GF) (hG := hG) := by
  intro f mp g lk osl rv sl vs
  wp_start as ⟨#Htr, #Hmp, #Hg, #Hgok, #Hcond, Hitems, Hsl, Hcap⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_slice_literal (V := Delta)
    [Delta.mk go!"ReplacedAll" (interface.mkOk ReplacedAllInfo.ty #(ReplacedAllInfo.mk rv osl))]
  isplitr
  · ipureintro; rfl
  iintro %sl2 ⟨Hsl2, -⟩
  (try wp_auto)
  wp_apply wp_slice_append $$ [$Hsl $Hcap $Hsl2] as %sl' ⟨Hsl, Hcap, -⟩
  (try wp_auto)
  wp_apply sync.Cond.wp_Broadcast $$ [$Hcond]
  (try wp_auto)
  cases g with
  | nil => iunfold gaugeOk at Hgok; icases Hgok with ⟨⟩
  | ok gi =>
    iunfold gaugeOk at Hgok
    (try wp_auto)
    wp_apply Hgok
    (try wp_auto)
    iapply HΦ
    iexists sl'
    iframe

end proof

end cache
end EtcdGrove
end Perennial
