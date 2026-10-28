/-
Proof of `Spec/k8s_io/client_go/tools/cache/Reflector__startResync.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.Reflector__startResync
public import Spec.k8s_io.klog.v2.FromContext

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.tools.cache apimodel informer

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

theorem Reflector.startResync.wp_proof
    (wp_resyncChan : Reflector.resyncChan.spec (GF := GF) (hG := hG))
    (wp_FromContext : klog.FromContext.spec (GF := GF) (hG := hG)) :
    Reflector.startResync.spec (GF := GF) (hG := hG) := by
  intro r f lw et dh ctx cs errCh
  wp_start as ⟨#Hfix, #Hctx⟩
  ihave #Hklog : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.klog.v2 $$ []
  · iPkgInit
  iunfold reflFixed at Hfix
  icases Hfix with ⟨#Hf1, -, -⟩
  iunfold reflFixed1 at Hf1
  icases Hf1 with ⟨%c, -, -, -, -, #Hrp, -, -⟩
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply (wp_FromContext (GoInterface.ok ctx)) $$ [$Hklog] as %lg -
  · ipureintro; simp
  (try wp_auto)
  wp_apply (wp_resyncChan r) $$ [$Hpkg $Hrp] as %cf #Hcf
  (try wp_auto)
  wp_for
  ihave #Hctx2 := Hctx
  iunfold context.isContext at Hctx2
  iunfold context.isContextDef at Hctx2
  iNamed Hctx2
  wp_apply HDone as %dch %γd #Hdone
  wp_apply_core chan.wp_select_blocking_nil
  iapply BigAndL.bigAndL_cons.2
  isplit
  · iright
    iapply (chan.nilClausePre_recv time.Time _ _ rfl)
  iapply BigAndL.bigAndL_cons.2
  isplit
  · ileft
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, dch, γd
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply context.isContextDone_is_chan $$ Hdone
    iapply context.isContextDone_receive _ _ _ _ $$ Hdone
    iintro -
    wp_auto
    wp_for_post
    (try wp_auto)
    iunfold cleanupOk at Hcf
    wp_apply Hcf
    (try wp_auto)
    iapply HΦ
    itrivial
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end cache
end EtcdGrove
end Perennial
