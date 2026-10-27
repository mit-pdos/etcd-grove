/-
Proof of `Spec/k8s_io/client_go/tools/cache/threadSafeMap__LastStoreSyncResourceVersion.lean`.
Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.threadSafeMap__LastStoreSyncResourceVersion

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

theorem threadSafeMap.LastStoreSyncResourceVersion.wp_proof :
    threadSafeMap.LastStoreSyncResourceVersion.spec (GF := GF) (hG := hG) := by
  intro c γ OK Fam
  iintro %Φ ⟨#Hpkg, #Hc, Hrd, #Hgate⟩ HAU
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold isTS at Hc
  icases Hc with ⟨%mp, %g, #Hidx, #Him, #Hmp, #Hg, #Hgok, #Hguard⟩
  iunfold features.gateIs at Hgate
  wp_method_call
  wp_call
  wp_auto
  wp_apply wp_with_defer as %defer defer
  wp_apply Hgate as %gv ⟨%i, %hi, #Hen⟩
  subst hi
  wp_auto
  wp_apply Hen
  iunfold tsReader at Hrd
  wp_apply (lc := 2) sync.RWMutex.wp_RLock $$ [$Hrd] as ⟨Hrl, HP⟩
  iunfold tsP at HP
  icases HP with ⟨%σ, %ph, %iv, Hst, Hgp, Hph, #Hpers, %Hok⟩
  iunfold tsPhys at Hph
  icases Hph with ⟨Hitems, Hil, Hrv, Hind, Hix, Hfv⟩
  wp_auto
  imod storeSt_peek γ _ σ _ $$ [$Hst $HAU] with ⟨Hst, HK⟩
  wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl Hgp Hitems Hrv Hind Hix Hfv Hil Hst]
  · inext
    iunfold tsP
    iexists σ, ph, iv
    iframe; iframe #
    isplitl
    · iunfold tsPhys; iframe
    · ipureintro; exact Hok
  iintro Hrd
  wp_auto
  iapply HK
  iunfold tsReader; iexact Hrd

end proof

end cache
end EtcdGrove
end Perennial
