/-
Proof of `Spec/k8s_io/client_go/tools/cache/RealFIFO__HasSynced.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.RealFIFO__HasSynced
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

theorem RealFIFO.HasSynced.wp_proof
    (wp_hsl : RealFIFO.hasSynced_locked.spec (GF := GF) (hG := hG)) :
    RealFIFO.HasSynced.spec (GF := GF) (hG := hG) := by
  intro f γ OK
  iintro %Φ ⟨#Hpkg, #Hf⟩ HAU
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold isFIFO at Hf
  icases Hf with ⟨%ch, %kf, %mp, %g, %h, %uwp, %idn, #Hkf, #Hkey, #Htr, #Hae, #Hbm, #Huwp, #Hbs,
    #Hch, #Hmp, #Hg, #Hgok, #Hh, #Hhok, #Hguard, #Hcond, #Hinv, #Hid, #Hkany⟩
  wp_method_call
  wp_call
  wp_auto
  wp_apply wp_with_defer as %defer defer
  wp_apply (lc := 3) sync.RWMutex.wp_Lock_guard $$ [$Hguard] as ⟨Hlk, Htok⟩
  imod fifo_acquire f γ OK ch $$ Hinv Hlc1 Hlc2 Htok with HR
  iunfold fifoRes at HR
  icases HR with ⟨%q, %sl, %vs, Hex, Hst, Hsy, Hitems, Hsl, Hcap, Hds, Hpop, Hinit, %Hic,
    Hsc, Hcl, Hbc⟩
  (try wp_auto)
  wp_apply (wp_hsl f q.synced) $$ [$Hsc] as Hsc
  imod fifoSt_peek γ q _ $$ [$Hst $HAU] with ⟨Hst, HK⟩
  imod fifo_release f γ OK ch $$ Hinv Hlc3 [Hex Hst Hsy Hitems Hsl Hcap Hds Hpop Hinit Hsc Hcl Hbc]
    with Htok
  · iunfold fifoRes
    iexists (q), sl, vs
    iframe
    ipureintro; exact Hic
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hsync $Hlk $Htok]
  (try wp_auto)
  iapply HK; itrivial

end proof

end cache
end EtcdGrove
end Perennial
