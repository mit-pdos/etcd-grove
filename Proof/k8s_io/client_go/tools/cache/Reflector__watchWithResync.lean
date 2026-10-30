/-
Proof of `Spec/k8s_io/client_go/tools/cache/Reflector__watchWithResync.lean`, over
`wait.Group.Start`'s named hypothesis. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.Reflector__watchWithResync
public import Spec.k8s_io.client_go.tools.cache.Reflector__startResync
public import Spec.k8s_io.apimachinery.pkg.util.wait.Group__Start
public import Perennial.Proof.context.Results

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

theorem Reflector.watchWithResync.wp_proof
    (wp_watch : Reflector.watch.spec (GF := GF) (hG := hG))
    (wp_startResync : Reflector.startResync.spec (GF := GF) (hG := hG))
    (wp_GroupStart : wait.Group.Start.spec (GF := GF) (hG := hG)) :
    Reflector.watchWithResync.spec (GF := GF) (hG := hG) := by
  intro r f lw et dh ctx cs dch γd γa cfg res γf γt γi k hrvu hbm
  wp_start as ⟨#Hfix, #Henv, #Hctx, #Hsctx, #HerrIs, Hst⟩
  ihave #Hctxp : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Hwait : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.wait $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply (chan.wp_make2 (V := GoInterface) (W64 1)) as %ech %γe ⟨#Hech, -, Heown⟩
  · ipureintro; decide
  imod inv_alloc (nroot.@"resyncerrc") ⊤ (ownChan γe GoInterface (.Buffered [])) $$ [Heown]
    with #Heinv
  · inext; iexact Heown
  ihave #HerrCh : errChOk ech $$ []
  · unfold errChOk; iexists γe; iframe #
  (try wp_auto)
  wp_apply (context.wp_WithCancel_any ctx cs) $$ [$Hctxp $Hctx] as %ctx' %γ' %cancel ⟨#Hcancel, #Hctx'⟩
  (try wp_auto)
  ipersist r
  ipersist cancelCtx
  ipersist resyncerrc
  simp only [recv_eq_func_mk]
  wp_apply (wp_GroupStart wg_ptr _) $$ [$Hwait wg] as Hwait'
  · iframe
    inext
    wp_auto
    wp_apply (wp_startResync r f lw et dh ctx' _ ech) $$ [$Hpkg $Hfix $Hctx']
    (try wp_auto)
    itrivial
  (try wp_auto)
  wp_apply (wp_watch r f lw et dh ctx dch γd ech γa cfg res γf γt γi k hrvu hbm)
    $$ [$Hpkg $Hfix $Henv $Hsctx $HerrCh $HerrIs $Hst] as %err Hpost
  (try wp_auto)
  iunfold context.cancelSpec at Hcancel
  wp_apply Hcancel as -
  · itrivial
  (try wp_auto)
  wp_apply Hwait'
  (try wp_auto)
  iapply HΦ
  iexact Hpost

end proof

end cache
end EtcdGrove
end Perennial
