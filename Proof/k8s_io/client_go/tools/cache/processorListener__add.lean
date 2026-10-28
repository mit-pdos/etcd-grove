/-
Proof of `Spec/k8s_io/client_go/tools/cache/processorListener__add.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.processorListener__add
public import Spec.k8s_io.client_go.tools.cache.synctrack.SingleFileTracker__Start

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

theorem processorListener.add.wp_proof
    (wp_Start : synctrack.SingleFileTracker.Start.spec (GF := GF) (hG := hG)) :
    processorListener.add.spec (GF := GF) (hG := hG) := by
  intro l γ Q sent e Hbound
  wp_start as ⟨#Hl, Hprod, HQ⟩
  ihave #Hst : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache.synctrack $$ []
  · iPkgInit
  iunfold isListener at Hl
  icases Hl with ⟨%addCh, %nextCh, %t, %h, %lg, %hn, #Hadd, #Hnext, #Hlg, #Hhn, #Hh, #Ht,
    #Hsa, #Hsn, #Hsft, #Hlen⟩
  ihave HP : (if e.initial then synctrack.sftTok γ.tr else iprop(True)) -∗
      notifP Q γ.tr (sent.length : Int) (notifOf e) $$ [HQ]
  · iintro Htok; iunfold notifP; iexists e; simp only [Int.toNat_natCast]; iframe
  cases e with
  | add o b =>
    simp only [notifOf, interface.mkOk]
    wp_auto
    cases b
    · wp_auto
      wp_apply (wp_spsc_send γ.add addCh _ _ sent _) $$ [$Hsa $Hprod HP] as Hprod
      · iapply HP; simp only [Ev.initial, Bool.false_eq_true, ↓reduceIte]; itrivial
      (try wp_auto)
      iapply HΦ; iexact Hprod
    · wp_auto
      wp_apply wp_Start t γ.tr Hbound $$ [$Hst $Hsft] as Htok
      (try wp_auto)
      wp_apply (wp_spsc_send γ.add addCh _ _ sent _) $$ [$Hsa $Hprod HP Htok] as Hprod
      · iapply HP; simp only [Ev.initial, ↓reduceIte]; iexact Htok
      (try wp_auto)
      iapply HΦ; iexact Hprod
  | update a b =>
    simp only [notifOf, interface.mkOk]
    wp_auto
    wp_apply (wp_spsc_send γ.add addCh _ _ sent _) $$ [$Hsa $Hprod HP] as Hprod
    · iapply HP; simp only [Ev.initial, Bool.false_eq_true, ↓reduceIte]; itrivial
    (try wp_auto)
    iapply HΦ; iexact Hprod
  | delete o =>
    simp only [notifOf, interface.mkOk]
    wp_auto
    wp_apply (wp_spsc_send γ.add addCh _ _ sent _) $$ [$Hsa $Hprod HP] as Hprod
    · iapply HP; simp only [Ev.initial, Bool.false_eq_true, ↓reduceIte]; itrivial
    (try wp_auto)
    iapply HΦ; iexact Hprod

end proof

end cache
end EtcdGrove
end Perennial
