/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8sdaemonset/apimodel/watcher__Stop.lean`.
Lean-first: under the server's lock, the watcher's entry of the registered watchers (`watchersLocked`)
holds its stop flag and, while not stopped, the stop channel's sending side, which closes it.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.watcher__Stop
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock
public import Perennial.Spec.sync.Cond__Broadcast

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apimodel

open Iris Iris.BI Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8sdaemonset

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : apimodel.Assumptions]

theorem watcher.Stop.wp_proof
    (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG))
    (wp_Broadcast : sync.Cond.Broadcast.spec (GF := GF) (hG := hG)) :
    watcher.Stop.spec (GF := GF) (hG := hG) := by
  intro _ w γ γw r ns bm inits
  wp_start as #Hw
  unfold watchAt
  icases Hw with ⟨%w', %ch, %dch, %s, %cfg, %g, %hw, #Hch, #Hdch, #Hs, #Hsrv, #Hspsc, #Hdspsc, #Hreg⟩
  have hw' : w' = w := by
    simp [interface.mkOk] at hw; exact (go.intoVal_inj hw).symm
  subst hw'
  ihave #Hsrv' := Hsrv
  iunfold isServer at Hsrv'
  icases Hsrv' with ⟨%L, #Hfx⟩
  iNamed Hfx
  wp_auto
  wp_apply wp_Lock $$ [$Hmu] as ⟨Hown, Hinv⟩
  iunfold lockInv at Hinv
  icases Hinv with ⟨%σ0, %H, Hlk, Hhist, %Hok, Hws⟩
  iunfold watchersLocked at Hws
  icases Hws with ⟨%W, Hauth, Hws⟩
  ihave %hW := ghost_map_lookup $$ Hauth Hreg
  icases (BigSepM.bigSepM_lookup_acc (PROP := IProp GF) hW).1 $$ Hws with ⟨Hwe, Hws⟩
  icases Hwe with ⟨%g', %b, %hg, Hstop, Hprod⟩
  have hg' : g' = g := spscCode_inj hg
  subst hg'
  cases b
  · -- not stopped: stop, close the stop channel
    simp only [Bool.false_eq_true, ↓reduceIte]
    wp_auto
    wp_apply (wp_spsc_close g' dch (fun _ _ => iprop(False)) (fun _ => iprop(True)) []) $$
      [$Hdspsc $Hprod]
    (try wp_auto)
    wp_apply (wp_Broadcast L.cond _) $$ Hcond
    wp_apply wp_Unlock $$ [$Hmu $Hown Hlk Hhist Hauth Hws Hstop]
    · iunfold lockInv
      inext
      iexists σ0, H
      iframe
      isplitr
      · ipureintro; exact Hok
      iunfold watchersLocked
      iexists W
      iframe
      iapply Hws
      iexists g', true
      iframe
      isplitl []
      · ipureintro; rfl
      simp only [↓reduceIte]
      itrivial
    iapply HΦ
    itrivial
  · -- already stopped
    simp only [↓reduceIte]
    wp_auto
    wp_apply wp_Unlock $$ [$Hmu $Hown Hlk Hhist Hauth Hws Hstop Hprod]
    · iunfold lockInv
      inext
      iexists σ0, H
      iframe
      isplitr
      · ipureintro; exact Hok
      iunfold watchersLocked
      iexists W
      iframe
      iapply Hws
      iexists g', true
      iframe
      isplitl []
      · ipureintro; rfl
      simp only [↓reduceIte]
      itrivial
    iapply HΦ
    itrivial

end proof

end apimodel
end EtcdGrove
end Perennial
