/-
Proof of `Spec/k8s_io/client_go/tools/cache/threadSafeMap__deleteLocked.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.threadSafeMap__deleteLocked
public import Spec.k8s_io.client_go.tools.cache.storeIndex__updateIndices

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

theorem threadSafeMap.deleteLocked.wp_proof
    (wp_upd : storeIndex.updateIndices.spec (GF := GF) (hG := hG)) :
    threadSafeMap.deleteLocked.spec (GF := GF) (hG := hG) := by
  intro c γ OK Fam σ ph key
  wp_start as ⟨#Hidx, #Him, Hph, #Hpers, %Hok⟩
  iunfold tsPhys at Hph
  icases Hph with ⟨Hitems, Hil, Hrv, Hind, Hix, Hfv⟩
  iunfold tsPers at Hpers
  icases Hpers with ⟨#Hfns, #Hits⟩
  (try wp_auto)
  wp_apply (wp_map_lookup2 go.string (go.GoType.InterfaceType []) ph.il σ.items key)
    $$ [$Hil] as Hil
  cases hk : σ.items !! key with
  | none =>
    simp only [Option.getD_none, Option.isSome_none]
    (try wp_auto)
    have hd : GMap.delete key σ.items = σ.items := by
      ext k; simp only [GMap.lookup_delete_iff]; split <;> simp_all
    iapply HΦ
    iexists ph.ix
    iunfold tsPhys
    rw [hd]
    iframe
    ipureintro; exact Hok
  | some o =>
    simp only [Option.getD_some, Option.isSome_some, _root_.decide_true]
    (try wp_auto)
    ihave #Hold : okNil OK o $$ []
    · iapply BigSepM.bigSepM_lookup hk $$ Hits
    ihave #Hnil : okNil OK GoInterface.nil $$ []
    · iunfold okNil; ileft; ipureintro; rfl
    wp_apply (wp_upd γ.idx γ.im ph.ip DFrac.discard 1 ph.fv (σ.fns Fam) ph.ix OK σ.items
        (GMap.delete key σ.items) key o GoInterface.nil)
      $$ [$Him $Hfv $Hfns $Hold $Hnil $Hind $Hix] as ⟨%ix', -, Hfv, Hind, Hix, %Hok'⟩
    · ipureintro
      refine ⟨Hok, by unfold objAt; rw [hk]; rfl, ?_, ?_⟩
      · unfold objAt; rw [GMap.lookup_delete]; rfl
      · intro k hk'; unfold objAt; rw [GMap.lookup_delete_ne _ (Ne.symm hk')]
    (try wp_auto)
    wp_apply (wp_mapDelete ph.il σ.items key go.string (go.GoType.InterfaceType [])) $$ [$Hil] as Hil
    (try wp_auto)
    iapply HΦ
    iexists ix'
    iunfold tsPhys
    iframe
    ipureintro; exact Hok'

end proof

end cache
end EtcdGrove
end Perennial
