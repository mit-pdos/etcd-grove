/-
Proof of `Spec/k8s_io/client_go/tools/cache/threadSafeMap__updateLocked.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.threadSafeMap__updateLocked
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

theorem threadSafeMap.updateLocked.wp_proof
    (wp_upd : storeIndex.updateIndices.spec (GF := GF) (hG := hG)) :
    threadSafeMap.updateLocked.spec (GF := GF) (hG := hG) := by
  intro c γ OK Fam σ ph key obj
  wp_start as ⟨#Hidx, #Him, Hph, #Hpers, #Hobj, %Hok⟩
  iunfold tsPhys at Hph
  icases Hph with ⟨Hitems, Hil, Hrv, Hind, Hix, Hfv⟩
  iunfold tsPers at Hpers
  icases Hpers with ⟨#Hfns, #Hits⟩
  (try wp_auto)
  wp_apply (wp_map_lookup1 go.string (go.GoType.InterfaceType []) ph.il σ.items key)
    $$ [$Hil] as Hil
  (try wp_auto)
  wp_apply (wp_mapInsert go.string ph.il σ.items key obj) $$ [$Hil] as Hil
  (try wp_auto)
  ihave #Hold : okNil OK ((σ.items !! key).getD GoInterface.nil) $$ []
  · skip
    cases hk : σ.items !! key with
    | none => iunfold okNil; ileft; ipureintro; rfl
    | some o => iapply BigSepM.bigSepM_lookup hk $$ Hits
  wp_apply (wp_upd γ.idx γ.im ph.ip DFrac.discard 1 ph.fv (σ.fns Fam) ph.ix OK σ.items
      (<[key := obj]> σ.items) key ((σ.items !! key).getD GoInterface.nil) obj)
    $$ [$Him $Hfv $Hfns $Hold $Hobj $Hind $Hix] as ⟨%ix', -, Hfv, Hind, Hix, %Hok'⟩
  · ipureintro
    refine ⟨Hok, rfl, ?_, ?_⟩
    · unfold objAt; rw [GMap.lookup_insert]; rfl
    · intro k hk; unfold objAt; rw [GMap.lookup_insert_ne _ _ (Ne.symm hk)]
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
