/-
Proof of `Spec/k8s_io/client_go/util/consistency/ownerRecord__WroteAt.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.consistency.ownerRecord__WroteAt
public import Spec.k8s_io.apimachinery.pkg.util.resourceversion.CompareResourceVersion
public import Proof.k8s_io.client_go.util.consistency.InvLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace consistency

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.util.consistency resourceversion

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.util.consistency.Assumptions]

theorem ownerRecord.WroteAt.wp_proof
    (wp_Compare : resourceversion.CompareResourceVersion.spec (GF := GF) (hG := hG)) :
    ownerRecord.WroteAt.spec (GF := GF) (hG := hG) := by
  intro γ T r s id gr rv q
  wp_start as ⟨#Hinv, #Hexcl, #Hrec, Htok⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hrv : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.resourceversion $$ []
  · iPkgInit
  ihave #Hrec' := Hrec
  iunfold isRec at Hrec'
  icases Hrec' with ⟨-, Hphys⟩
  iunfold recPhys at Hphys
  icases Hphys with ⟨#Huid, #Hvm, #Hmu⟩
  wp_apply wp_with_defer as %defer defer
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HI⟩
  iunfold recLockInv at HI
  icases HI with ⟨%V, Hvmap, Hg⟩
  wp_apply (lc := 3) wp_map_lookup2 $$ [$Hvmap] as Hvmap
  imod rec_vs_wf γ T V $$ [$Hinv $Hlc1 $Hrec $Hg] with ⟨Hg, %HVwf⟩
  cases hv : V !! gr with
  | none =>
    simp only [Option.isSome_none, Bool.false_eq_true, decide_false, Bool.not_false]
    wp_auto
    wp_apply wp_Compare
    cases hw : wellFormed rv
    · simp only [compareRV, hw, Bool.false_eq_true, ↓reduceIte]
      wp_auto
      have hV' : wroteAtVs V gr rv = V := by simp [wroteAtVs, hw]
      imod withdraw_commit γ T V $$ [$Hinv $Hexcl $Hlc2 $Hrec $Htok $Hg] with ⟨Hg, HT⟩
      rw [hV']
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hvmap Hg]
      · iunfold recLockInv; iexists V; iframe
      iapply HΦ $$ HT
    · simp only [compareRV, hw, ↓reduceIte]
      wp_auto
      wp_apply wp_mapInsert $$ [$Hvmap] as Hvmap
      have hV' : wroteAtVs V gr rv = <[gr := rv]> V := by simp [wroteAtVs, hw, hv]
      imod withdraw_commit γ T V $$ [$Hinv $Hexcl $Hlc2 $Hrec $Htok $Hg] with ⟨Hg, HT⟩
      rw [hV']
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hvmap Hg]
      · iunfold recLockInv; iexists _; iframe
      iapply HΦ $$ HT
  | some old =>
    have hwo : wellFormed old = true := HVwf gr old hv
    simp only [Option.isSome_some, decide_true, Bool.not_true]
    wp_auto
    wp_apply wp_map_lookup1 $$ [$Hvmap] as Hvmap
    rw [hv]
    simp only [Option.getD_some]
    wp_apply wp_Compare
    cases hw : wellFormed rv
    · -- `rv` malformed: an error, nothing changes
      simp only [compareRV, hw, hwo, Bool.false_eq_true, ↓reduceIte]
      wp_auto
      have hV' : wroteAtVs V gr rv = V := by simp [wroteAtVs, hw]
      imod withdraw_commit γ T V $$ [$Hinv $Hexcl $Hlc2 $Hrec $Htok $Hg] with ⟨Hg, HT⟩
      rw [hV']
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hvmap Hg]
      · iunfold recLockInv; iexists V; iframe
      iapply HΦ $$ HT
    · simp only [compareRV, hw, hwo, ↓reduceIte]
      by_cases hlt : decVal old < decVal rv
      · -- newer: written
        simp only [cmpNat, hlt, ↓reduceIte]
        wp_auto
        wp_apply wp_mapInsert $$ [$Hvmap] as Hvmap
        have hV' : wroteAtVs V gr rv = <[gr := rv]> V := by simp [wroteAtVs, hw, hv, hlt]
        imod withdraw_commit γ T V $$ [$Hinv $Hexcl $Hlc2 $Hrec $Htok $Hg] with ⟨Hg, HT⟩
        rw [hV']
        wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hvmap Hg]
        · iunfold recLockInv; iexists _; iframe
        iapply HΦ $$ HT
      · -- not newer: nothing changes
        have hV' : wroteAtVs V gr rv = V := by simp [wroteAtVs, hw, hv, hlt]
        by_cases heq : decVal old = decVal rv
        · simp only [cmpNat, hlt, heq, ↓reduceIte, Nat.lt_irrefl]
          wp_auto
          imod withdraw_commit γ T V $$ [$Hinv $Hexcl $Hlc2 $Hrec $Htok $Hg] with ⟨Hg, HT⟩
          rw [hV']
          wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hvmap Hg]
          · iunfold recLockInv; iexists V; iframe
          iapply HΦ $$ HT
        · simp only [cmpNat, hlt, heq, ↓reduceIte, Nat.lt_irrefl]
          wp_auto
          imod withdraw_commit γ T V $$ [$Hinv $Hexcl $Hlc2 $Hrec $Htok $Hg] with ⟨Hg, HT⟩
          rw [hV']
          wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hvmap Hg]
          · iunfold recLockInv; iexists V; iframe
          iapply HΦ $$ HT

end proof

end consistency
end EtcdGrove
end Perennial
