/-
Proof of `Spec/go_etcd_io/etcd/server/v3/auth/tokenSimple__assignSimpleTokenToUser.lean` (pr-verify etcd#22560, 2026-10-16).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.tokenSimple__assignSimpleTokenToUser
public import Spec.go_etcd_io.etcd.server.v3.auth.simpleTokenTTLKeeper__addSimpleToken

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth auth

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.tokenSimple.assignSimpleTokenToUser.wp_proof
    (h_add : auth.simpleTokenTTLKeeper.addSimpleToken.spec (GF := GF) (hG := hG)) :
    auth.tokenSimple.assignSimpleTokenToUser.spec (GF := GF) (hG := hG) := fun t γ γk A kp u tk => by
  wp_start as ⟨#Hts, Hadm, %HAtk⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold isTS at Hts
  icases Hts with ⟨%Htnn, -, #Hmu⟩
  iunfold tsAdmin at Hadm
  icases Hadm with ⟨Hkp1, HA1⟩
  wp_apply wp_with_defer as %defer defer
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HP⟩
  iunfold stLockP at HP
  icases HP with ⟨%kp', %A', %K, %ttl, Hkp, HA, Htab, Httl, HK, #HKe, HKm, Hcur⟩
  iunfold stTables at Htab
  icases Htab with ⟨%sp, %ep, %live, %exp, Hsp, Hspm, Hep, Hepm, %Hsub⟩
  icombine Hkp1 Hkp gives %Heq
  subst Heq
  ihave %HAeq := ghostVar_agree γ A _ A' _ $$ HA1 HA
  subst HAeq
  wp_if_destruct
  · wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hkp HA Httl HK HKm Hcur Hsp Hspm Hep Hepm]
    · inext
      iunfold stLockP
      iexists null, A, K, ttl
      iframe
      iframe HKe
      isplitl [Hsp Hspm Hep Hepm]
      · iunfold stTables
        iexists sp, ep, live, exp
        iframe
        ipureintro; exact Hsub
      · ileft; ipureintro; rfl
    iapply HΦ
    iunfold tsAdmin
    iframe
  icases Hcur with (%Hnull | ⟨%HKkp, #Hro⟩)
  · exact absurd Hnull Hif
  ihave #Hro' := Hro
  iunfold keeperRO at Hro'
  icases Hro' with ⟨-, -, -, ⟨%d, #Hd⟩, -, -⟩
  icases (BigSepM.bigSepM_lookup_acc (Φ := fun k (_ : Unit) => keeperMap (GF := GF) k) HKkp).1
    $$ HKm with ⟨Hkm, HKback⟩
  have Hlive : live !! tk = none := by
    cases h : live !! tk with
    | none => rfl
    | some v => rw [Hsub.1 tk v h] at HAtk; cases HAtk
  wp_apply wp_map_lookup2 $$ [$Hspm] as Hspm
  rw [Hlive]
  wp_auto
  ihave %Hepnn := ownMap_not_nil _ _ _ $$ Hepm
  rw [decide_eq_false Hepnn]
  wp_auto
  wp_apply wp_mapDelete $$ [$Hepm] as Hepm
  wp_apply wp_mapInsert $$ [$Hspm] as Hspm
  wp_apply (h_add kp d tk) $$ [$Hkm $Hd] as Hkm
  ihave HKm := HKback $$ Hkm
  imod ghostVar_update_halves (GMap.insert tk u A) γ A A $$ HA1 HA with ⟨HA1, HA⟩
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hkp HA Httl HK HKm Hsp Hspm Hep Hepm]
  · inext
    iunfold stLockP
    iexists kp, (GMap.insert tk u A), K, ttl
    iframe
    iframe HKe
    isplitl [Hsp Hspm Hep Hepm]
    · iunfold stTables
      iexists sp, ep, (GMap.insert tk u live), (GMap.delete tk exp)
      iframe
      ipureintro
      exact ⟨subseteq_insert_insert tk u Hsub.1, subseteq_delete_insert tk u Hsub.2⟩
    · iright; iframe #; ipureintro; exact HKkp
  iapply HΦ
  iunfold tsAdmin
  rw [if_neg Hif]
  iframe

end proof

end EtcdGrove
end Perennial
