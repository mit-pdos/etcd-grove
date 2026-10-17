/-
Proof of `Spec/go_etcd_io/etcd/server/v3/auth/tokenSimple__renew.lean` (pr-verify etcd#22560, 2026-10-16).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.tokenSimple__renew
public import Spec.go_etcd_io.etcd.server.v3.auth.simpleTokenTTLKeeper__addSimpleToken
public import Spec.go_etcd_io.etcd.server.v3.auth.simpleTokenTTLKeeper__resetSimpleToken

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

theorem auth.tokenSimple.renew.wp_proof
    (h_add : auth.simpleTokenTTLKeeper.addSimpleToken.spec (GF := GF) (hG := hG))
    (h_reset : auth.simpleTokenTTLKeeper.resetSimpleToken.spec (GF := GF) (hG := hG)) :
    auth.tokenSimple.renew.spec (GF := GF) (hG := hG) := fun t γ γk ctx tk rev => by
  wp_start as #Hts
  ihave Hai : (authInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hai with ⟨-, -, -, -, #HeIT, -, -, #HAF, -⟩
  iunfold authErrVar at HeIT HAF
  icases HeIT with ⟨%eIT, #HeIT, -⟩
  icases HAF with ⟨%eAF, #HAF, -⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold isTS at Hts
  icases Hts with ⟨%Htnn, -, #Hmu⟩
  wp_apply wp_with_defer as %defer defer
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HP⟩
  iunfold stLockP at HP
  icases HP with ⟨%kp, %A, %K, %ttl, Hkp, HA, Htab, Httl, HK, #HKe, HKm, Hcur⟩
  iunfold stTables at Htab
  icases Htab with ⟨%sp, %ep, %live, %exp, Hsp, Hspm, Hep, Hepm, %Hsub⟩
  wp_auto
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
    iright
    isplitr
    · ipureintro; rfl
    ileft
    iunfold errVarIs
    iexists eAF
    iframe #
    ipureintro; rfl
  icases Hcur with (%Hnull | ⟨%HKkp, #Hro⟩)
  · exact absurd Hnull Hif
  ihave #Hro' := Hro
  iunfold keeperRO at Hro'
  icases Hro' with ⟨-, -, -, ⟨%d, #Hd⟩, -, -⟩
  icases (BigSepM.bigSepM_lookup_acc (Φ := fun k (_ : Unit) => keeperMap (GF := GF) k) HKkp).1
    $$ HKm with ⟨Hkm, HKback⟩
  wp_apply wp_map_lookup2 $$ [$Hspm] as Hspm
  wp_if_destruct
  · wp_apply (h_reset kp d tk) $$ [$Hkm $Hd] as Hkm
    ihave HKm := HKback $$ Hkm
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hkp HA Httl HK HKm Hsp Hspm Hep Hepm]
    · inext
      iunfold stLockP
      iexists kp, A, K, ttl
      iframe
      iframe HKe
      isplitl [Hsp Hspm Hep Hepm]
      · iunfold stTables
        iexists sp, ep, live, exp
        iframe
        ipureintro; exact Hsub
      · iright; iframe #; ipureintro; exact HKkp
    iapply HΦ
    ileft; ipureintro; exact ⟨rfl, rfl⟩
  wp_apply wp_map_lookup2 $$ [$Hepm] as Hepm
  wp_if_destruct
  · cases hE : exp !! tk with
    | none => simp [hE] at Hif
    | some u =>
      simp only [Option.getD_some]
      wp_apply wp_mapDelete $$ [$Hepm] as Hepm
      wp_apply wp_mapInsert $$ [$Hspm] as Hspm
      wp_apply (h_add kp d tk) $$ [$Hkm $Hd] as Hkm
      ihave HKm := HKback $$ Hkm
      have hA : A !! tk = some u := Hsub.2 tk u hE
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hkp HA Httl HK HKm Hsp Hspm Hep Hepm]
      · inext
        iunfold stLockP
        iexists kp, A, K, ttl
        iframe
        iframe HKe
        isplitl [Hsp Hspm Hep Hepm]
        · iunfold stTables
          iexists sp, ep, (GMap.insert tk u live), (GMap.delete tk exp)
          iframe
          ipureintro
          exact ⟨by rw [← GMap.insert_id A tk u hA]; exact subseteq_insert_insert tk u Hsub.1,
            subseteq_delete tk Hsub.2⟩
        · iright; iframe #; ipureintro; exact HKkp
      iapply HΦ
      ileft; ipureintro; exact ⟨rfl, rfl⟩
  ihave HKm := HKback $$ Hkm
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hkp HA Httl HK HKm Hsp Hspm Hep Hepm]
  · inext
    iunfold stLockP
    iexists kp, A, K, ttl
    iframe
    iframe HKe
    isplitl [Hsp Hspm Hep Hepm]
    · iunfold stTables
      iexists sp, ep, live, exp
      iframe
      ipureintro; exact Hsub
    · iright; iframe #; ipureintro; exact HKkp
  iapply HΦ
  iright
  isplitr
  · ipureintro; rfl
  iright
  iunfold errVarIs
  iexists eIT
  iframe #
  ipureintro; rfl

end proof

end EtcdGrove
end Perennial
