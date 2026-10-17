/-
Proof of `Spec/go_etcd_io/etcd/server/v3/auth/tokenSimple__enable.lean` (pr-verify etcd#22560, 2026-10-16).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.tokenSimple__enable
public import Spec.go_etcd_io.etcd.server.v3.auth.simpleTokenTTLKeeper__run
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Logger__Debug

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth auth

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.tokenSimple.enable.wp_proof
    (h_run : auth.simpleTokenTTLKeeper.run.spec (GF := GF) (hG := hG))
    (h_String : zap.String.spec (GF := GF) (hG := hG))
    (h_Debug : zap.Logger.Debug.spec (GF := GF) (hG := hG)) :
    auth.tokenSimple.enable.spec (GF := GF) (hG := hG) := fun t γ γk A kp => by
  wp_start as ⟨#Hts, Hadm⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave Hai : (authInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hai with ⟨-, -, -, -, -, -, -, ⟨%d0, #Hd0⟩, -⟩
  ihave #Hts' := Hts
  iunfold isTS at Hts'
  icases Hts' with ⟨%Htnn, ⟨%lg, #Hlg, %Hlgnn⟩, #Hmu⟩
  iunfold tsAdmin at Hadm
  icases Hadm with ⟨Hkp1, HA1⟩
  wp_apply wp_with_defer as %defer defer
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HP⟩
  iunfold stLockP at HP
  icases HP with ⟨%kp', %A', %K, %ttl, Hkp, HA, Htab, Httl, HK, #HKe, HKm, Hcur⟩
  icombine Hkp1 Hkp gives %Heq
  subst Heq
  ipersist t
  wp_if_destruct
  · wp_join iprop(∃ ttl' : time.Duration, tF go!"simpleTokenTTL" t ↦ ttl') with [Httl]
      as ⟨%ttl', Httl⟩
    wp_apply wp_map_make1 (K := GoString) (V := time.Time) as %km Hkmm
    wp_apply (chan.wp_make1 (V := Unit)) as %c1 %γ1 ⟨#Hc1, %Hcap1, Hown1⟩
    wp_apply (chan.wp_make1 (V := Unit)) as %c2 %γ2 ⟨#Hc2, %Hcap2, Hown2⟩
    ihave %Hknn := typedPointsto_not_null _ _ _ $$ «$r0»
    iStructNamed «$r0»
    ipersist donec
    ipersist stopc
    ipersist deleteTokenFunc
    ipersist mu
    ipersist simpleTokenTTL
    ipersist lg
    ipersist tokens
    ihave #Hro : keeperRO (GF := GF) t «$r0_ptr» $$ []
    · iunfold keeperRO
      isplitr
      · ipureintro; exact Hknn
      iframe mu
      isplitr
      · iexists _
        isplitr
        · iexact deleteTokenFunc
        iunfold delfOk
        imodintro
        iintro %A0 %tk
        wp_start as Htab
        iunfold stTables at Htab
        icases Htab with ⟨%sp, %live, Hsp, Hspm, %Hsub⟩
        wp_auto
        wp_apply wp_map_lookup2 $$ [$Hspm] as Hspm
        cases hL : live !! tk with
        | none =>
          wp_auto
          iapply HΦ
          iunfold stTables
          iexists sp, live
          iframe
          ipureintro; exact Hsub
        | some u =>
          simp only [Option.isSome_some, _root_.decide_true, Option.getD_some]
          wp_auto
          wp_apply h_String as %f1 -
          (try wp_auto)
          wp_apply h_String as %f2 -
          (try wp_auto)
          wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1, f2]
          isplitr
          · ipureintro; rfl
          iintro %fsl ⟨-, -⟩
          (try wp_auto)
          wp_apply h_Debug
          · ipureintro; exact Hlgnn
          (try wp_auto)
          wp_apply wp_mapDelete $$ [$Hspm] as Hspm
          iapply HΦ
          iunfold stTables
          iexists sp, (GMap.delete tk live)
          iframe
          ipureintro; exact subseteq_delete tk Hsub
      isplitr
      · iexists _; iexact simpleTokenTTL
      isplitr
      · iexists _; iexact lg
      isplitr
      · iexists _, _; iframe donec Hc1
      · iexists _, _; iframe stopc Hc2
    ihave Hkpf := (ts_ptsto_halves _ _).2 $$ [Hkp1 Hkp]
    · iframe Hkp1 Hkp
    wp_auto
    icases (ts_ptsto_halves _ _).1 $$ Hkpf with ⟨Hkp1, Hkp⟩
    -- the new keeper joins the keepers
    ihave Hkm_new : keeperMap (GF := GF) «$r0_ptr» $$ [Hkmm]
    · iunfold keeperMap; iexists _, _; iframe Hkmm tokens
    imod keepers_join γk K «$r0_ptr» $$ HK HKe HKm Hkm_new with ⟨%K', HK, #HKe', HKm, %HK', #Hel⟩
    wp_apply wp_fork $$ [Hown1 Hown2]
    · wp_apply (h_run t γ γk «$r0_ptr») $$ [Hown1 Hown2]
      · iframe Hts Hro Hel
        iunfold keeperChans
        isplitl [Hown1]
        · iexists c1, γ1; iframe donec Hc1 Hown1
        · iexists c2, γ2; iframe stopc Hc2 Hown2
      ipureintro; exact isPanic_intoVal _
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hkp HA Htab Httl HK HKm]
    · inext
      iunfold stLockP
      iexists «$r0_ptr», A', K', ttl'
      iframe
      iframe HKe'
      iright
      iframe Hro
      ipureintro; exact HK'
    iapply HΦ
    iunfold tsAdmin
    iframe
    ipureintro; exact ⟨Hknn, fun h => absurd rfl h⟩
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hkp HA Htab Httl HK HKm Hcur]
  · inext
    iunfold stLockP
    iexists kp, A', K, ttl
    iframe
    iframe HKe
  iapply HΦ
  iunfold tsAdmin
  iframe
  ipureintro; exact ⟨Hif, fun _ => rfl⟩

end proof

end EtcdGrove
end Perennial
