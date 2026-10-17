/-
Proof of `Spec/go_etcd_io/etcd/server/v3/auth/tokenSimple__disable.lean` (pr-verify etcd#22560, 2026-10-16).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.tokenSimple__disable
public import Spec.go_etcd_io.etcd.server.v3.auth.simpleTokenTTLKeeper__stop

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

theorem auth.tokenSimple.disable.wp_proof
    (h_stop : auth.simpleTokenTTLKeeper.stop.spec (GF := GF) (hG := hG)) :
    auth.tokenSimple.disable.spec (GF := GF) (hG := hG) := fun t γ γk A kp => by
  wp_start as ⟨#Hts, Hadm⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave Hai : (authInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hai with ⟨-, -, -, -, -, -, -, -, ⟨%g, #Hgv, #Hset⟩⟩
  iunfold isTS at Hts
  icases Hts with ⟨%Htnn, -, #Hmu⟩
  iunfold tsAdmin at Hadm
  icases Hadm with ⟨Hkp1, HA1⟩
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HP⟩
  iunfold stLockP at HP
  icases HP with ⟨%kp', %A', %K, %ttl, Hkp, HA, Htab, Httl, HK, #HKe, HKm, Hcur⟩
  iunfold stTables at Htab
  icases Htab with ⟨%sp, %live, Hsp, Hspm, %Hsub⟩
  icombine Hkp1 Hkp gives %Heq
  subst Heq
  ihave Hkpf := (ts_ptsto_halves _ _).2 $$ [Hkp1 Hkp]
  · iframe Hkp1 Hkp
  ihave #Hro : iprop(⌜kp = null⌝ ∨ keeperRO (GF := GF) t kp) $$ [Hcur]
  · icases Hcur with (%H | ⟨-, #H⟩)
    · ileft; ipureintro; exact H
    · iright; iexact H
  wp_auto
  wp_apply wp_map_make1 (K := GoString) (V := GoString) as %sp' Hspm'
  icases (ts_ptsto_halves _ _).1 $$ Hkpf with ⟨Hkp1, Hkp⟩
  ihave %HAeq := ghostVar_agree γ A _ A' _ $$ HA1 HA
  subst HAeq
  imod ghostVar_update_halves (∅ : GMap GoString GoString) γ A A $$ HA1 HA with ⟨HA1, HA⟩
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hkp HA Httl HK HKm Hsp Hspm']
  · inext
    iunfold stLockP
    iexists null, ∅, K, ttl
    iframe
    iframe HKe
    isplitl [Hsp Hspm']
    · iunfold stTables
      iexists sp', ∅
      iframe
      ipureintro; exact subseteq_empty _
    · ileft; ipureintro; rfl
  -- `if tk != nil { tk.stop() }`, then the PR's `simpleTokenGauge.Set(0)` (without the lock)
  wp_if_destruct
  · wp_apply Hset
    iapply HΦ
    iunfold tsAdmin
    iframe
  · icases Hro with (%H | #Hro)
    · simp_all
    wp_apply (h_stop t kp) $$ [$Hro]
    wp_apply Hset
    iapply HΦ
    iunfold tsAdmin
    iframe

end proof

end EtcdGrove
end Perennial
