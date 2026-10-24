/-
Proof of the spec of the same name (the auth plan's S4, 2026-10-24). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__Recover
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__refreshRangePermCache
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__setRevision
public import Proof.go_etcd_io.etcd.server.v3.auth.VerdictLemmas
public import Spec.go_uber_org.zap.String
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth auth go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.authStore.Recover.wp_proof
    (h_refresh : auth.authStore.refreshRangePermCache.spec (GF := GF) (hG := hG))
    (h_setRevision : auth.authStore.setRevision.spec (GF := GF) (hG := hG)) :
    auth.authStore.Recover.spec (GF := GF) (hG := hG) := by
  intro st R M P f T hs be
  wp_start as ⟨#Hinv, Hown, HWR, HR, %Hbenn, #Hbeok, #Hwbeok, #Hfit⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hinv' := Hinv
  iunfold authInv at Hinv'
  icases Hinv' with ⟨%Hst, -, -, #HbeGuard, ⟨%tp, #Htp, #Htpok⟩, #Hguard, -⟩
  iunfold tokenProviderOk at Htpok
  icases Htpok with ⟨%tpi, %Htpi, -, #HEnable, -, -⟩
  subst Htpi
  iunfold authWR at HWR
  icases HWR with ⟨⟨%be0, Hbe, -⟩, HT, Hen⟩
  iunfold enabledHalf at Hen
  icases Hen with ⟨%en, Hen, -⟩
  ihave #Hbeok' := Hbeok
  iunfold authBackendOk at Hbeok'
  icases Hbeok' with ⟨%bi, %Hbi, #HRT⟩
  subst Hbi
  (try wp_auto)
  -- replace the backend under `beMu`'s write lock
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$HbeGuard] as ⟨Hlk, HP⟩
  iunfold beP at HP
  icases HP with ⟨%be1, Hbe', -⟩
  icombine Hbe Hbe' gives %Heq
  subst Heq
  ihave Hbe := (typedPointsto_half_split _ _ (1 : Qp)).2 $$ [Hbe Hbe']
  · iframe
  (try wp_auto)
  ihave ⟨Hbe, Hbe'⟩ := (typedPointsto_half_split _ _ (1 : Qp)).1 $$ Hbe
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk Hbe']
  · inext; iunfold beP; iexists (GoInterface.ok bi); iframe Hbe'; iexact Hbeok
  (try wp_auto)
  wp_apply HRT as %tx Htx
  iunfold authReadTxOk at Htx
  icases Htx with ⟨%ti, %Hti, %Hs, #HRL, #Hreads⟩
  subst Hti
  iunfold authTxReads at Hreads
  icases Hreads with ⟨#Hrd, #HRU⟩
  ihave #Hrd' := Hrd
  iunfold authReaderOk at Hrd'
  icases Hrd' with ⟨-, -, #HRE, #HRR, -⟩
  (try wp_auto)
  wp_bind (App (Val #(methods ti.ty go!"RLock" ti.v)) (Val #()))
  iapply HRL $$ HR
  inext
  iintro ⟨%sta, Htok, #Hsnap⟩
  ihave %Hfit' := Hfit $$ %sta Hsnap
  (try wp_auto)
  wp_bind (App (Val #(methods ti.ty go!"UnsafeReadAuthEnabled" ti.v)) (Val #()))
  iapply HRE $$ %sta Htok
  inext
  iintro %enb ⟨Htok, %Henb⟩
  (try wp_auto)
  wp_bind (App (Val #(methods ti.ty go!"UnsafeReadAuthRevision" ti.v)) (Val #()))
  iapply HRR $$ %sta Htok
  inext
  iintro %rv ⟨Htok, %Hrv⟩
  (try wp_auto)
  -- the state read is the latest
  ihave %Hpks : ⌜(M.isOn = true → M ≠ .any → permKeysOk sta) ∧ (M = .off → sta.enabled = false)⌝ $$ [Hsnap]
  · cases M with
    | on γa =>
      simp only [authSnap]
      icases Hsnap with ⟨%i, #Hst⟩
      ihave %Hk := authStateAt_permKeysOk γa i sta $$ Hst
      ipureintro; exact ⟨fun _ _ => Hk, fun h => nomatch h⟩
    | off =>
      simp only [authSnap]; icases Hsnap with %H; ipureintro
      first | exact ⟨fun h _ => nomatch h, fun _ => H⟩ | exact H | simp [H]
    | any =>
      ipureintro
      first | exact ⟨fun _ h => absurd rfl h, fun h => nomatch h⟩ | simp
  have Hlast : histLast M (hs ++ [sta]) sta := by
    cases M with
    | on γa => simp [histLast]
    | off => exact Hpks.2 rfl
    | any => trivial
  wp_apply (h_setRevision st R M rv hs [sta] sta) $$ [$Hinv $Hown] as Hown
  · ipureintro
    refine ⟨Hlast, Hrv, by simp, ?_⟩
    intro x hx; rw [List.mem_singleton] at hx; subst hx; exact Hpks
  (try wp_auto)
  wp_bind (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"refreshRangePermCache"))
    (Val #(GoInterface.ok ti)))
  iapply (h_refresh st R M ti Hs sta) $$ [Htok]
  · iframe Hpkg Hinv Hrd Htok Hsnap
    ipureintro; exact Hfit'
  inext
  iintro Htok
  (try wp_auto)
  wp_bind (App (Val #(methods ti.ty go!"RUnlock" ti.v)) (Val #()))
  iapply HRU $$ %sta Htok
  inext
  iintro HR
  (try wp_auto)
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hguard] as ⟨Hlk, HP⟩
  iunfold enabledP at HP
  icases HP with ⟨%en', Hen', -⟩
  icombine Hen Hen' gives %Heq
  subst Heq
  ihave Hen := (typedPointsto_half_split _ _ (1 : Qp)).2 $$ [Hen Hen']
  · iframe
  (try wp_auto)
  ihave #Hev : enabledVerdict M enb $$ []
  · rw [Henb]; iapply enabledVerdict_of_snap M sta $$ Hsnap
  wp_join with [Hen «as»]
  · (try wp_auto)
    wp_bind (App (Val #(methods tpi.ty go!"enable" tpi.v)) (Val #()))
    iapply HEnable $$ [] [-]
    · itrivial
    inext
    iintro -
    (try wp_auto)
    wp_join_done
  ihave ⟨Hen, Hen'⟩ := (typedPointsto_half_split _ _ (1 : Qp)).1 $$ Hen
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk Hen']
  · inext; iunfold enabledP; iexists enb; iframe Hen'; iexact Hev
  (try wp_auto)
  iapply HΦ
  iframe HR
  isplitl [Hbe HT Hen]
  · iunfold authWR; iframe HT; isplitl [Hbe]
    · iexists (GoInterface.ok bi); iframe Hbe Hwbeok
    · iunfold enabledHalf; iexists enb; iframe Hen Hev
  iexists sta
  iframe Hsnap Hown

end proof

end EtcdGrove
end Perennial
