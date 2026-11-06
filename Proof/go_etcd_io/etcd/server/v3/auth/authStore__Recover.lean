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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.authStore.Recover.wp_proof
    (h_refresh : auth.authStore.refreshRangePermCache.spec (GF := GF) (hG := hG))
    (h_setRevision : auth.authStore.setRevision.spec (GF := GF) (hG := hG)) :
    auth.authStore.Recover.spec (GF := GF) (hG := hG) := by
  intro st R M hs N stI be γc₀ γc
  wp_start as ⟨#Hinv, Hown, ⟨%be0, Hbe⟩, Hen, Hca, Htpa, HR, %Hbenn, #Hbeok, Hin, Hfit⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hinv' := Hinv
  iunfold authInv at Hinv'
  icases Hinv' with ⟨%Hst, -, -, #HbeGuard, ⟨%tp0, -, -⟩, #Hguard, -⟩
  iunfold tpAdmin at Htpa
  icases Htpa with ⟨%tp, %Atp, #Htp, #HtpokA, HA⟩
  ihave #Htpok := HtpokA
  iunfold tokenProviderOkA at Htpok
  icases Htpok with ⟨%tpi, %Htpi, -, #HEnable, -, -, -, -⟩
  subst Htpi
  iunfold enabledHalf at Hen
  icases Hen with ⟨%en, Hen, -⟩
  iunfold flagAt at Hen
  icases Hen with ⟨Hen, HenQ⟩
  ihave #Hbeok' := Hbeok
  iunfold authBackendOk at Hbeok'
  icases Hbeok' with ⟨%bi, %Hbi, #HRT⟩
  subst Hbi
  (try wp_auto)
  -- replace the backend under `beMu`'s write lock (in `on γa`, its names with it)
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$HbeGuard] as ⟨Hlk, HP⟩
  iunfold beP at HP
  icases HP with ⟨%be1, %γ1, Hbe', -, Hcu1⟩
  icombine Hbe Hbe' gives %Heq
  subst Heq
  imod (recover_swap M γc₀ γc γ1) $$ Hin Hcu1 with ⟨Hcu, Hout⟩
  ihave Hbe := (typedPointsto_half_split _ _ (1 : Qp)).2 $$ [Hbe Hbe']
  · iframe
  (try wp_auto)
  ihave ⟨Hbe, Hbe'⟩ := (typedPointsto_half_split _ _ (1 : Qp)).1 $$ Hbe
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk Hbe' Hcu]
  · inext; iunfold beP; iexists (GoInterface.ok bi), γc; iframe Hbe' Hbeok Hcu
  (try wp_auto)
  wp_apply HRT as %tx Htx
  ihave Htx := authReadTxOk_recover _ R M γc $$ Htx
  icases Htx with ⟨%ti, %Hti, %Hs, #HRL, #Hreads⟩
  subst Hti
  iunfold authTxReads at Hreads
  icases Hreads with ⟨#Hrd, #HRU⟩
  ihave #Hrd' := Hrd
  iunfold authReaderOk at Hrd'
  icases Hrd' with ⟨-, -, #HRE, #HRR, -⟩
  (try wp_auto)
  wp_bind (App (Val #(methods ti.ty go!"RLock" ti.v)) (Val #()))
  iapply HRL $$ %hs %N %γc₀ [HR Hown Hout]
  · iframe HR Hown Hout
  inext
  iintro ⟨%sta, Htok, #Hsnap, Hown, Hout, %Hlast⟩
  ihave %Hfit' : ⌜permsFit sta⌝ $$ [Hfit]
  · cases M with
    | on γa =>
      simp only [recoverFit, histLast] at Hlast ⊢
      icases Hfit with %Hf
      ipureintro
      obtain ⟨h1, h2⟩ := Hf
      rw [Hlast] at h1
      cases h1
      exact h2
    | off =>
      simp only [recoverFit]
      icases Hfit with ⟨-, #Hf⟩
      iapply Hf $$ Hsnap
    | any =>
      simp only [recoverFit]
      icases Hfit with ⟨-, #Hf⟩
      iapply Hf $$ Hsnap
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
  -- the atomic at the state read, the latest (nothing appended)
  wp_apply (h_setRevision st R M rv hs N [] sta) $$ [$Hinv $Hown] as ⟨Hown, -⟩
  · simp only [List.isEmpty_nil, ↓reduceIte, List.append_nil]
    isplitr
    · itrivial
    isplitr
    · iintro !> %x %hx; simp at hx
    ipureintro
    refine ⟨Hlast, Hrv, ?_⟩
    simp
  simp only [List.append_nil]
  (try wp_auto)
  wp_bind (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"refreshRangePermCache"))
    (Val #(GoInterface.ok ti)))
  iapply (h_refresh st R M ti Hs sta (hs ++ N)) $$ [Htok Hca Hown]
  · iframe Hpkg Hinv Hca Hrd Htok Hsnap Hown
    ipureintro; exact ⟨Hfit', fun _ h => by subst h; exact Hlast⟩
  inext
  iintro ⟨Htok, Hca, Hown⟩
  (try wp_auto)
  wp_bind (App (Val #(methods ti.ty go!"RUnlock" ti.v)) (Val #()))
  iapply HRU $$ %sta Htok
  inext
  iintro HR
  (try wp_auto)
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hguard] as ⟨Hlk, HP⟩
  iunfold enabledP at HP
  icases HP with ⟨%en', Hen', -, Hg⟩
  icombine Hen Hen' gives %Heq
  subst Heq
  -- (E3h) the field's ghost variable set to the read state's flag (the latest)
  imod (enG_update st R M (hs ++ N) en enb (fun γa stl hM hl => by
    subst hM; simp only [histLast] at Hlast; rw [Hlast] at hl; cases hl; exact Henb))
    $$ Hinv Hown Hg HenQ with ⟨Hown, Hg, HenQ⟩
  ihave Hen := (typedPointsto_half_split _ _ (1 : Qp)).2 $$ [Hen Hen']
  · iframe
  (try wp_auto)
  ihave #Hev : enabledVerdict M enb $$ []
  · rw [Henb]; iapply enabledVerdict_of_snap M sta $$ Hsnap
  wp_join with [Hen «as» HA]
  · (try wp_auto)
    wp_bind (App (Val #(methods tpi.ty go!"enable" tpi.v)) (Val #()))
    iapply HEnable $$ [HA] [-]
    · iexact HA
    inext
    iintro HA
    (try wp_auto)
    wp_join_done
  ihave ⟨Hen, Hen'⟩ := (typedPointsto_half_split _ _ (1 : Qp)).1 $$ Hen
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk Hen' Hg]
  · inext; iunfold enabledP; iexists enb; iframe Hen' Hg; iexact Hev
  (try wp_auto)
  iapply HΦ
  isplitl [HA]
  · iunfold tpAdmin; iexists (GoInterface.ok tpi), Atp; iframe HA; iframe #
  simp only [authOwnT]
  iframe HR Hbe Hown Hout
  iunfold tieRes
  iexists enb, sta
  iframe Hev Hca Hsnap
  isplitl [Hen HenQ]
  · iunfold flagAt; iframe Hen HenQ
  ipureintro
  cases M with
  | on γa =>
    intro stl hl
    simp only [histLast] at Hlast
    rw [Hlast] at hl
    cases hl
    exact ⟨Henb, fun _ => rfl, rfl⟩
  | off => trivial
  | any => trivial

end proof

end EtcdGrove
end Perennial
