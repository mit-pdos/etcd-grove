/-
Proof of the spec of the same name (the auth plan's E2j, 2026-10-26). Lean-first (no Rocq
counterpart). The closure reads the user and the revision under the locked read transaction (its
`defer` the `RUnlock`); bcrypt's comparison runs after it, on the message's read-only hash.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__CheckPassword
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__IsAuthEnabled
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__lockedReadTx
public import Spec.golang_org.x.crypto.bcrypt.CompareHashAndPassword
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Logger__Info
public import Proof.go_etcd_io.etcd.server.v3.auth.AdminLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth auth go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.authStore.CheckPassword.wp_proof
    (h_IsAuthEnabled : auth.authStore.IsAuthEnabled.spec (GF := GF) (hG := hG))
    (h_lockedReadTx : auth.authStore.lockedReadTx.spec (GF := GF) (hG := hG))
    (h_Compare : bcrypt.CompareHashAndPassword.spec (GF := GF) (hG := hG))
    (h_String : zap.String.spec (GF := GF) (hG := hG))
    (h_Info : zap.Logger.Info.spec (GF := GF) (hG := hG)) :
    auth.authStore.CheckPassword.spec (GF := GF) (hG := hG) := by
  intro st R M username password
  wp_start as ⟨#Hinv, Hen, Hbr, HR⟩
  icases authErrVar_of_init .authNotEnabled $$ Hpkg with ⟨%eNE, #HeNE⟩
  icases authErrVar_of_init .authFailed $$ Hpkg with ⟨%eAF, #HeAF⟩
  icases authErrVar_of_init .noPasswordUser $$ Hpkg with ⟨%eNP, #HeNP⟩
  simp only [AuthErr.var]
  ihave #Hbc : isPkgInit (PROP := IProp GF) pkg_id.golang_org.x.crypto.bcrypt $$ []
  · iPkgInit
  ihave #Hinv' := Hinv
  iunfold authInv at Hinv'
  icases Hinv' with ⟨%Hst, -, ⟨%lg, #Hlg, %Hlgnn⟩, -, -, -, -⟩
  (try wp_auto)
  wp_apply (h_IsAuthEnabled st R M) $$ [$Hinv $Hen] as %en ⟨Hen, #Hev⟩
  cases en
  · (try wp_auto)
    iapply HΦ
    iframe Hen Hbr HR
    iunfold passwordChecked
    ileft; ipureintro; simp
  (try wp_auto)
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply (h_lockedReadTx st R M) $$ [$Hinv $Hbr $HR] as %tx ⟨Hbr, Htx⟩
  iunfold authReadTxLocked at Htx
  icases Htx with ⟨%ti, %Hti, Htx⟩
  subst Hti
  icases Htx with ⟨%sta, %Hs, Htok, #Hsnap, #Hreads⟩
  iunfold authTxReads at Hreads
  icases Hreads with ⟨#Hrds, #HRU⟩
  iunfold authReaderOk at Hrds
  icases Hrds with ⟨#HUG, -, -, #HRev, -⟩
  (try wp_auto)
  wp_bind (App (Val #(methods ti.ty go!"UnsafeGetUser" ti.v)) (Val #username))
  iapply HUG $$ Htok
  inext
  iintro %u ⟨Htok, Hu⟩
  (try wp_auto)
  wp_if_destruct
  · -- no such user
    (try wp_auto)
    wp_bind (App (Val #(methods ti.ty go!"RUnlock" ti.v)) (Val #()))
    iapply HRU $$ Htok
    inext
    iintro HR
    (try wp_auto)
    iapply HΦ
    iframe Hen Hbr HR
    iunfold passwordChecked
    ileft; ipureintro; simp
  ihave Hu' := userOut_some u sta username Hif $$ Hu
  icases Hu' with ⟨%roles, %ur, %Hur, Hu⟩
  iunfold ownUser at Hu
  icases Hu with ⟨%s1, %n, %pw, %rl, %o, %uf, %sc, Hp, #Hn, #Hpw, #Hrl, #Ho⟩
  icases typedPointsto_split _ _ _ $$ Hp with Hp
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hp
  ipersist Password
  ipersist Options
  iunfold userOptsAt at Ho
  icases Ho with (%Ho | ⟨%Hon, %s2, %uf2, %sc2, #Hov⟩)
  · obtain ⟨Ho, -⟩ := Ho
    subst Ho
    (try wp_auto)
    wp_bind (App (Val #(methods ti.ty go!"UnsafeReadAuthRevision" ti.v)) (Val #()))
    iapply HRev $$ %sta Htok
    inext
    iintro %rev ⟨Htok, %Hrev⟩
    (try wp_auto)
    wp_bind (App (Val #(methods ti.ty go!"RUnlock" ti.v)) (Val #()))
    iapply HRU $$ Htok
    inext
    iintro HR
    (try wp_auto)
    wp_apply wp_string_to_bytes password as %psl ⟨Hpsl, -⟩
    wp_apply (h_Compare pw psl ur.password password DFrac.discard (DFrac.own 1))
      $$ [$Hbc $Hpw $Hpsl] as %cerr ⟨-, -⟩
    (try wp_auto)
    cases cerr with
    | ok ei =>
      -- a wrong password
      (try wp_auto)
      wp_apply h_String _ _ as %f1 -
      (try wp_auto)
      wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1]
      isplitr
      · ipureintro; rfl
      iintro %fsl ⟨-, -⟩
      (try wp_auto)
      wp_apply h_Info
      · ipureintro; exact Hlgnn
      (try wp_auto)
      iapply HΦ
      iframe Hen Hbr HR
      iunfold passwordChecked
      ileft; ipureintro; simp
    | nil =>
      (try wp_auto)
      iapply HΦ
      iframe Hen Hbr HR
      iunfold passwordChecked
      iright
      isplitr
      · ipureintro; rfl
      iframe Hev
      iexists sta
      iframe Hsnap
      ipureintro
      exact ⟨Hrev, by simp [Hur.1]⟩
  · (try wp_auto)
    have hd : decide (o = null) = false := decide_eq_false Hon
    rw [hd]
    (try wp_auto)
    (try simp only)
    icases typedPointsto_split _ _ _ $$ Hov with Hov
    simp only [TypedPointsto.typedPointstoDef]
    iNamed Hov
    (try wp_auto)
    cases hnp : ur.noPassword
    rotate_left
    · -- a no-password user
      (try wp_auto)
      wp_bind (App (Val #(methods ti.ty go!"RUnlock" ti.v)) (Val #()))
      iapply HRU $$ Htok
      inext
      iintro HR
      (try wp_auto)
      iapply HΦ
      iframe Hen Hbr HR
      iunfold passwordChecked
      ileft; ipureintro; simp
    (try wp_auto)
    wp_bind (App (Val #(methods ti.ty go!"UnsafeReadAuthRevision" ti.v)) (Val #()))
    iapply HRev $$ %sta Htok
    inext
    iintro %rev ⟨Htok, %Hrev⟩
    (try wp_auto)
    wp_bind (App (Val #(methods ti.ty go!"RUnlock" ti.v)) (Val #()))
    iapply HRU $$ Htok
    inext
    iintro HR
    (try wp_auto)
    wp_apply wp_string_to_bytes password as %psl ⟨Hpsl, -⟩
    wp_apply (h_Compare pw psl ur.password password DFrac.discard (DFrac.own 1))
      $$ [$Hbc $Hpw $Hpsl] as %cerr ⟨-, -⟩
    (try wp_auto)
    cases cerr with
    | ok ei =>
      -- a wrong password
      (try wp_auto)
      wp_apply h_String _ _ as %f1 -
      (try wp_auto)
      wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1]
      isplitr
      · ipureintro; rfl
      iintro %fsl ⟨-, -⟩
      (try wp_auto)
      wp_apply h_Info
      · ipureintro; exact Hlgnn
      (try wp_auto)
      iapply HΦ
      iframe Hen Hbr HR
      iunfold passwordChecked
      ileft; ipureintro; simp
    | nil =>
      (try wp_auto)
      iapply HΦ
      iframe Hen Hbr HR
      iunfold passwordChecked
      iright
      isplitr
      · ipureintro; rfl
      iframe Hev
      iexists sta
      iframe Hsnap
      ipureintro
      exact ⟨Hrev, by simp [Hur.1]⟩

end proof

end EtcdGrove
end Perennial
