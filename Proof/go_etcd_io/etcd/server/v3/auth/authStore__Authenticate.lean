/-
Proof of the spec of the same name (the auth plan's S5, 2026-10-24). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__Authenticate
public import Proof.go_etcd_io.etcd.server.v3.auth.LatestTie
public import Proof.go_etcd_io.etcd.server.v3.auth.VerdictLemmas
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__IsAuthEnabled
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__Revision
public import Spec.go_etcd_io.etcd.server.v3.auth.redactToken
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Logger__Check
public import Spec.go_uber_org.zap.zapcore.CheckedEntry__Write

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

/-- **`Authenticate`, over the store's backend `be` and a frame `F`** (C1's A2, 2026-10-28): the
proof of `Authenticate.spec` and `Authenticate.specTB`, which differ in the write resource's halves
of the flag and the cache (`authWR`'s, `authWRxB`'s at their values): `Authenticate` reads neither
(`IsAuthEnabled` reads the flag under `enabledMu`'s read lock), so they are the frame `F`. Its error
is `nil` or one of the package's. -/
theorem auth.authStore.Authenticate.wp_core
    (h_IsAuthEnabled : auth.authStore.IsAuthEnabled.spec (GF := GF) (hG := hG))
    (h_Revision : auth.authStore.Revision.spec (GF := GF) (hG := hG))
    (h_redactToken : auth.redactToken.spec (GF := GF) (hG := hG))
    (h_String : zap.String.spec (GF := GF) (hG := hG))
    (h_Check : zap.Logger.Check.spec (GF := GF) (hG := hG))
    (h_Write : zapcore.CheckedEntry.Write.spec (GF := GF) (hG := hG))
    (st : Loc) (R : IProp GF) (M : AuthMode) (P : IProp GF) (f : val) (T F : IProp GF)
    (hs : List AuthState) (Pre Q Post : IProp GF) (ctx : GoInterface) (username password : GoString)
    (be : AuthBackend) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗
        enabledRd st M ∗ authOwn M hs ∗
        (aF go!"be" st ↦{DFrac.own (1 : Qp).half} be ∗ authWBackendOk be M P f T) ∗ T ∗ F ∗
        mvcc.csContract P f Pre Q Post ∗ authnCtx M ctx }}
      (App (App (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"Authenticate"))
        (Val #ctx)) (Val #username)) (Val #password))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); (Post ∨ Pre) ∗ enabledRd st M ∗
        authOwn M hs ∗ (aF go!"be" st ↦{DFrac.own (1 : Qp).half} be ∗ authWBackendOk be M P f T) ∗
        T ∗ F ∗ (⌜err = GoInterface.nil⌝ ∨ ∃ e : AuthErr, authErrOf e err) ∗
        authenticated M hs username resp err }} := by
  wp_start as ⟨#Hinv, Hen, Hown, ⟨Hbe, #Hbeok⟩, HT, HF, Hcs, Hctx⟩
  icases authErrVar_of_init .authNotEnabled $$ Hpkg with ⟨%eNE, #HeNE⟩
  icases authErrVar_of_init .authFailed $$ Hpkg with ⟨%eAF, #HeAF⟩
  ihave #HfNE := authErrOf_intro .authNotEnabled eNE $$ HeNE
  ihave #HfAF := authErrOf_intro .authFailed eAF $$ HeAF
  simp only [AuthErr.var]
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Hzapc : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap.zapcore $$ []
  · iPkgInit
  ihave #Hinv' := Hinv
  iunfold authInv at Hinv'
  icases Hinv' with ⟨%Hst, -, ⟨%lg, #Hlg, %Hlgnn⟩, -, ⟨%tp, #Htp, #Htpok⟩, -, -⟩
  iunfold tokenProviderOk at Htpok
  icases Htpok with ⟨%Atp, %tpi, %Htpi, -, -, -, -, #HAssign, -⟩
  subst Htpi
  ihave #Hbeok' := Hbeok
  iunfold authWBackendOk at Hbeok'
  icases Hbeok' with ⟨%bi, %Hbi, -, -, #HRds⟩
  iunfold authBackendReads at HRds
  icases HRds with ⟨#HGetUser, -, -, -⟩
  subst Hbi
  (try wp_auto)
  wp_apply (h_IsAuthEnabled st R M) $$ [$Hinv $Hen] as %en ⟨Hen, #Hev⟩
  cases en
  · -- auth disabled
    (try wp_auto)
    iapply HΦ
    isplitl [Hcs]
    · iapply csContract_noWrite $$ Hcs
    iframe Hen Hown
    iframe Hbe Hbeok HT HF
    isplitr
    · iright; iexists .authNotEnabled; iexact HfNE
    iunfold authenticated
    ileft; ipureintro; exact ⟨by simp, rfl⟩
  (try wp_auto)
  -- `GetUser` is the backend's read transaction: the hook does not run (`Pre` kept)
  ihave HPost := csContract_noWrite P f Pre Q Post $$ Hcs
  wp_bind (App (Val #(methods bi.ty go!"GetUser" bi.v)) (Val #username))
  iapply HGetUser $$ %hs %username [$HT $Hown]
  inext
  iintro %u ⟨HT, Hown, %sta, %Hl, Hu⟩
  (try wp_auto)
  wp_if_destruct
  · -- no such user
    ihave %Hnone := userOut_null sta username $$ Hu
    (try wp_auto)
    iapply HΦ
    isplitl [HPost]
    · iexact HPost
    iframe Hen Hown
    iframe Hbe Hbeok HT HF
    isplitr
    · iright; iexists .authFailed; iexact HfAF
    iunfold authenticated
    ileft; ipureintro; exact ⟨by simp, rfl⟩
  ihave Hu' := userOut_some u sta username Hif $$ Hu
  icases Hu' with ⟨%roles, %ur, %Hur, Hu⟩
  iunfold ownUser at Hu
  icases Hu with ⟨%s1, %n, %pw, %rl, %o, %uf, %sc, Hp, #Hn, #Hpw, #Hrl, #Ho⟩
  iunfold userOptsAt at Ho
  icases Ho with (%Ho | ⟨%Hon, %s2, %uf2, %sc2, #Hov⟩)
  · obtain ⟨Ho, -⟩ := Ho
    subst Ho
    (try wp_auto)
    (try wp_auto)
    wp_apply (h_Revision st R M (some hs)) $$ [$Hinv Hown] as %rev ⟨Hown, -, -⟩
    · iunfold authOwnOpt; iexact Hown
    iunfold authOwnOpt at Hown
    (try wp_auto)
    wp_bind (App (App (App (Val #(methods tpi.ty go!"assign" tpi.v)) (Val #ctx)) (Val #username)) (Val #rev))
    iapply HAssign $$ %ctx %username %rev [Hctx]
    · iexact Hctx
    inext
    iintro %tok %err Htok
    (try wp_auto)
    cases err with
    | ok ei =>
      icases Htok with (⟨%Hn, -⟩ | ⟨-, %e, #He⟩)
      · cases Hn
      (try wp_auto)
      iapply HΦ
      isplitl [HPost]
      · iexact HPost
      iframe Hen Hown
      iframe Hbe Hbeok HT HF
      isplitr
      · iright; iexists e; iexact He
      iunfold authenticated
      ileft; ipureintro; exact ⟨by simp, rfl⟩
    | nil =>
      icases Htok with (⟨-, #Htok⟩ | ⟨%Hne, -⟩)
      rotate_left
      · exact absurd rfl Hne
      (try wp_auto)
      (try wp_auto)
      wp_apply h_Check as %ce -
      · ipureintro; exact Hlgnn
      (try wp_auto)
      wp_if_destruct
      · -- no entry to write
        (try wp_auto)
        irename «$r0» => Hrl
        generalize «$r0_ptr» = rl at *
        (try wp_auto)
        iapply HΦ
        isplitl [HPost]
        · iexact HPost
        iframe Hen Hown
        iframe Hbe Hbeok HT HF
        isplitr
        · ileft; ipureintro; rfl
        iunfold authenticated
        iright
        isplitr
        · ipureintro; rfl
        iexists tok, _
        iframe Hrl
        isplitr
        · ipureintro; rfl
        iframe Htok Hev
        ipureintro; exact ⟨sta, Hl, by simp [Hur.1]⟩
      · wp_apply h_redactToken _ as %fp -
        (try wp_auto)
        wp_apply h_String _ _ as %f1 -
        (try wp_auto)
        wp_apply h_String _ _ as %f2 -
        (try wp_auto)
        wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1, f2]
        isplitr
        · ipureintro; rfl
        iintro %fsl ⟨-, -⟩
        (try wp_auto)
        wp_apply h_Write
        · ipureintro; exact Hif
        (try wp_auto)
        irename «$r0» => Hrl
        generalize «$r0_ptr» = rl at *
        (try wp_auto)
        iapply HΦ
        isplitl [HPost]
        · iexact HPost
        iframe Hen Hown
        iframe Hbe Hbeok HT HF
        isplitr
        · ileft; ipureintro; rfl
        iunfold authenticated
        iright
        isplitr
        · ipureintro; rfl
        iexists tok, _
        iframe Hrl
        isplitr
        · ipureintro; rfl
        iframe Htok Hev
        ipureintro; exact ⟨sta, Hl, by simp [Hur.1]⟩
  · (try wp_auto)
    have hd : decide (o = null) = false := decide_eq_false Hon
    rw [hd]
    (try wp_auto)
    simp only
    icases typedPointsto_split _ _ _ $$ Hov with Hov
    simp only [TypedPointsto.typedPointstoDef]
    iNamed Hov
    (try wp_auto)
    cases hnp : ur.noPassword
    rotate_left
    · -- a no-password user
      (try wp_auto)
      iapply HΦ
      isplitl [HPost]
      · iexact HPost
      iframe Hen Hown
      iframe Hbe Hbeok HT HF
      isplitr
      · iright; iexists .authFailed; iexact HfAF
      iunfold authenticated
      ileft; ipureintro; exact ⟨by simp, rfl⟩
    (try wp_auto)
    wp_apply (h_Revision st R M (some hs)) $$ [$Hinv Hown] as %rev ⟨Hown, -, -⟩
    · iunfold authOwnOpt; iexact Hown
    iunfold authOwnOpt at Hown
    (try wp_auto)
    wp_bind (App (App (App (Val #(methods tpi.ty go!"assign" tpi.v)) (Val #ctx)) (Val #username)) (Val #rev))
    iapply HAssign $$ %ctx %username %rev [Hctx]
    · iexact Hctx
    inext
    iintro %tok %err Htok
    (try wp_auto)
    cases err with
    | ok ei =>
      icases Htok with (⟨%Hn, -⟩ | ⟨-, %e, #He⟩)
      · cases Hn
      (try wp_auto)
      iapply HΦ
      isplitl [HPost]
      · iexact HPost
      iframe Hen Hown
      iframe Hbe Hbeok HT HF
      isplitr
      · iright; iexists e; iexact He
      iunfold authenticated
      ileft; ipureintro; exact ⟨by simp, rfl⟩
    | nil =>
      icases Htok with (⟨-, #Htok⟩ | ⟨%Hne, -⟩)
      rotate_left
      · exact absurd rfl Hne
      (try wp_auto)
      (try wp_auto)
      wp_apply h_Check as %ce -
      · ipureintro; exact Hlgnn
      (try wp_auto)
      wp_if_destruct
      · -- no entry to write
        (try wp_auto)
        irename «$r0» => Hrl
        generalize «$r0_ptr» = rl at *
        (try wp_auto)
        iapply HΦ
        isplitl [HPost]
        · iexact HPost
        iframe Hen Hown
        iframe Hbe Hbeok HT HF
        isplitr
        · ileft; ipureintro; rfl
        iunfold authenticated
        iright
        isplitr
        · ipureintro; rfl
        iexists tok, _
        iframe Hrl
        isplitr
        · ipureintro; rfl
        iframe Htok Hev
        ipureintro; exact ⟨sta, Hl, by simp [Hur.1]⟩
      · wp_apply h_redactToken _ as %fp -
        (try wp_auto)
        wp_apply h_String _ _ as %f1 -
        (try wp_auto)
        wp_apply h_String _ _ as %f2 -
        (try wp_auto)
        wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1, f2]
        isplitr
        · ipureintro; rfl
        iintro %fsl ⟨-, -⟩
        (try wp_auto)
        wp_apply h_Write
        · ipureintro; exact Hif
        (try wp_auto)
        irename «$r0» => Hrl
        generalize «$r0_ptr» = rl at *
        (try wp_auto)
        iapply HΦ
        isplitl [HPost]
        · iexact HPost
        iframe Hen Hown
        iframe Hbe Hbeok HT HF
        isplitr
        · ileft; ipureintro; rfl
        iunfold authenticated
        iright
        isplitr
        · ipureintro; rfl
        iexists tok, _
        iframe Hrl
        isplitr
        · ipureintro; rfl
        iframe Htok Hev
        ipureintro; exact ⟨sta, Hl, by simp [Hur.1]⟩

theorem auth.authStore.Authenticate.wp_proof
    (h_IsAuthEnabled : auth.authStore.IsAuthEnabled.spec (GF := GF) (hG := hG))
    (h_Revision : auth.authStore.Revision.spec (GF := GF) (hG := hG))
    (h_redactToken : auth.redactToken.spec (GF := GF) (hG := hG))
    (h_String : zap.String.spec (GF := GF) (hG := hG))
    (h_Check : zap.Logger.Check.spec (GF := GF) (hG := hG))
    (h_Write : zapcore.CheckedEntry.Write.spec (GF := GF) (hG := hG)) :
    auth.authStore.Authenticate.spec (GF := GF) (hG := hG) := by
  intro st R M P f T hs Pre Q Post ctx username password
  iintro %Φ ⟨#Hpkg, #Hinv, Hen, Hown, HWR, Hcs, Hctx⟩ HΦ
  iunfold authWR at HWR
  icases HWR with ⟨⟨%be, Hbe⟩, HT, Henh, Hca⟩
  iapply (auth.authStore.Authenticate.wp_core h_IsAuthEnabled h_Revision h_redactToken h_String
      h_Check h_Write st R M P f T iprop(enabledHalf st M ∗ cacheHalf st M) hs Pre Q Post ctx
      username password be) $$ [$Hpkg $Hinv $Hen $Hown $Hbe $HT $Hcs $Hctx Henh Hca]
  · iframe Henh Hca
  inext
  iintro %resp %err ⟨HPP, Hen, Hown, Hbe, HT, ⟨Henh, Hca⟩, -, Hau⟩
  iapply HΦ
  iframe HPP Hen Hown Hau
  iunfold authWR; iframe HT Henh Hca; iexists be; iframe Hbe

/-- **`Authenticate.specTB`** (C1's A2): `wp_core` with the halves at their values as the frame. -/
theorem auth.authStore.Authenticate.wp_tieB
    (h_IsAuthEnabled : auth.authStore.IsAuthEnabled.spec (GF := GF) (hG := hG))
    (h_Revision : auth.authStore.Revision.spec (GF := GF) (hG := hG))
    (h_redactToken : auth.redactToken.spec (GF := GF) (hG := hG))
    (h_String : zap.String.spec (GF := GF) (hG := hG))
    (h_Check : zap.Logger.Check.spec (GF := GF) (hG := hG))
    (h_Write : zapcore.CheckedEntry.Write.spec (GF := GF) (hG := hG)) :
    auth.authStore.Authenticate.specTB (GF := GF) (hG := hG) := by
  intro st R M P f T hs Pre Q Post ctx username password b0 sc0 be
  iintro %Φ ⟨#Hpkg, #Hinv, Hen, Hown, HWR, Hcs, Hctx⟩ HΦ
  iunfold authWRxB at HWR
  icases HWR with ⟨Hbe, HT, Hfl, #Hev, Hca, #Hsn⟩
  iapply (auth.authStore.Authenticate.wp_core h_IsAuthEnabled h_Revision h_redactToken h_String
      h_Check h_Write st R M P f T iprop(flagAt st M b0 ∗ cacheAt st M sc0) hs Pre Q Post ctx
      username password be) $$ [$Hpkg $Hinv $Hen $Hown $Hbe $HT $Hcs $Hctx Hfl Hca]
  · iframe Hfl Hca
  inext
  iintro %resp %err ⟨HPP, Hen, Hown, Hbe, HT, ⟨Hfl, Hca⟩, #He, Hau⟩
  iapply HΦ
  iframe HPP Hen Hown Hau He
  iunfold authWRxB; iframe Hbe HT Hfl Hev Hca Hsn

end proof

end EtcdGrove
end Perennial
