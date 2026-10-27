/-
**`IsAdminPermitted` at the latest state** (the auth plan's E2s, 2026-10-26; `notes/decisions.md`,
"E2s of the auth plan"). As `Latest.lean` for the permission checks: the apply thread, holding the
admin side's authority `hs` and its half of the flag tied to the latest state (`latestTie`), is
promised the latest state's verdict (`adminVerdictL`), exact both ways, where the generic spec's
(`adminVerdict`, S3) is some recorded state's per read.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.Latest
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__IsAdminPermitted

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth auth

namespace auth

section pure
variable [GooseExts]

/-- **`IsAdminPermitted`'s verdict at the latest state** of the admin side's authority `hs` (pure):
in `on γa`, the check passes exactly when the latest state admits the principal (`adminOk`: auth
disabled, or a named user existing with the root role); in `off` it passes; in `any` nothing. -/
def adminVerdictL (M : AuthMode) (hs : List AuthState) (ai : Option AuthInfoM) (err : GoInterface) :
    Prop :=
  match M with
  | .on _ => ∀ stl, hs.getLast? = some stl → (err = GoInterface.nil ↔ adminOk stl ai)
  | .off => err = GoInterface.nil
  | .any => True

end pure

section res
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The apply thread's latest-state resource** of the store `st` at the admin side's history
`hs` (the auth plan's E2s): the authority, and its halves of the flag and of the cache tied to the
latest state (`latestTie`); what the checks' `specL`s take and give back. Since E3f also the
halves' recorded verdicts (`enabledVerdict`, `authSnap`, persistent), so that it is exactly the
authority with the tie (`authOwnT`, `TieRes.lean`) and the apply thread can lend it and take it
back (`authOwnT_lend`). -/
def latestRes (st : Loc) (M : AuthMode) (hs : List AuthState) : IProp GF :=
  iprop(authOwn M hs ∗ ∃ (b : Bool) (sc : AuthState), flagAt st M b ∗ cacheAt st M sc ∗
    enabledVerdict M b ∗ authSnap M sc ∗ ⌜latestTie M hs b sc⌝)

/-- **The latest state recorded** (persistent): in `on γa`, the last state of `hs` at its index;
otherwise nothing. What turns a verdict at the latest state into S3's verdict over recorded states
(`permVerdict_of_L`). -/
def latestSnap (M : AuthMode) (hs : List AuthState) : IProp GF :=
  match M with
  | .on γa => iprop(∃ (i : Nat) (stl : AuthState), ⌜hs.getLast? = some stl⌝ ∗ authStateAt γa i stl)
  | _ => iprop(True)

instance latestSnap_persistent (M : AuthMode) (hs : List AuthState) :
    Persistent (latestSnap (GF := GF) M hs) := by
  unfold latestSnap; cases M <;> infer_instance

/-- A half of a monotone list's authority keeps its lower bound (`auth_lb_op`). -/
theorem monoListAuthOwn_keep_lb (γ : GName) (q : Qp) (l : List AuthState) :
    monoListAuthOwn (GF := GF) γ q l ⊢ monoListAuthOwn γ q l ∗ monoListLbOwn γ l := by
  unfold monoListAuthOwn monoListLbOwn
  have h := Iris.MonoList.auth_lb_op (DFrac.own q) (l.map encodeO)
  refine Iris.BI.BIBase.Entails.trans ?_ (own_op γ _ _).1
  rw [← h]

/-- **The admin side's authority records its latest state** (no update: the authority's half keeps
its lower bound). -/
theorem authOwn_latestSnap (M : AuthMode) (hs : List AuthState) :
    authOwn (GF := GF) M hs ⊢ authOwn M hs ∗ latestSnap M hs := by
  cases M with
  | on γa =>
    simp only [authOwn, latestSnap, authHistHalf]
    iintro ⟨⟨Hh, %Hk⟩, ⟨%stl, %Hl, Hc⟩⟩
    ihave ⟨Hh, #Hlb⟩ := monoListAuthOwn_keep_lb γa.hist _ hs $$ Hh
    have hi : hs[hs.length - 1]? = some stl := by
      cases hs with
      | nil => cases Hl
      | cons x xs =>
        rw [List.getLast?_eq_getElem?] at Hl
        exact Hl
    isplitl [Hh Hc]
    · iframe Hh; isplitr
      · ipureintro; exact Hk
      · iexists stl; iframe Hc; ipureintro; exact Hl
    · iexists hs.length - 1, stl
      isplitr
      · ipureintro; exact Hl
      unfold authStateAt
      isplitl
      · iapply (monoListIdxOwn_get (hs.length - 1) stl hi) $$ Hlb
      · ipureintro; exact Hk stl (List.mem_of_getElem? hi)
  | off => simp only [latestSnap]; iintro H; iframe H
  | any => simp only [latestSnap]; iintro H; iframe H

/-- **S3's verdict from the latest state's**, the latest state recorded. -/
theorem permVerdict_of_L (M : AuthMode) (hs : List AuthState)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (k e : GoString) (op : PermType)
    (err : GoInterface) (h : permVerdictL M hs (authInfoM info) k e op err) :
    latestSnap (GF := GF) M hs ⊢ permVerdict M info k e op err := by
  cases M with
  | on γa =>
    simp only [latestSnap, permVerdict]
    iintro #⟨%i, %stl, %Hl, #Hs⟩
    obtain ⟨hp, hr⟩ := h stl Hl
    isplitl
    · iexists i, stl; iframe Hs; ipureintro; exact fun he => (hp he).1
    isplitl
    · iexists i, stl; iframe Hs; ipureintro; exact fun he => (hp he).2
    · iexists ⟨stl, stl, stl, stl⟩
      isplitl
      · iapply (recordedV_intro γa i i i i stl stl stl stl) $$ Hs Hs Hs Hs
      · ipureintro; exact hr
  | off => simp only [permVerdict]; iintro -; ipureintro; exact h
  | any => simp only [permVerdict]; iintro -; itrivial

end res

end auth

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- `as.IsAdminPermitted(authInfo)` on the apply thread: with the admin side's authority `hs` and
its half of the flag (at `b`) tied to the latest state, the latest state's verdict
(`adminVerdictL`); the resources back. -/
abbrev auth.authStore.IsAdminPermitted.specL : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : auth.AuthMode) (hs : List auth.AuthState) (b : Bool)
    (sc : auth.AuthState) (a : Loc) (ai : Option AuthInfo) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗
      authRd st R M ∗ authInfoAt a dq ai ∗ authOwn M hs ∗ flagAt st M b ∗ ⌜latestTie M hs b sc⌝ }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"IsAdminPermitted")) (Val #a))
  {{ (err : GoInterface), RET #err; authRd st R M ∗ authInfoAt a dq ai ∗ authErrIs err ∗
      authOwn M hs ∗ flagAt st M b ∗ ⌜adminVerdictL M hs (ai.map authInfoM) err⌝ }}

end spec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- A refusal at the latest state, auth enabled there (the flag's half), for a principal the
latest state does not admit. -/
theorem adminVerdictL_on_refused (γa : AuthNames) (hs : List AuthState) (sc : AuthState)
    (ai : Option AuthInfoM) (err : GoInterface) (herr : err ≠ GoInterface.nil)
    (ht : latestTie (.on γa) hs true sc)
    (hwhy : ∀ stl, hs.getLast? = some stl →
      ∀ a u, ai = some a → a.user ≠ [] → stl.users !! a.user = some u → ¬ isRoot u) :
    adminVerdictL (.on γa) hs ai err := by
  intro stl hl
  have he := (ht stl hl).1
  constructor
  · intro h; exact absurd h herr
  · rintro (hd | ⟨a, u, hai, hne, hu, hr⟩)
    · rw [← he] at hd; cases hd
    · exact absurd hr (hwhy stl hl a u hai hne hu)

theorem auth.authStore.IsAdminPermitted.wp_latest
    (h_IsAuthEnabled : auth.authStore.IsAuthEnabled.specL (GF := GF) (hG := hG))
    (h_lockedReadTx : auth.authStore.lockedReadTx.specL (GF := GF) (hG := hG))
    (h_hasRootRole : auth.hasRootRole.spec (GF := GF) (hG := hG)) :
    auth.authStore.IsAdminPermitted.specL (GF := GF) (hG := hG) := by
  intro st R M hs b sc a ai dq
  wp_start as ⟨#Hinv, Hrd, Ha, Hown, Hfl, %Htie⟩
  iunfold authRd at Hrd
  icases Hrd with ⟨Hen, Hca, Hbr, HR⟩
  ihave Hai : (authInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hai with ⟨#HeUE, #HeUNF, #HePD, #HeOR, #HeIT, #Hs1, #Hs2, -⟩
  ihave #HeUE' := HeUE
  iunfold authErrVar at HeUE'
  icases HeUE' with ⟨%eUE, #HeUEa, -⟩
  ihave #HeUNF' := HeUNF
  iunfold authErrVar at HeUNF'
  icases HeUNF' with ⟨%eUNF, #HeUNFa, -⟩
  ihave #HePD' := HePD
  iunfold authErrVar at HePD'
  icases HePD' with ⟨%ePD, #HePDa, -⟩
  ihave #Hinv' := Hinv
  iunfold authInv at Hinv'
  icases Hinv' with ⟨%Hst, -, -, -, -, -, -⟩
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply (h_IsAuthEnabled st R M b) $$ [$Hinv $Hen $Hfl] as %en ⟨Hen, Hfl, #Hev, %Hen_b⟩
  subst Hen_b
  cases en
  · wp_auto
    iapply HΦ
    iunfold authRd
    iframe
    isplitl []
    · iunfold authErrIs; ileft; ipureintro; rfl
    ipureintro
    cases M with
    | on γa =>
      intro stl hl
      have he := (Htie stl hl).1
      exact ⟨fun _ => Or.inl he.symm, fun _ => rfl⟩
    | off => rfl
    | any => trivial
  ihave %Hnoff := enabledVerdict_true_ne_off M $$ Hev
  wp_auto
  cases ai with
  | none =>
    iunfold authInfoAt at Ha
    icases Ha with %Han
    subst Han
    (try wp_auto)
    iapply HΦ
    iunfold authRd
    iframe
    isplitl []
    · iunfold authInfoAt; ipureintro; rfl
    isplitl []
    · iunfold authErrIs
      iright
      iexists ErrUserEmpty, eUE
      iframe HeUEa
      ipureintro; simp
    ipureintro
    cases M with
    | on γa =>
      exact adminVerdictL_on_refused γa hs sc none _ (fun h => by cases h) Htie
        (fun _ _ a _ h => by cases h)
    | off => exact absurd rfl Hnoff
    | any => trivial
  | some info =>
    iunfold authInfoAt at Ha
    ihave %Hann := typedPointsto_not_null $$ Ha
    simp only [show decide (a = null) = false from decide_eq_false Hann]
    iStructNamed Ha
    wp_auto
    wp_if_destruct
    · (try wp_auto)
      ihave Ha : a ↦{dq} info $$ [Username Revision]
      · iapply typedPointsto_combine a info dq Hann
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      iapply HΦ
      iunfold authRd
      iframe
      isplitl [Ha]
      · iunfold authInfoAt; iexact Ha
      isplitl []
      · iunfold authErrIs
        iright
        iexists ErrUserEmpty, eUE
        iframe HeUEa
        ipureintro; simp
      ipureintro
      cases M with
      | on γa =>
        refine adminVerdictL_on_refused γa hs sc _ _ (fun h => by cases h) Htie ?_
        intro _ _ a' _ hai hne _
        simp only [Option.map_some, Option.some.injEq] at hai
        subst hai
        exact absurd Hif hne
      | off => exact absurd rfl Hnoff
      | any => trivial
    have hname : info.Username' ≠ [] := Hif
    wp_apply (h_lockedReadTx st R M hs) $$ [$Hinv $Hbr $HR $Hown] as %tx ⟨Hbr, Htx, Hown⟩
    iunfold authReadTxLockedL at Htx
    icases Htx with ⟨%ti, %Hti, Htx⟩
    subst Hti
    icases Htx with ⟨%sta, %Hs, Htok, -, %Hsta, #Hreads⟩
    iunfold authTxReads at Hreads
    icases Hreads with ⟨#Hrds, #HRU⟩
    iunfold authReaderOk at Hrds
    icases Hrds with ⟨#HUG, -, -, -, -⟩
    wp_auto
    wp_bind (App (Val #(methods ti.ty go!"UnsafeGetUser" ti.v)) (Val #info.Username'))
    iapply HUG $$ Htok
    inext
    iintro %u ⟨Htok, Hu⟩
    ihave Ha : a ↦{dq} info $$ [Username Revision]
    · iapply typedPointsto_combine a info dq Hann
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    wp_auto
    wp_if_destruct
    · ihave %Hnone := userOut_null sta info.Username' $$ Hu
      (try wp_auto)
      wp_bind (App (Val #(methods ti.ty go!"RUnlock" ti.v)) (Val #()))
      iapply HRU $$ Htok
      inext
      iintro HR
      (try wp_auto)
      iapply HΦ
      iunfold authRd
      iframe
      isplitl [Ha]
      · iunfold authInfoAt; iexact Ha
      isplitl []
      · iunfold authErrIs
        iright
        iexists ErrUserNotFound, eUNF
        iframe HeUNFa
        ipureintro; simp
      ipureintro
      cases M with
      | on γa =>
        refine adminVerdictL_on_refused γa hs sc _ _ (fun h => by cases h) Htie ?_
        intro stl hl a' u' hai _ hu'
        have hsl := histLast_on_unique γa hs sta stl Hsta hl
        subst hsl
        simp only [Option.map_some, Option.some.injEq] at hai
        subst hai
        have hu'' : sta.users !! info.Username' = some u' := hu'
        rw [Hnone] at hu''; cases hu''
      | off => exact absurd rfl Hnoff
      | any => trivial
    ihave Hu' := userOut_some u sta info.Username' Hif $$ Hu
    icases Hu' with ⟨%roles, %ur, %Hur, Hu⟩
    wp_apply h_hasRootRole $$ [$Hu] as %root ⟨Hu, %Hroot⟩
    · ipureintro; rw [Hur.2.1]; exact Hur.2.2
    cases root
    · have hn : ¬ isRoot roles := by rw [← Hur.2.1]; exact of_decide_eq_false Hroot.symm
      (try wp_auto)
      wp_bind (App (Val #(methods ti.ty go!"RUnlock" ti.v)) (Val #()))
      iapply HRU $$ Htok
      inext
      iintro HR
      (try wp_auto)
      iapply HΦ
      iunfold authRd
      iframe
      isplitl [Ha]
      · iunfold authInfoAt; iexact Ha
      isplitl []
      · iunfold authErrIs
        iright
        iexists ErrPermissionDenied, ePD
        iframe HePDa
        ipureintro; simp
      ipureintro
      cases M with
      | on γa =>
        refine adminVerdictL_on_refused γa hs sc _ _ (fun h => by cases h) Htie ?_
        intro stl hl a' u' hai _ hu'
        have hsl := histLast_on_unique γa hs sta stl Hsta hl
        subst hsl
        simp only [Option.map_some, Option.some.injEq] at hai
        subst hai
        have hu'' : sta.users !! info.Username' = some u' := hu'
        rw [Hur.1] at hu''; cases hu''
        exact hn
      | off => exact absurd rfl Hnoff
      | any => trivial
    · have hroot : isRoot roles := by rw [← Hur.2.1]; exact of_decide_eq_true Hroot.symm
      (try wp_auto)
      wp_bind (App (Val #(methods ti.ty go!"RUnlock" ti.v)) (Val #()))
      iapply HRU $$ Htok
      inext
      iintro HR
      (try wp_auto)
      iapply HΦ
      iunfold authRd
      iframe
      isplitl [Ha]
      · iunfold authInfoAt; iexact Ha
      isplitl []
      · iunfold authErrIs; ileft; ipureintro; rfl
      ipureintro
      cases M with
      | on γa =>
        intro stl hl
        have hsl := histLast_on_unique γa hs sta stl Hsta hl
        subst hsl
        refine ⟨fun _ => Or.inr ⟨authInfoM info, roles, rfl, hname, Hur.1, hroot⟩, fun _ => rfl⟩
      | off => exact absurd rfl Hnoff
      | any => trivial

end proof

end EtcdGrove
end Perennial
