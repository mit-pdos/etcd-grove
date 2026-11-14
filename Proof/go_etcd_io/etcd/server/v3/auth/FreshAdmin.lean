/-
**`IsAdminPermitted` no older than a reader's lower bound** (the lease-src plan, 2026-11-02;
`notes/lease-src-plan.md`). Lean-first (no Rocq counterpart).

As `IsAuthEnabled.specLb` and the permission checks' `specLb`s (E3h, E3j): a reader holding a lower
bound `n` of the published index (`authPubLbM`) has `IsAdminPermitted`'s passing verdict at a state
no older than `n`. `IsAdminPermitted` passes when `IsAuthEnabled()` reads `false` (a state no
older than `n`, `IsAuthEnabled.specLb`), or when the user its read transaction finds (a state no
older than `n`, `lockedReadTx.specLb`) has the root role; either way `adminOk` holds of that state.
What the lease checks need of it (`isAuthStoreLeaseLb`).

**The refusal half** (auth-guard-completeness G1, 2026-11-14; `notes/auth-guard-scope.md`, §2.2):
`IsAdminPermitted.specLbO` takes the auth info as `authInfoAt` (`nil` covered: the admin guards pass
`AuthInfoFromCtx`'s `nil`) and states a refusal too (`adminVerdictFromO`): auth enabled at a state recorded at an index at least `n`,
each error tied to its case (`adminRefusalFrom`): `ErrUserEmpty` for a `nil` or unnamed auth info,
`ErrUserNotFound` for a user absent at such a state, `ErrPermissionDenied` for one present there
without the root role. `specLb` follows from it (`adminVerdictFromO_some`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.WhyDefs
public import Proof.go_etcd_io.etcd.server.v3.auth.ReadLb
public import Proof.go_etcd_io.etcd.server.v3.auth.VerdictLemmas
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__IsAdminPermitted
public import Spec.go_etcd_io.etcd.server.v3.auth.hasRootRole

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth auth

namespace auth

section defs
variable [GooseExts] {GF : BundledGFunctors} [AllG GF]

/-- **`IsAdminPermitted`'s verdict no older than the index `n`** in the mode `M` (persistent): in
`on γa`, a pass admits the principal (`adminOk`) at a state recorded at an index at least `n`; in
`off`, it passes; in `any`, nothing. -/
def adminVerdictFrom (M : AuthMode) (n : Nat) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (err : GoInterface) : IProp GF :=
  match M with
  | .off => iprop(⌜err = GoInterface.nil⌝)
  | .any => iprop(True)
  | .on γa => iprop(∃ (i : Nat) (st : AuthState), authStateAt γa i st ∗
      ⌜n ≤ i ∧ (err = GoInterface.nil → adminOk st (some (authInfoM info)))⌝)

instance adminVerdictFrom_persistent (M : AuthMode) (n : Nat)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (err : GoInterface) :
    Persistent (adminVerdictFrom (GF := GF) M n info err) := by
  unfold adminVerdictFrom; cases M <;> infer_instance

end defs

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- With auth disabled at a state no older than `n`, a pass. -/
theorem adminVerdictFrom_of_disabled (M : AuthMode) (n : Nat)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) :
    enabledVerdictFrom (GF := GF) M n false ⊢ adminVerdictFrom M n info GoInterface.nil := by
  cases M with
  | off => unfold adminVerdictFrom; iintro -; ipureintro; rfl
  | any => unfold adminVerdictFrom; iintro -; itrivial
  | on γa =>
    unfold enabledVerdictFrom adminVerdictFrom
    iintro ⟨%j, %st, #Hst, %Hb⟩
    iexists j, st; iframe #; ipureintro
    exact ⟨Hb.1, fun _ => Or.inl Hb.2.symm⟩

/-- With auth enabled at a state no older than `n`, a refusal (an error is stated by nothing). -/
theorem adminVerdictFrom_refused (M : AuthMode) (n : Nat)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (err : GoInterface)
    (herr : err ≠ GoInterface.nil) :
    enabledVerdictFrom (GF := GF) M n true ⊢ adminVerdictFrom M n info err := by
  cases M with
  | off => unfold enabledVerdictFrom; iintro %H; cases H
  | any => unfold adminVerdictFrom; iintro -; itrivial
  | on γa =>
    unfold enabledVerdictFrom adminVerdictFrom
    iintro ⟨%j, %st, #Hst, %Hb⟩
    iexists j, st; iframe #; ipureintro
    exact ⟨Hb.1, fun h => absurd h herr⟩

/-- A user with the root role at a state no older than `n`: a pass. -/
theorem adminVerdictFrom_root (M : AuthMode) (n : Nat)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (sta : AuthState) (roles : User)
    (hname : info.Username' ≠ []) (hu : sta.users !! info.Username' = some roles)
    (hroot : isRoot roles) :
    authSnapFrom (GF := GF) M n sta ⊢ adminVerdictFrom M n info GoInterface.nil := by
  cases M with
  | off => unfold adminVerdictFrom; iintro -; ipureintro; rfl
  | any => unfold adminVerdictFrom; iintro -; itrivial
  | on γa =>
    unfold authSnapFrom adminVerdictFrom
    iintro ⟨%j, #Hsu, %Hj⟩
    iexists j, sta; iframe #; ipureintro
    exact ⟨Hj, fun _ => Or.inr ⟨authInfoM info, roles, rfl, hname, hu, hroot⟩⟩

end lemmas

section refusal
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- Both halves give the passing one (`specLb`'s verdict). -/
theorem adminVerdictFromO_some (M : AuthMode) (n : Nat) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (err : GoInterface) :
    adminVerdictFromO (GF := GF) M n (some info) err ⊢ adminVerdictFrom M n info err := by
  cases M with
  | off => unfold adminVerdictFromO adminVerdictFrom; iintro H; iexact H
  | any => unfold adminVerdictFrom; iintro -; itrivial
  | on γa =>
    unfold adminVerdictFromO adminVerdictFrom
    iintro ⟨⟨%i, %st, #Hst, %Hp⟩, -⟩
    iexists i, st; iframe Hst; ipureintro; exact Hp

/-- With auth disabled at a state no older than `n`, a pass. -/
theorem adminVerdictFromO_of_disabled (M : AuthMode) (n : Nat)
    (oinfo : Option go_etcd_io.etcd.server.v3.auth.AuthInfo) :
    enabledVerdictFrom (GF := GF) M n false ⊢ adminVerdictFromO M n oinfo GoInterface.nil := by
  cases M with
  | off => unfold adminVerdictFromO; iintro -; ipureintro; rfl
  | any => unfold adminVerdictFromO; iintro -; itrivial
  | on γa =>
    unfold enabledVerdictFrom adminVerdictFromO
    iintro ⟨%j, %st, #Hst, %Hb⟩
    isplitr
    · iexists j, st; iframe #; ipureintro
      exact ⟨Hb.1, fun _ => Or.inl Hb.2.symm⟩
    · iintro %h; exact absurd rfl h

/-- `authInfo == nil || authInfo.Username == ""` with auth enabled: `ErrUserEmpty`. -/
theorem adminVerdictFromO_empty (M : AuthMode) (n : Nat)
    (oinfo : Option go_etcd_io.etcd.server.v3.auth.AuthInfo) (err : GoInterface)
    (herr : err ≠ GoInterface.nil) (h : ∀ info, oinfo = some info → info.Username' = []) :
    enabledVerdictFrom (GF := GF) M n true ⊢ authErrOf .userEmpty err -∗
      adminVerdictFromO M n oinfo err := by
  cases M with
  | off => unfold enabledVerdictFrom; iintro %H; cases H
  | any => unfold adminVerdictFromO; iintro - -; itrivial
  | on γa =>
    unfold enabledVerdictFrom adminVerdictFromO
    iintro ⟨%j, %st, #Hst, %Hb⟩ #He
    isplitr
    · iexists j, st; iframe #; ipureintro; exact ⟨Hb.1, fun h' => absurd h' herr⟩
    · iintro %_
      unfold adminRefusalFrom
      isplitr
      · iexists j, st; iframe #; ipureintro; exact ⟨Hb.1, Hb.2.symm⟩
      · ileft; iframe He; ipureintro; exact h

/-- `tx.UnsafeGetUser(authInfo.Username) == nil`: `ErrUserNotFound`. -/
theorem adminVerdictFromO_noUser (M : AuthMode) (n : Nat)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (err : GoInterface) (sta : AuthState)
    (herr : err ≠ GoInterface.nil) (hname : info.Username' ≠ [])
    (hu : sta.users !! info.Username' = none) :
    enabledVerdictFrom (GF := GF) M n true ⊢ authSnapFrom M n sta -∗ authErrOf .userNotFound err -∗
      adminVerdictFromO M n (some info) err := by
  cases M with
  | off => unfold enabledVerdictFrom; iintro %H; cases H
  | any => unfold adminVerdictFromO; iintro - - -; itrivial
  | on γa =>
    unfold enabledVerdictFrom authSnapFrom adminVerdictFromO
    iintro ⟨%i, %sf, #Hsf, %Hb⟩ ⟨%j, #Hsu, %Hj⟩ #He
    isplitr
    · iexists i, sf; iframe #; ipureintro; exact ⟨Hb.1, fun h' => absurd h' herr⟩
    · iintro %_
      unfold adminRefusalFrom
      isplitr
      · iexists i, sf; iframe #; ipureintro; exact ⟨Hb.1, Hb.2.symm⟩
      · iright; iexists info; isplitr
        · ipureintro; exact ⟨rfl, hname⟩
        · ileft; iframe He; iexists j, sta; iframe Hsu; ipureintro; exact ⟨Hj, hu⟩

/-- `!hasRootRole(u)`: `ErrPermissionDenied`. -/
theorem adminVerdictFromO_notRoot (M : AuthMode) (n : Nat)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (err : GoInterface) (sta : AuthState)
    (roles : User) (herr : err ≠ GoInterface.nil) (hname : info.Username' ≠ [])
    (hu : sta.users !! info.Username' = some roles) (hn : ¬ isRoot roles) :
    enabledVerdictFrom (GF := GF) M n true ⊢ authSnapFrom M n sta -∗
      authErrOf .permissionDenied err -∗ adminVerdictFromO M n (some info) err := by
  cases M with
  | off => unfold enabledVerdictFrom; iintro %H; cases H
  | any => unfold adminVerdictFromO; iintro - - -; itrivial
  | on γa =>
    unfold enabledVerdictFrom authSnapFrom adminVerdictFromO
    iintro ⟨%i, %sf, #Hsf, %Hb⟩ ⟨%j, #Hsu, %Hj⟩ #He
    isplitr
    · iexists i, sf; iframe #; ipureintro; exact ⟨Hb.1, fun h' => absurd h' herr⟩
    · iintro %_
      unfold adminRefusalFrom
      isplitr
      · iexists i, sf; iframe #; ipureintro; exact ⟨Hb.1, Hb.2.symm⟩
      · iright; iexists info; isplitr
        · ipureintro; exact ⟨rfl, hname⟩
        · iright; iframe He; iexists j, sta, roles; iframe Hsu; ipureintro; exact ⟨Hj, hu, hn⟩

/-- A named user with the root role at a state no older than `n`: a pass. -/
theorem adminVerdictFromO_root (M : AuthMode) (n : Nat)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (sta : AuthState) (roles : User)
    (hname : info.Username' ≠ []) (hu : sta.users !! info.Username' = some roles)
    (hroot : isRoot roles) :
    authSnapFrom (GF := GF) M n sta ⊢ adminVerdictFromO M n (some info) GoInterface.nil := by
  cases M with
  | off => unfold adminVerdictFromO; iintro -; ipureintro; rfl
  | any => unfold adminVerdictFromO; iintro -; itrivial
  | on γa =>
    unfold authSnapFrom adminVerdictFromO
    iintro ⟨%j, #Hsu, %Hj⟩
    isplitr
    · iexists j, sta; iframe #; ipureintro
      exact ⟨Hj, fun _ => Or.inr ⟨authInfoM info, roles, rfl, hname, hu, hroot⟩⟩
    · iintro %h; exact absurd rfl h

end refusal

end auth

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- `as.IsAdminPermitted(authInfo)` read by a reader with the lower bound `n`, for a non-nil
`authInfo`: the verdict at a state no older than `n` (`adminVerdictFrom`). -/
abbrev auth.authStore.IsAdminPermitted.specLb : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : auth.AuthMode) (n : Nat) (a : Loc) (info : AuthInfo)
    (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗
      authRd st R M ∗ a ↦{dq} info ∗ authPubLbM M n }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"IsAdminPermitted")) (Val #a))
  {{ (err : GoInterface), RET #err; authRd st R M ∗ a ↦{dq} info ∗ authErrIs err ∗
      auth.adminVerdictFrom M n info err }}

/-- `as.IsAdminPermitted(authInfo)` read by a reader with the lower bound `n`, the auth info `nil`
or not (`authInfoAt`): both halves of the verdict at states no older than `n`
(`adminVerdictFromO`; auth-guard-completeness G1). -/
abbrev auth.authStore.IsAdminPermitted.specLbO : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : auth.AuthMode) (n : Nat) (a : Loc) (oinfo : Option AuthInfo)
    (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗
      authRd st R M ∗ authInfoAt a dq oinfo ∗ authPubLbM M n }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"IsAdminPermitted")) (Val #a))
  {{ (err : GoInterface), RET #err; authRd st R M ∗ authInfoAt a dq oinfo ∗ authErrIs err ∗
      auth.adminVerdictFromO M n oinfo err }}

end spec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.authStore.IsAdminPermitted.wp_lbO
    (h_IsAuthEnabled : auth.authStore.IsAuthEnabled.specLb (GF := GF))
    (h_lockedReadTx : auth.authStore.lockedReadTx.specLb (GF := GF) (hG := hG))
    (h_hasRootRole : auth.hasRootRole.spec (GF := GF) (hG := hG)) :
    auth.authStore.IsAdminPermitted.specLbO (GF := GF) (hG := hG) := by
  intro st R M n a oinfo dq
  wp_start as ⟨#Hinv, Hrd, Ha, #Hlb⟩
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
  ihave #HoUE : authErrOf (GF := GF) .userEmpty (GoInterface.ok eUE) $$ []
  · iunfold authErrOf; iexists eUE; simp only [AuthErr.var]; iframe HeUEa
  ihave #HoUNF : authErrOf (GF := GF) .userNotFound (GoInterface.ok eUNF) $$ []
  · iunfold authErrOf; iexists eUNF; simp only [AuthErr.var]; iframe HeUNFa
  ihave #HoPD : authErrOf (GF := GF) .permissionDenied (GoInterface.ok ePD) $$ []
  · iunfold authErrOf; iexists ePD; simp only [AuthErr.var]; iframe HePDa
  ihave #Hinv' := Hinv
  iunfold authInv at Hinv'
  icases Hinv' with ⟨%Hst, -, -, -, -, -, -⟩
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply (h_IsAuthEnabled st R M n) $$ [$Hinv $Hen $Hlb] as %en ⟨Hen, #Hev⟩
  cases en
  · wp_auto
    iapply HΦ
    iunfold authRd
    iframe
    isplitl []
    · iunfold authErrIs; ileft; ipureintro; rfl
    · iapply adminVerdictFromO_of_disabled M n oinfo $$ Hev
  wp_auto
  cases oinfo with
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
    · iapply (adminVerdictFromO_empty M n none (GoInterface.ok eUE) (fun h => by cases h)
        (fun _ h => by cases h)) $$ Hev HoUE
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
      · iapply (adminVerdictFromO_empty M n (some info) (GoInterface.ok eUE) (fun h => by cases h)
          (fun i h => by cases h; exact Hif)) $$ Hev HoUE
    have hname : info.Username' ≠ [] := Hif
    wp_apply (h_lockedReadTx st R M n) $$ [$Hinv $Hbr $HR $Hlb] as %tx ⟨Hbr, Htx⟩
    iunfold authReadTxLockedFrom at Htx
    icases Htx with ⟨%ti, %Hti, Htx⟩
    subst Hti
    icases Htx with ⟨%sta, %Hs, Htok, #Hsnap, #Hreads⟩
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
      · iapply (adminVerdictFromO_noUser M n info (GoInterface.ok eUNF) sta (fun h => by cases h)
          hname Hnone) $$ Hev Hsnap HoUNF
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
      · iapply (adminVerdictFromO_notRoot M n info (GoInterface.ok ePD) sta roles
          (fun h => by cases h) hname Hur.1 hn) $$ Hev Hsnap HoPD
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
      · iapply (adminVerdictFromO_root M n info sta roles hname Hur.1 hroot) $$ Hsnap

/-- `specLb`, of `specLbO` at a non-`nil` auth info (the refusal half dropped). -/
theorem auth.authStore.IsAdminPermitted.wp_lb
    (h_IsAuthEnabled : auth.authStore.IsAuthEnabled.specLb (GF := GF))
    (h_lockedReadTx : auth.authStore.lockedReadTx.specLb (GF := GF) (hG := hG))
    (h_hasRootRole : auth.hasRootRole.spec (GF := GF) (hG := hG)) :
    auth.authStore.IsAdminPermitted.specLb (GF := GF) (hG := hG) := by
  intro st R M n a info dq
  iintro %Φ ⟨#Hpkg, #Hinv, Hrd, Ha, #Hlb⟩ HΦ
  iapply (auth.authStore.IsAdminPermitted.wp_lbO h_IsAuthEnabled h_lockedReadTx h_hasRootRole
    st R M n a (some info) dq) $$ [Hrd Ha]
  · iunfold authInfoAt; iframe; iframe #
  iintro !> %err ⟨Hrd, Ha, #He, #Hv⟩
  iunfold authInfoAt at Ha
  iapply HΦ
  iframe Hrd Ha He
  iapply adminVerdictFromO_some M n info err $$ Hv

end proof

end EtcdGrove
end Perennial
