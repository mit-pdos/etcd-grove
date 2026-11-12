/-
**`IsAdminPermitted` no older than a reader's lower bound** (the lease-src plan, 2026-11-02;
`notes/lease-src-plan.md`). Lean-first (no Rocq counterpart).

As `IsAuthEnabled.specLb` and the permission checks' `specLb`s (E3h, E3j): a reader holding a lower
bound `n` of the published index (`authPubLbM`) has `IsAdminPermitted`'s passing verdict at a state
no older than `n`. `IsAdminPermitted` passes when `IsAuthEnabled()` reads `false` (a state no
older than `n`, `IsAuthEnabled.specLb`), or when the user its read transaction finds (a state no
older than `n`, `lockedReadTx.specLb`) has the root role; either way `adminOk` holds of that state.
What the lease checks need of it (`isAuthStoreLeaseLb`). A refusal is stated by nothing here (the
lease checks need only the passing verdict).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.Fresh
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

end spec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.authStore.IsAdminPermitted.wp_lb
    (h_IsAuthEnabled : auth.authStore.IsAuthEnabled.specLb (GF := GF))
    (h_lockedReadTx : auth.authStore.lockedReadTx.specLb (GF := GF) (hG := hG))
    (h_hasRootRole : auth.hasRootRole.spec (GF := GF) (hG := hG)) :
    auth.authStore.IsAdminPermitted.specLb (GF := GF) (hG := hG) := by
  intro st R M n a info dq
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
    · iapply adminVerdictFrom_of_disabled M n info $$ Hev
  wp_auto
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
    isplitl []
    · iunfold authErrIs
      iright
      iexists ErrUserEmpty, eUE
      iframe HeUEa
      ipureintro; simp
    · iapply (adminVerdictFrom_refused M n info (GoInterface.ok eUE) (fun h => by cases h)) $$ Hev
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
  · (try wp_auto)
    wp_bind (App (Val #(methods ti.ty go!"RUnlock" ti.v)) (Val #()))
    iapply HRU $$ Htok
    inext
    iintro HR
    (try wp_auto)
    iapply HΦ
    iunfold authRd
    iframe
    isplitl []
    · iunfold authErrIs
      iright
      iexists ErrUserNotFound, eUNF
      iframe HeUNFa
      ipureintro; simp
    · iapply (adminVerdictFrom_refused M n info (GoInterface.ok eUNF) (fun h => by cases h)) $$ Hev
  ihave Hu' := userOut_some u sta info.Username' Hif $$ Hu
  icases Hu' with ⟨%roles, %ur, %Hur, Hu⟩
  wp_apply h_hasRootRole $$ [$Hu] as %root ⟨Hu, %Hroot⟩
  · ipureintro; rw [Hur.2.1]; exact Hur.2.2
  cases root
  · (try wp_auto)
    wp_bind (App (Val #(methods ti.ty go!"RUnlock" ti.v)) (Val #()))
    iapply HRU $$ Htok
    inext
    iintro HR
    (try wp_auto)
    iapply HΦ
    iunfold authRd
    iframe
    isplitl []
    · iunfold authErrIs
      iright
      iexists ErrPermissionDenied, ePD
      iframe HePDa
      ipureintro; simp
    · iapply (adminVerdictFrom_refused M n info (GoInterface.ok ePD) (fun h => by cases h)) $$ Hev
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
    isplitl []
    · iunfold authErrIs; ileft; ipureintro; rfl
    · iapply (adminVerdictFrom_root M n info sta roles hname Hur.1 hroot) $$ Hsnap

end proof

end EtcdGrove
end Perennial
