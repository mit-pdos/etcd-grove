/-
Proof of `Spec/go_etcd_io/etcd/server/v3/auth/authStore__RenewToken.lean` (pr-verify etcd#22560, 2026-10-16).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__RenewToken
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__IsAuthEnabled
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__Revision

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

theorem auth.authStore.RenewToken.wp_proof
    (h_IsAuthEnabled : auth.authStore.IsAuthEnabled.spec (GF := GF) (hG := hG))
    (h_Revision : auth.authStore.Revision.spec (GF := GF) (hG := hG)) :
    auth.authStore.RenewToken.spec (GF := GF) (hG := hG) := fun st R ctx tk => by
  wp_start as ⟨#Hinv, Hen, HR⟩
  ihave #Hstrings : isPkgInit (PROP := IProp GF) pkg_id.strings $$ []
  · iPkgInit
  ihave Hai : (authInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hai with ⟨-, #HeUNF, -, -, #HeIT, -⟩
  iunfold authErrVar at HeUNF HeIT
  icases HeUNF with ⟨%eUNF, #HeUNF, -⟩
  icases HeIT with ⟨%eIT, #HeIT, -⟩
  ihave #Hinv' := Hinv
  iunfold authInv at Hinv'
  icases Hinv' with ⟨%Hst, -, -, ⟨%be, #Hbe, #Hbeok⟩, ⟨%tp, #Htp, #Htpok⟩, -, -⟩
  iunfold tokenProviderOk at Htpok
  icases Htpok with ⟨%ti, %Hti, #Hinfo, #Hrenew, %Adm, #Hinval⟩
  subst Hti
  wp_auto
  wp_apply (h_IsAuthEnabled st R) $$ [$Hinv $Hen] as %en Hen
  cases en
  · wp_auto
    iapply HΦ
    iframe
    ileft; ipureintro; rfl
  wp_auto
  wp_apply strings.wp_TrimPrefix
  wp_apply (h_Revision st R) $$ [$Hinv] as %rev -
  (try wp_auto)
  wp_apply Hrenew as %nt %err %Herr
  cases err with
  | ok e =>
    wp_auto
    iapply HΦ
    iframe
    iright; ipureintro; rfl
  | nil =>
  wp_auto
  wp_apply (h_Revision st R) $$ [$Hinv] as %rev' -
  (try wp_auto)
  wp_apply Hinfo as %a %ok #Ha
  cases ok
  · wp_auto
    iapply HΦ
    iframe
    iright; ipureintro; rfl
  iunfold authInfoRO at Ha
  icases Ha with (%Hnull | ⟨%user, %arev, %Hann, #Hu, #Hrev⟩)
  · subst Hnull
    wp_auto
    iapply HΦ
    iframe
    iright; ipureintro; rfl
  wp_auto
  rw [decide_eq_false Hann]
  wp_auto
  iunfold authBackendOk at Hbeok
  icases Hbeok with ⟨%bi, %Hbi, #HRT⟩
  subst Hbi
  wp_auto
  wp_apply HRT as %tx Htx
  iunfold authReadTxOk at Htx
  icases Htx with ⟨%ti', %Hti', Htx⟩
  subst Hti'
  icases Htx with ⟨%Tk, #HRL, #HUG, #HRU⟩
  wp_auto
  wp_bind (App (Val #(methods ti'.ty go!"RLock" ti'.v)) (Val #()))
  iapply HRL $$ HR
  inext
  iintro Htok
  wp_auto
  wp_bind (App (Val #(methods ti'.ty go!"UnsafeGetUser" ti'.v)) (Val #user))
  iapply HUG $$ Htok
  inext
  iintro %u Htok
  wp_auto
  wp_bind (App (Val #(methods ti'.ty go!"RUnlock" ti'.v)) (Val #()))
  iapply HRU $$ Htok
  inext
  iintro HR
  wp_auto
  wp_if_destruct
  · -- `u == nil`: `as.tokenProvider.invalidateUser(ai.Username)`. The provider's
    -- `invalidateUser` is the admin's (`tokenProviderOk`: it needs the provider's `Adm`, for the
    -- simple provider `tsAdmin`, as it reads `simpleTokenKeeper` without the lock); `RenewToken`
    -- runs on a request goroutine (the in-process client of v3election/v3lock), which does not
    -- have it. Not provable: the PR's data race with `disable` (`AuthDisable` on the apply
    -- goroutine), notes/pr-verify/etcd-22560.md.
    sorry
  iapply HΦ
  iframe
  ileft; ipureintro; rfl

end proof

end EtcdGrove
end Perennial
