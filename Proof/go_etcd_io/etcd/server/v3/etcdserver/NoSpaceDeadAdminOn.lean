/-
**`applyEntryNormal`'s NOSPACE branch is dead for an admin entry with auth on** (the auth plan's
E3j, 2026-10-27; E3i's "Not covered"). Lean-first (no Rocq counterpart).

E3i's `applyResultIs_notNoSpaceOn` covers the KV and cluster entries. An admitted admin entry's
result (`apply.Apply.adminSpecL`'s postcondition) is `nil` (skipped), the auth layer's rejection,
whose error `IsAdminPermitted` returned (`apply.adminRejErr`, since E3j stated over the auth
package's error variables, `authApplyErrIs`), or the admin step's, `nil` or the model's `AuthErr`'s
variable (`auth.authErrOf`, `apply.AdminReq.result`): each one of the auth package's error
variables, which the apply package's facts tell apart from `ErrNoSpace` (`authErrsApart`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NoSpaceDeadOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.ApplyFnAdminL
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AuthDerive

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section iris
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **An admin operation's result's error** (`auth.adminOutX`) is one of the auth package's
(`authApplyErrIs`; kept). -/
theorem adminOutX_authApplyErrIs (M : auth.AuthMode) (Own : List auth.AuthState → IProp GF)
    (hs : List auth.AuthState) (R : auth.StepRel) (extra : auth.AuthErr → Prop) (err : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ⊢
      auth.adminOutX M Own hs R extra err -∗
      auth.adminOutX M Own hs R extra err ∗ authApplyErrIs err := by
  iintro #Hpkg H
  iunfold auth.adminOutX at H
  icases H with (⟨%e, %hx, Ho, #He⟩ | ⟨%st, %o, %hp, Hr⟩)
  · ihave #HA := apply.authErrOf_authApplyErrIs e err $$ [$Hpkg $He]
    isplitl [Ho]
    · iunfold auth.adminOutX; ileft; iexists e; iframe Ho He; ipureintro; exact hx
    · iexact HA
  · cases o with
    | err e =>
      simp only [auth.outResX]
      icases Hr with ⟨Ho, #He⟩
      ihave #HA := apply.authErrOf_authApplyErrIs e err $$ [$Hpkg $He]
      isplitl [Ho]
      · iunfold auth.adminOutX; iright; iexists st, (.err e)
        isplitr
        · ipureintro; exact hp
        simp only [auth.outResX]; iframe Ho He
      · iexact HA
    | same =>
      simp only [auth.outResX]
      icases Hr with ⟨Ho, %hn⟩
      subst hn
      isplitl [Ho]
      · iunfold auth.adminOutX; iright; iexists st, .same
        isplitr
        · ipureintro; exact hp
        simp only [auth.outResX]; iframe Ho
      · iapply authApplyErrIs_nil
    | next st' =>
      simp only [auth.outResX]
      icases Hr with ⟨Ho, %hn⟩
      subst hn
      isplitl [Ho]
      · iunfold auth.adminOutX; iright; iexists st, (.next st')
        isplitr
        · ipureintro; exact hp
        simp only [auth.outResX]; iframe Ho
      · iapply authApplyErrIs_nil

/-- **An admin request's result's error** (`apply.AdminReq.result`) is one of the auth package's
(kept). -/
theorem adminReqResult_authApplyErrIs (Own : auth.AuthNames → List auth.AuthState → IProp GF)
    (γa : auth.AuthNames) (M : auth.AuthMode) (hs : List auth.AuthState) (err : GoInterface)
    (ad : apply.AdminReq) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ⊢
      ad.result Own γa M hs err -∗ ad.result Own γa M hs err ∗ authApplyErrIs err := by
  iintro #Hpkg H
  cases ad with
  | userAdd n => iapply adminOutX_authApplyErrIs $$ Hpkg H
  | roleAdd n => iapply adminOutX_authApplyErrIs $$ Hpkg H
  | userGrantRole u ro => iapply adminOutX_authApplyErrIs $$ Hpkg H
  | roleGrantPermission n w => iapply adminOutX_authApplyErrIs $$ Hpkg H
  | authEnable =>
    simp only [apply.AdminReq.result]
    icases H with ⟨%en, #Hev, H⟩
    ihave ⟨H, #HA⟩ := adminOutX_authApplyErrIs _ _ _ _ _ err $$ Hpkg H
    isplitl [H]
    · iexists en; iframe Hev H
    · iexact HA

variable [errors_sem : _root_.Perennial.errors.Assumptions]

/-- **`apply.Apply`'s result on an admitted admin request with auth on** (given back, with the
admin outcome): `nil`, or its `Err` is not `ErrNoSpace`'s (`applyResultIs_notNoSpaceOn`'s
counterpart for the admin entries). -/
theorem applyResultIs_notNoSpaceAdmin (Own : auth.AuthNames → List auth.AuthState → IProp GF)
    (γa : auth.AuthNames) (M : auth.AuthMode) (hs : List auth.AuthState) (rq : apply.IRRModel)
    (log : mvcc.Log) (ar : Loc) (out : apply.ApplyOut) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗
      go_etcd_io.etcd.server.v3.etcdserver.apply.applyErrVars ⊢
      apply.applyResultIs rq true log ar out -∗ apply.adminOut Own γa M hs rq true ar out -∗
      apply.adminRejErr ar out -∗
      apply.applyResultIs rq true log ar out ∗ apply.adminOut Own γa M hs rq true ar out ∗
      (⌜ar = null⌝ ∨ ∃ err : GoInterface,
        structFieldRef go_etcd_io.etcd.server.v3.etcdserver.apply.Result go!"Err" ar ↦□ err ∗
        notNoSpaceErr err) := by
  iintro ⟨#Hpkg, #Hv⟩ H Hout #Hrej
  icases Hv with ⟨-, -, -, -, -, -, -, -, -, -, #Hap⟩
  cases out with
  | skipped =>
    simp only [apply.applyResultIs]
    icases H with %h
    iframe Hout
    isplitr
    · ipureintro; exact h
    ileft; ipureintro; exact h
  | rejected =>
    simp only [apply.adminRejErr]
    icases Hrej with ⟨%v, #Hvv, #HA⟩
    iframe H Hout
    iright
    iexists v.Err'
    iunfold authApplyErrIs at HA
    icases HA with ⟨-, #HV⟩
    isplitl []
    · iapply apply.result_err_ro; iexact Hvv
    iapply authErrVarIs_notNoSpace v.Err' $$ Hap HV
  | dispatched o skip =>
    simp only [apply.adminOut, apply.adminDone, ↓reduceIte]
    icases Hout with ⟨%v, %ad, %had, #Hvv, Hres⟩
    ihave ⟨Hres, #HA⟩ := adminReqResult_authApplyErrIs Own γa M hs v.Err' ad $$ Hpkg Hres
    iframe H
    isplitl [Hres]
    · iexists v, ad; iframe Hvv Hres; ipureintro; exact had
    iright
    iexists v.Err'
    iunfold authApplyErrIs at HA
    icases HA with ⟨-, #HV⟩
    isplitl []
    · iapply apply.result_err_ro; iexact Hvv
    iapply authErrVarIs_notNoSpace v.Err' $$ Hap HV

end iris

end EtcdGrove
end Perennial
