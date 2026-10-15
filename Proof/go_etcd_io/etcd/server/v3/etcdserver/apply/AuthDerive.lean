/-
The apply package's auth-store contract (`apply.isAuthStore`), its request-side part, of the real
auth store, from the auth store's proofs (2026-10-14, unit P2). Lean-first (no Rocq
counterpart); see `Proof/go_etcd_io/etcd/server/v3/auth/InvAuth.lean`.

`isAuthStore`'s permission clauses (`IsPutPermitted`, `IsRangePermitted`,
`IsDeleteRangePermitted`, `IsAdminPermitted`) and `IsAuthEnabled` take no resource (`{{ True }}`
and the caller's slices), but the real methods read-lock `enabledMu` and `rangePermCacheMu` and
the backend's read transaction, each an `RWMutex` whose readers Perennial bounds (a reader slot,
`sync.ownRWMutex`, per concurrent reader): not derivable as stated. `isAuthStorePerms st RD`
states them with a reader resource `RD` the caller holds and gets back (the shape of the request
path's `waitOk w RD`), and the permission checks with the key below `2^63 - 1`
(`NewBytesAffinePoint`'s `make([]byte, len(key)+1)`: no slice in memory reaches it, but the
model's `make` does not assume it); `isAuthStorePerms_of_authInv` derives it of the real store,
with `RD := auth.authRd st R`. `Revision` is derived as `isAuthStore` states it
(`authRevision_of_authInv`). The store's errors are the package's `errors.New` variables
(`auth.authErrVar`, the shape of `errVarLeaf`): `applyErrIs` (`authErrIs_applyErrIs`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Contracts
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__IsPutPermitted
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__IsRangePermitted
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__IsDeleteRangePermitted
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__IsAdminPermitted
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__IsAuthEnabled
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__Revision

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apply

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3 go_etcd_io.etcd.api.v3

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`isAuthStore`'s clauses assumed of the real store** (see the file header): `HasRole` (it
reads `u.Roles` of an axiomatized `authpb.User`) and the admin requests, each a `csContract`
(`AuthEnable`, `AuthDisable`, `Authenticate`, the user and role requests: their write side is not
translated). -/
def isAuthStoreAdmin (st : GoInterface) (P : IProp GF) (f : val) : IProp GF :=
  iprop(∃ ai : GoInterfaceOk, ⌜st = GoInterface.ok ai⌝ ∗
    □ (∀ (u r : GoString),
      {{ True }} (App (App (Val #(methods ai.ty go!"HasRole" ai.v)) (Val #u)) (Val #r))
      {{ (b : Bool), RET #b; True }}) ∗
    □ (∀ (Pre Q Post : IProp GF),
      {{ mvcc.csContract P f Pre Q Post }} (App (Val #(methods ai.ty go!"AuthEnable" ai.v)) (Val #()))
      {{ (err : GoInterface), RET #err; (Post ∨ Pre) ∗ applyErrIs err }}) ∗
    □ (∀ (Pre Q Post : IProp GF),
      {{ mvcc.csContract P f Pre Q Post }} (App (Val #(methods ai.ty go!"AuthDisable" ai.v)) (Val #()))
      {{ RET #(); Post ∨ Pre }}) ∗
    □ (∀ (ctx : GoInterface) (name pw : GoString) (Pre Q Post : IProp GF),
      {{ mvcc.csContract P f Pre Q Post }}
        (App (App (App (Val #(methods ai.ty go!"Authenticate" ai.v)) (Val #ctx)) (Val #name))
          (Val #pw))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); (Post ∨ Pre) ∗
          respHdrOk etcdserverpb.AuthenticateResponse resp ∗ applyErrIs err }}) ∗
    authReqContract ai go!"UserAdd" etcdserverpb.AuthUserAddResponse P f ∗
    authReqContract ai go!"UserDelete" etcdserverpb.AuthUserDeleteResponse P f ∗
    authReqContract ai go!"UserChangePassword" etcdserverpb.AuthUserChangePasswordResponse P f ∗
    authReqContract ai go!"UserGrantRole" etcdserverpb.AuthUserGrantRoleResponse P f ∗
    authReqContract ai go!"UserGet" etcdserverpb.AuthUserGetResponse P f ∗
    authReqContract ai go!"UserRevokeRole" etcdserverpb.AuthUserRevokeRoleResponse P f ∗
    authReqContract ai go!"RoleAdd" etcdserverpb.AuthRoleAddResponse P f ∗
    authReqContract ai go!"RoleGrantPermission" etcdserverpb.AuthRoleGrantPermissionResponse P f ∗
    authReqContract ai go!"RoleGet" etcdserverpb.AuthRoleGetResponse P f ∗
    authReqContract ai go!"RoleRevokePermission" etcdserverpb.AuthRoleRevokePermissionResponse P f ∗
    authReqContract ai go!"RoleDelete" etcdserverpb.AuthRoleDeleteResponse P f ∗
    authReqContract ai go!"UserList" etcdserverpb.AuthUserListResponse P f ∗
    authReqContract ai go!"RoleList" etcdserverpb.AuthRoleListResponse P f)

instance isAuthStoreAdmin_persistent (st : GoInterface) (P : IProp GF) (f : val) :
    Persistent (isAuthStoreAdmin st P f) := by
  unfold isAuthStoreAdmin authReqContract; infer_instance

end defs

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- An auth-store error is one `errors.Is` can take. -/
theorem authErrIs_applyErrIs (err : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗
      auth.authErrIs err ⊢ applyErrIs err := by
  iintro ⟨#Hpkg, #Herr⟩
  ihave Hai : (go_etcd_io.etcd.server.v3.auth.authInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hai with ⟨#HUE, #HUNF, #HPD, #HOR, #HIT, -, -⟩
  iunfold auth.authErrIs at Herr
  icases Herr with (%Hnil | ⟨%g, %e, %Hg, #Hge, %He⟩)
  · subst Hnil; iapply applyErrIs_nil
  ihave #Hv : errVarLeaf (GF := GF) g $$ []
  · rcases Hg with rfl | rfl | rfl | rfl | rfl
    · iunfold go_etcd_io.etcd.server.v3.auth.authErrVar at HUE
      iunfold errVarLeaf; iunfold errLeaf; iunfold errMsgOk; iexact HUE
    · iunfold go_etcd_io.etcd.server.v3.auth.authErrVar at HUNF
      iunfold errVarLeaf; iunfold errLeaf; iunfold errMsgOk; iexact HUNF
    · iunfold go_etcd_io.etcd.server.v3.auth.authErrVar at HPD
      iunfold errVarLeaf; iunfold errLeaf; iunfold errMsgOk; iexact HPD
    · iunfold go_etcd_io.etcd.server.v3.auth.authErrVar at HOR
      iunfold errVarLeaf; iunfold errLeaf; iunfold errMsgOk; iexact HOR
    · iunfold go_etcd_io.etcd.server.v3.auth.authErrVar at HIT
      iunfold errVarLeaf; iunfold errLeaf; iunfold errMsgOk; iexact HIT
  iapply errVar_applyErrIs g err $$ Hv
  iexists e; iframe Hge; ipureintro; exact He

/-- **`isAuthStore`'s `Revision` clause, of the real store** (as the contract states it). -/
theorem authRevision_of_authInv
    (hRev : auth.authStore.Revision.spec (GF := GF) (hG := hG))
    (st : Loc) (R : IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ auth.authInv st R ⊢
      □ ({{ True }} (App (Val #(methods (go.GoType.PointerType auth.authStore.ty) go!"Revision"
          #st)) (Val #()))
        {{ (x : w64), RET #x; True }}) := by
  iintro ⟨#Hpkg, #Hinv⟩
  iintro !> %Φ !> - HΦ
  iapply (hRev st R) $$ [] HΦ
  iframe Hpkg Hinv

/-- **The apply package's `isAuthStore`, of the real store** at `st` (`auth.authInv st R`),
with the reader resource `auth.authRd st R`: the permission checks, `IsAdminPermitted`,
`IsAuthEnabled` and `Revision` from the store's proofs; `HasRole` and the admin requests from
the contract `isAuthStoreAdmin` (see the file header). -/
theorem isAuthStore_of_authInv
    (hPut : auth.authStore.IsPutPermitted.spec (GF := GF) (hG := hG))
    (hRange : auth.authStore.IsRangePermitted.spec (GF := GF) (hG := hG))
    (hDel : auth.authStore.IsDeleteRangePermitted.spec (GF := GF) (hG := hG))
    (hAdmin : auth.authStore.IsAdminPermitted.spec (GF := GF) (hG := hG))
    (hEn : auth.authStore.IsAuthEnabled.spec (GF := GF) (hG := hG))
    (hRev : auth.authStore.Revision.spec (GF := GF) (hG := hG))
    (st : Loc) (R : IProp GF) (P : IProp GF) (f : val) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ auth.authInv st R ∗
      isAuthStoreAdmin (auth.authIface st) P f ⊢
      isAuthStore (auth.authIface st) P f (auth.authRd st R) := by
  iintro ⟨#Hpkg, #Hinv, #Hadm⟩
  iunfold isAuthStoreAdmin at Hadm
  icases Hadm with ⟨%ai', %Hai', #HHas, #HAE, #HAD, #HAu, #H1, #H2, #H3, #H4, #H5, #H6, #H7, #H8,
    #H9, #H10, #H11, #H12, #H13⟩
  have Hai'' : ai' = interface.mk (go.GoType.PointerType auth.authStore.ty) #st := by
    unfold auth.authIface at Hai'; cases Hai'; rfl
  subst Hai''
  iunfold isAuthStore
  iexists (interface.mk (go.GoType.PointerType auth.authStore.ty) #st)
  isplitr
  · ipureintro; rfl
  isplitr
  · iunfold permCheck2
    iintro !> %a %info %dq %key %k %dk %Φ !> ⟨Ha, Hk, Hrd, %Hlen⟩ HΦ
    iapply (hPut st R a info dq key k dk) $$ [Ha Hk Hrd]
    · iframe; iframe #; ipureintro; exact Hlen
    iintro !> %err ⟨Hrd, Ha, Hk, #Herr⟩
    iapply HΦ
    iframe
    iapply authErrIs_applyErrIs err $$ [$Hpkg $Herr]
  isplitr
  · iunfold permCheck3
    iintro !> %a %info %dq %key %re %k %e %dk %de %Φ !> ⟨Ha, Hk, He, Hrd, %Hlen⟩ HΦ
    iapply (hRange st R a info dq key re k e dk de) $$ [Ha Hk He Hrd]
    · iframe; iframe #; ipureintro; exact Hlen
    iintro !> %err ⟨Hrd, Ha, Hk, He, #Herr⟩
    iapply HΦ
    iframe
    iapply authErrIs_applyErrIs err $$ [$Hpkg $Herr]
  isplitr
  · iunfold permCheck3
    iintro !> %a %info %dq %key %re %k %e %dk %de %Φ !> ⟨Ha, Hk, He, Hrd, %Hlen⟩ HΦ
    iapply (hDel st R a info dq key re k e dk de) $$ [Ha Hk He Hrd]
    · iframe; iframe #; ipureintro; exact Hlen
    iintro !> %err ⟨Hrd, Ha, Hk, He, #Herr⟩
    iapply HΦ
    iframe
    iapply authErrIs_applyErrIs err $$ [$Hpkg $Herr]
  isplitr
  · iintro !> %a %info %dq %Φ !> ⟨Ha, Hrd⟩ HΦ
    iapply (hAdmin st R a info dq) $$ [Ha Hrd]
    · iframe; iframe #
    iintro !> %err ⟨Hrd, Ha, #Herr⟩
    iapply HΦ
    iframe
    iapply authErrIs_applyErrIs err $$ [$Hpkg $Herr]
  iframe HHas
  isplitr
  · iintro !> %Φ !> Hrd HΦ
    iunfold auth.authRd at Hrd
    icases Hrd with ⟨Hen, Hca, HR⟩
    iapply (hEn st R) $$ [Hen]
    · iframe; iframe #
    iintro !> %b Hen
    iapply HΦ
    iunfold auth.authRd
    iframe
  isplitr
  · iapply authRevision_of_authInv hRev st R $$ [$Hpkg $Hinv]
  iframe #

end proof

end apply
end EtcdGrove
end Perennial
