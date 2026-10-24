/-
**The auth store's admin side as model steps, at the apply layer** (the auth plan's S4, its
apply part, 2026-10-24; `notes/decisions.md`, "S4's apply part"). Lean-first (no Rocq
counterpart).

S4 proved the store's admin operations (`authStore.AuthEnable`, `AuthDisable`, `UserAdd`,
`UserDelete`, `UserChangePassword`, `RoleAdd`) to perform a step of the model's state
(`auth/Steps.lean`: `adminOut`, the history `authHist` grown by the step's state, or the model's
refusal), from the admin side's authority (`auth.authOwn M hs`) and the store's write resource
(`auth.authWR st M P f T`). The apply package's contract `isAuthStore` keeps its admin clauses as
critical-section contracts (`authReqContract`, `isAuthStoreAdmin`: some error, the write right
`RW` given back), which the server's environment instantiates with `RW = False` (its workload
admits no auth request: `AEnv.RW`).

**`isAuthSteps st P f M W`** states the six proved operations of the auth store `st` as the
store's specs state them, with the store's write resource abstracted as `W` (the real store's
`auth.authWR st M P f T`: `isAuthSteps_of_authInv`) and the errors the apply layer's
(`applyErrIs`, from the package's error variables). It is a separate persistent fact rather than
clauses appended to `isAuthStore`: the admin side's authority and `W` are the apply thread's own
resources (the apply thread is the store's only writer; raft applies serially), which no
environment of a closed theorem holds yet (the server's admits no auth request), and the
contract's 51 users keep their shape.

**The apply layer's admin requests** (`applierV3backend_UserAdd_step`, ...): a second triple of
`applierV3backend.X` (the first, `applierV3backend.X.spec`, is the contract's, which the dispatch
proofs use), from the backend's options' `isAuthSteps` (`backendAuthSteps E p W`), the authority
at `hs` and `W`: the request performed the model's step on the latest recorded state for the
request's arguments, or the model's refusal (`adminOut`), the response's header set. With A3's
`adminPass` (the admin check passed for the request's principal before the backend is reached),
an applied admin request in the mode `on γa` is a step of the history made by an admin.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Chain
public import Proof.go_etcd_io.etcd.server.v3.auth.Steps
public import Proof.go_etcd_io.etcd.server.v3.auth.Requests
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__AuthEnable
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__AuthDisable
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__UserAdd
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__UserDelete
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__UserChangePassword
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__RoleAdd
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__newHeader

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apply

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3 go_etcd_io.etcd.server.v3.etcdserver.apply
  go_etcd_io.etcd.api.v3

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The auth store `st`'s six proved admin operations as model steps** (see the file header):
each from the authority `auth.authOwn M hs` and the write resource `W`, under the batch lock's
critical-section contract (`P`, `f`), with S4's premises (`stepOk`: the revision and the cache's
trees; a new record's name within bbolt's key bound); each gives back `W`, an error the apply
layer can take, the response (`auth.respOk`), and the step's result (`auth.adminOut`: the
authority after the step, or a refusal). `AuthEnable`, `AuthDisable` and `UserDelete` are
relative to the flag the store read (`en`, its verdict `auth.enabledVerdict`). -/
def isAuthSteps (st : GoInterface) (P : IProp GF) (f : val) (M : auth.AuthMode) (W : IProp GF) :
    IProp GF :=
  iprop(∃ ai : GoInterfaceOk, ⌜st = GoInterface.ok ai⌝ ∗
    □ (∀ (hs : List auth.AuthState) (Pre Q Post : IProp GF),
      {{ ⌜M.isOn = true⌝ ∗ auth.authOwn M hs ∗ W ∗ mvcc.csContract P f Pre Q Post ∗
          ⌜∀ en : Bool, auth.stepOk M hs (auth.stepOf (auth.authEnableF en))⌝ }}
        (App (Val #(methods ai.ty go!"AuthEnable" ai.v)) (Val #()))
      {{ (err : GoInterface), RET #err; (Post ∨ Pre) ∗ W ∗ applyErrIs err ∗
          ∃ en : Bool, auth.enabledVerdict M en ∗
            auth.adminOut M hs (auth.stepOf (auth.authEnableF en)) auth.noExtra err }}) ∗
    □ (∀ (hs : List auth.AuthState) (Pre Q Post : IProp GF),
      {{ auth.authOwn M hs ∗ W ∗ mvcc.csContract P f Pre Q Post ∗
          ⌜∀ en : Bool, auth.stepOk M hs (auth.stepOf (auth.authDisableF en))⌝ }}
        (App (Val #(methods ai.ty go!"AuthDisable" ai.v)) (Val #()))
      {{ RET #(); (Post ∨ Pre) ∗ W ∗
          ∃ en : Bool, auth.enabledVerdict M en ∗
            auth.adminOut M hs (auth.stepOf (auth.authDisableF en)) auth.noExtra GoInterface.nil }}) ∗
    □ (∀ (hs : List auth.AuthState) (Pre Q Post : IProp GF) (r : Loc) (name : GoString),
      {{ auth.userAddReqIs r name ∗ ⌜name.length ≤ backend.maxKeySize⌝ ∗ auth.authOwn M hs ∗ W ∗
          mvcc.csContract P f Pre Q Post ∗ ⌜auth.stepOk M hs (auth.stepOf (auth.userAddF name))⌝ }}
        (App (Val #(methods ai.ty go!"UserAdd" ai.v)) (Val #r))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); (Post ∨ Pre) ∗ W ∗
          applyErrIs err ∗ auth.respOk etcdserverpb.AuthUserAddResponse resp err ∗
          auth.adminOut M hs (auth.stepOf (auth.userAddF name))
            (fun e => e = .noPasswordUser) err }}) ∗
    □ (∀ (hs : List auth.AuthState) (Pre Q Post : IProp GF) (r : Loc) (name : GoString),
      {{ auth.userDeleteReqIs r name ∗ auth.authOwn M hs ∗ W ∗ mvcc.csContract P f Pre Q Post ∗
          ⌜∀ en : Bool, auth.stepOk M hs (auth.stepOf (auth.userDeleteF en name))⌝ }}
        (App (Val #(methods ai.ty go!"UserDelete" ai.v)) (Val #r))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); (Post ∨ Pre) ∗ W ∗
          applyErrIs err ∗ auth.respOk etcdserverpb.AuthUserDeleteResponse resp err ∗
          ∃ en : Bool, auth.enabledVerdict M en ∗
            auth.adminOut M hs (auth.stepOf (auth.userDeleteF en name)) auth.noExtra err }}) ∗
    □ (∀ (hs : List auth.AuthState) (Pre Q Post : IProp GF) (r : Loc) (name : GoString),
      {{ auth.userChangePasswordReqIs r name ∗ ⌜name.length ≤ backend.maxKeySize⌝ ∗
          auth.authOwn M hs ∗ W ∗ mvcc.csContract P f Pre Q Post ∗
          ⌜auth.stepOk M hs (auth.stepOf (auth.userChangePasswordF name))⌝ }}
        (App (Val #(methods ai.ty go!"UserChangePassword" ai.v)) (Val #r))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); (Post ∨ Pre) ∗ W ∗
          applyErrIs err ∗ auth.respOk etcdserverpb.AuthUserChangePasswordResponse resp err ∗
          auth.adminOut M hs (auth.stepOf (auth.userChangePasswordF name))
            (fun e => e = .noPasswordUser) err }}) ∗
    □ (∀ (hs : List auth.AuthState) (Pre Q Post : IProp GF) (r : Loc) (name : GoString),
      {{ auth.roleAddReqIs r name ∗ ⌜name.length ≤ backend.maxKeySize⌝ ∗ auth.authOwn M hs ∗ W ∗
          mvcc.csContract P f Pre Q Post ∗ ⌜auth.stepOk M hs (auth.stepOf (auth.roleAddF name))⌝ }}
        (App (Val #(methods ai.ty go!"RoleAdd" ai.v)) (Val #r))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); (Post ∨ Pre) ∗ W ∗
          applyErrIs err ∗ auth.respOk etcdserverpb.AuthRoleAddResponse resp err ∗
          auth.adminOut M hs (auth.stepOf (auth.roleAddF name)) auth.noExtra err }}))

instance isAuthSteps_persistent (st : GoInterface) (P : IProp GF) (f : val) (M : auth.AuthMode)
    (W : IProp GF) : Persistent (isAuthSteps st P f M W) := by
  unfold isAuthSteps; infer_instance

/-- **The `*applierV3backend` `p`'s auth store's admin steps** (see the file header): its options,
read-only, whose auth store has `isAuthSteps` with the environment's lock, hook and mode. -/
def backendAuthSteps (E : AEnv GF) (p : Loc) (W : IProp GF) : IProp GF :=
  iprop(∃ opts : ApplierOptions, structFieldRef applierV3backend go!"options" p ↦□ opts ∗
    isAuthSteps opts.AuthStore' E.P E.f E.authMode W)

instance backendAuthSteps_persistent (E : AEnv GF) (p : Loc) (W : IProp GF) :
    Persistent (backendAuthSteps E p W) := by
  unfold backendAuthSteps; infer_instance

end defs

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- Every model error's variable is one of the auth package's facts. -/
theorem authErrVar_of_pkg (e : auth.AuthErr) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ⊢
      go_etcd_io.etcd.server.v3.auth.authErrVar e.var := by
  cases e <;> simp only [auth.AuthErr.var] <;> iintro #Hpkg <;>
    ihave Hai : (go_etcd_io.etcd.server.v3.auth.authInit : IProp GF) $$ [] <;>
    (try iapply isPkgInit_access $$ Hpkg) <;>
    icases Hai with ⟨#V1, #V2, #V3, #V4, #V5, -, -, #V6, #V7, #V8, #V9, #V10, #V11, #V12, #V13,
      #V14, #V15, #V16⟩ <;>
    first | iexact V1 | iexact V2 | iexact V3 | iexact V4 | iexact V5 | iexact V6 | iexact V7 | iexact V8 | iexact V9 | iexact V10 | iexact V11 | iexact V12 | iexact V13 | iexact V14 | iexact V15 | iexact V16

theorem outRes_err (M : auth.AuthMode) (hs : List auth.AuthState) (e : auth.AuthErr)
    (err : GoInterface) :
    auth.outRes (GF := GF) M hs (.err e) err = iprop(auth.authOwn M hs ∗ auth.authErrOf e err) := rfl

theorem outRes_same (M : auth.AuthMode) (hs : List auth.AuthState) (err : GoInterface) :
    auth.outRes (GF := GF) M hs .same err = iprop(auth.authOwn M hs ∗ ⌜err = GoInterface.nil⌝) := rfl

theorem outRes_next (M : auth.AuthMode) (hs : List auth.AuthState) (st' : auth.AuthState)
    (err : GoInterface) :
    auth.outRes (GF := GF) M hs (.next st') err =
      iprop(auth.authOwn M (hs ++ [st']) ∗ ⌜err = GoInterface.nil⌝) := rfl

/-- A model error the store returns is an error the apply layer can take. -/
theorem authErrOf_applyErrIs (e : auth.AuthErr) (err : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ auth.authErrOf e err ⊢
      applyErrIs err := by
  iintro ⟨#Hpkg, #He⟩
  ihave #Hv := authErrVar_of_pkg e $$ Hpkg
  ihave #Hl : errVarLeaf (GF := GF) e.var $$ []
  · iunfold go_etcd_io.etcd.server.v3.auth.authErrVar at Hv
    iunfold errVarLeaf; iunfold errLeaf; iunfold errMsgOk; iexact Hv
  iunfold auth.authErrOf at He
  iapply errVar_applyErrIs e.var err $$ Hl
  iexact He

/-- **An admin operation's result's error** is one the apply layer can take (the result kept). -/
theorem adminOut_applyErrIs (M : auth.AuthMode) (hs : List auth.AuthState) (R : auth.StepRel)
    (extra : auth.AuthErr → Prop) (err : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗
      auth.adminOut M hs R extra err ⊢ auth.adminOut M hs R extra err ∗ applyErrIs err := by
  iintro ⟨#Hpkg, H⟩
  iunfold auth.adminOut at H
  icases H with (⟨%e, %hx, Ho, #He⟩ | ⟨%s, %o, %ho, Hr⟩)
  · ihave #Ha := authErrOf_applyErrIs e err $$ [$Hpkg $He]
    isplitl
    · iunfold auth.adminOut
      ileft
      iexists e
      isplitr
      · ipureintro; exact hx
      iframe Ho He
    iexact Ha
  · cases o with
    | err e =>
      rw [outRes_err] at *
      icases Hr with ⟨Ho, #He⟩
      ihave #Ha := authErrOf_applyErrIs e err $$ [$Hpkg $He]
      isplitl
      · iunfold auth.adminOut
        iright
        iexists s, (auth.Outcome.err e)
        isplitr
        · ipureintro; exact ho
        rw [outRes_err]
        iframe Ho He
      iexact Ha
    | same =>
      rw [outRes_same] at *
      icases Hr with ⟨Ho, %Hn⟩
      subst Hn
      isplitl
      · iunfold auth.adminOut
        iright
        iexists s, auth.Outcome.same
        isplitr
        · ipureintro; exact ho
        rw [outRes_same]
        iframe Ho
        ipureintro; rfl
      iapply applyErrIs_nil
    | next st' =>
      rw [outRes_next] at *
      icases Hr with ⟨Ho, %Hn⟩
      subst Hn
      isplitl
      · iunfold auth.adminOut
        iright
        iexists s, (auth.Outcome.next st')
        isplitr
        · ipureintro; exact ho
        rw [outRes_next]
        iframe Ho
        ipureintro; rfl
      iapply applyErrIs_nil

/-- **`isAuthSteps` of the real store** at `st` (`auth.authInv st R M`), with its write resource
`auth.authWR st M P f T`, from S4's six specs. -/
theorem isAuthSteps_of_authInv
    (hEnable : auth.authStore.AuthEnable.spec (GF := GF) (hG := hG))
    (hDisable : auth.authStore.AuthDisable.spec (GF := GF) (hG := hG))
    (hUserAdd : auth.authStore.UserAdd.spec (GF := GF) (hG := hG))
    (hUserDelete : auth.authStore.UserDelete.spec (GF := GF) (hG := hG))
    (hUserChangePassword : auth.authStore.UserChangePassword.spec (GF := GF) (hG := hG))
    (hRoleAdd : auth.authStore.RoleAdd.spec (GF := GF) (hG := hG))
    (st : Loc) (R : IProp GF) (M : auth.AuthMode) (P : IProp GF) (f : val) (T : IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ auth.authInv st R M ⊢
      isAuthSteps (auth.authIface st) P f M (auth.authWR st M P f T) := by
  iintro ⟨#Hpkg, #Hinv⟩
  iunfold isAuthSteps
  iexists (interface.mk (go.GoType.PointerType auth.authStore.ty) #st)
  isplitr
  · ipureintro; rfl
  isplitr
  · iintro !> %hs %Pre %Q %Post %Φ !> ⟨%Hon, Ho, HW, Hcs, %Hok⟩ HΦ
    iapply (hEnable st R M P f T hs Pre Q Post) $$ [Ho HW Hcs]
    · iframe; iframe #; isplitr
      · ipureintro; exact Hon
      ipureintro; exact Hok
    iintro !> %err ⟨HPP, HW, %en, #Hv, Hout⟩
    icases adminOut_applyErrIs M hs _ _ err $$ [$Hpkg $Hout] with ⟨Hout, #Ha⟩
    iapply HΦ
    iframe
    iframe #
  isplitr
  · iintro !> %hs %Pre %Q %Post %Φ !> ⟨Ho, HW, Hcs, %Hok⟩ HΦ
    iapply (hDisable st R M P f T hs Pre Q Post) $$ [Ho HW Hcs]
    · iframe; iframe #; ipureintro; exact Hok
    iintro !> ⟨HPP, HW, %en, #Hv, Hout⟩
    iapply HΦ
    iframe
    iframe #
  isplitr
  · iintro !> %hs %Pre %Q %Post %r %name %Φ !> ⟨#Hr, %Hn, Ho, HW, Hcs, %Hok⟩ HΦ
    iapply (hUserAdd st R M P f T hs Pre Q Post r name) $$ [Ho HW Hcs]
    · iframe; iframe #; isplitr
      · ipureintro; exact Hn
      ipureintro; exact Hok
    iintro !> %resp %err ⟨HPP, HW, Hresp, Hout⟩
    icases adminOut_applyErrIs M hs _ _ err $$ [$Hpkg $Hout] with ⟨Hout, #Ha⟩
    iapply HΦ
    iframe
    iframe #
  isplitr
  · iintro !> %hs %Pre %Q %Post %r %name %Φ !> ⟨#Hr, Ho, HW, Hcs, %Hok⟩ HΦ
    iapply (hUserDelete st R M P f T hs Pre Q Post r name) $$ [Ho HW Hcs]
    · iframe; iframe #; ipureintro; exact Hok
    iintro !> %resp %err ⟨HPP, HW, Hresp, %en, #Hv, Hout⟩
    icases adminOut_applyErrIs M hs _ _ err $$ [$Hpkg $Hout] with ⟨Hout, #Ha⟩
    iapply HΦ
    iframe
    iframe #
  isplitr
  · iintro !> %hs %Pre %Q %Post %r %name %Φ !> ⟨#Hr, %Hn, Ho, HW, Hcs, %Hok⟩ HΦ
    iapply (hUserChangePassword st R M P f T hs Pre Q Post r name) $$ [Ho HW Hcs]
    · iframe; iframe #; isplitr
      · ipureintro; exact Hn
      ipureintro; exact Hok
    iintro !> %resp %err ⟨HPP, HW, Hresp, Hout⟩
    icases adminOut_applyErrIs M hs _ _ err $$ [$Hpkg $Hout] with ⟨Hout, #Ha⟩
    iapply HΦ
    iframe
    iframe #
  · iintro !> %hs %Pre %Q %Post %r %name %Φ !> ⟨#Hr, %Hn, Ho, HW, Hcs, %Hok⟩ HΦ
    iapply (hRoleAdd st R M P f T hs Pre Q Post r name) $$ [Ho HW Hcs]
    · iframe; iframe #; isplitr
      · ipureintro; exact Hn
      ipureintro; exact Hok
    iintro !> %resp %err ⟨HPP, HW, Hresp, Hout⟩
    icases adminOut_applyErrIs M hs _ _ err $$ [$Hpkg $Hout] with ⟨Hout, #Ha⟩
    iapply HΦ
    iframe
    iframe #

end proof

section stepSpecs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`a.UserAdd(r)` performs the model's step** (see the file header): the store's `UserAdd`
from the authority at `hs` and the write resource `W` (`isAuthSteps`), the response's header set
if there is a response. -/
abbrev applierV3backend.UserAdd.stepSpec : Prop :=
  ∀ (E : AEnv GF) (W : IProp GF) (p r : Loc) (log : mvcc.Log) (Pre Q Post : IProp GF)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (hs : List auth.AuthState) (name : GoString),
    name.length ≤ backend.maxKeySize →
    auth.stepOk E.authMode hs (auth.stepOf (auth.userAddF name)) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
        apply.backendIs E p ∗ backendAuthSteps E p W ∗ auth.userAddReqIs r name ∗
        auth.authOwn E.authMode hs ∗ W ∗
        apply.mPre E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) info log Pre Q Post }}
      (App (Val (p @!! go.GoType.PointerType applierV3backend.ty @!! go!"UserAdd")) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      apply.mPost E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) log Pre Post ∗
      applyErrIs err ∗ W ∗
      auth.adminOut E.authMode hs (auth.stepOf (auth.userAddF name)) (fun e => e = .noPasswordUser) err }}

/-- **`a.UserDelete(r)` performs the model's step** (see the file header): the store's `UserDelete`
from the authority at `hs` and the write resource `W` (`isAuthSteps`), the response's header set
if there is a response. -/
abbrev applierV3backend.UserDelete.stepSpec : Prop :=
  ∀ (E : AEnv GF) (W : IProp GF) (p r : Loc) (log : mvcc.Log) (Pre Q Post : IProp GF)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (hs : List auth.AuthState) (name : GoString),
    (∀ en : Bool, auth.stepOk E.authMode hs (auth.stepOf (auth.userDeleteF en name))) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
        apply.backendIs E p ∗ backendAuthSteps E p W ∗ auth.userDeleteReqIs r name ∗
        auth.authOwn E.authMode hs ∗ W ∗
        apply.mPre E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) info log Pre Q Post }}
      (App (Val (p @!! go.GoType.PointerType applierV3backend.ty @!! go!"UserDelete")) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      apply.mPost E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) log Pre Post ∗
      applyErrIs err ∗ W ∗
      ∃ en : Bool, auth.enabledVerdict E.authMode en ∗
        auth.adminOut E.authMode hs (auth.stepOf (auth.userDeleteF en name)) auth.noExtra err }}

/-- **`a.UserChangePassword(r)` performs the model's step** (see the file header): the store's `UserChangePassword`
from the authority at `hs` and the write resource `W` (`isAuthSteps`), the response's header set
if there is a response. -/
abbrev applierV3backend.UserChangePassword.stepSpec : Prop :=
  ∀ (E : AEnv GF) (W : IProp GF) (p r : Loc) (log : mvcc.Log) (Pre Q Post : IProp GF)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (hs : List auth.AuthState) (name : GoString),
    name.length ≤ backend.maxKeySize →
    auth.stepOk E.authMode hs (auth.stepOf (auth.userChangePasswordF name)) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
        apply.backendIs E p ∗ backendAuthSteps E p W ∗ auth.userChangePasswordReqIs r name ∗
        auth.authOwn E.authMode hs ∗ W ∗
        apply.mPre E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) info log Pre Q Post }}
      (App (Val (p @!! go.GoType.PointerType applierV3backend.ty @!! go!"UserChangePassword")) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      apply.mPost E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) log Pre Post ∗
      applyErrIs err ∗ W ∗
      auth.adminOut E.authMode hs (auth.stepOf (auth.userChangePasswordF name)) (fun e => e = .noPasswordUser) err }}

/-- **`a.RoleAdd(r)` performs the model's step** (see the file header): the store's `RoleAdd`
from the authority at `hs` and the write resource `W` (`isAuthSteps`), the response's header set
if there is a response. -/
abbrev applierV3backend.RoleAdd.stepSpec : Prop :=
  ∀ (E : AEnv GF) (W : IProp GF) (p r : Loc) (log : mvcc.Log) (Pre Q Post : IProp GF)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (hs : List auth.AuthState) (name : GoString),
    name.length ≤ backend.maxKeySize →
    auth.stepOk E.authMode hs (auth.stepOf (auth.roleAddF name)) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
        apply.backendIs E p ∗ backendAuthSteps E p W ∗ auth.roleAddReqIs r name ∗
        auth.authOwn E.authMode hs ∗ W ∗
        apply.mPre E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) info log Pre Q Post }}
      (App (Val (p @!! go.GoType.PointerType applierV3backend.ty @!! go!"RoleAdd")) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      apply.mPost E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) log Pre Post ∗
      applyErrIs err ∗ W ∗
      auth.adminOut E.authMode hs (auth.stepOf (auth.roleAddF name)) auth.noExtra err }}

/-- **`a.AuthEnable()` performs the model's step** (see the file header; the mode on, as the
contract's clause): the store's `AuthEnable`, then a fresh response with the header. -/
abbrev applierV3backend.AuthEnable.stepSpec : Prop :=
  ∀ (E : AEnv GF) (W : IProp GF) (p : Loc) (log : mvcc.Log) (Pre Q Post : IProp GF)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (hs : List auth.AuthState),
    E.authMode.isOn = true →
    (∀ en : Bool, auth.stepOk E.authMode hs (auth.stepOf (auth.authEnableF en))) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
        apply.backendIs E p ∗ backendAuthSteps E p W ∗ auth.authOwn E.authMode hs ∗ W ∗
        apply.mPre E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) info log Pre Q Post }}
      (App (Val (p @!! go.GoType.PointerType applierV3backend.ty @!! go!"AuthEnable")) (Val #()))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      apply.mPost E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) log Pre Post ∗
      applyErrIs err ∗ W ∗
      ∃ en : Bool, auth.enabledVerdict E.authMode en ∗
        auth.adminOut E.authMode hs (auth.stepOf (auth.authEnableF en)) auth.noExtra err }}

/-- **`a.AuthDisable()` performs the model's step** (see the file header): the store's
`AuthDisable`, then a fresh response with the header, and no error. -/
abbrev applierV3backend.AuthDisable.stepSpec : Prop :=
  ∀ (E : AEnv GF) (W : IProp GF) (p : Loc) (log : mvcc.Log) (Pre Q Post : IProp GF)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (hs : List auth.AuthState),
    (∀ en : Bool, auth.stepOk E.authMode hs (auth.stepOf (auth.authDisableF en))) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
        apply.backendIs E p ∗ backendAuthSteps E p W ∗ auth.authOwn E.authMode hs ∗ W ∗
        apply.mPre E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) info log Pre Q Post }}
      (App (Val (p @!! go.GoType.PointerType applierV3backend.ty @!! go!"AuthDisable")) (Val #()))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      apply.mPost E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) log Pre Post ∗
      ⌜err = GoInterface.nil⌝ ∗ W ∗
      ∃ en : Bool, auth.enabledVerdict E.authMode en ∗
        auth.adminOut E.authMode hs (auth.stepOf (auth.authDisableF en)) auth.noExtra
          GoInterface.nil }}

end stepSpecs

section applier
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

theorem applierV3backend.UserAdd.wp_step
    (hHdr : apply.applierV3backend.newHeader.spec (GF := GF) (hG := hG)) :
    applierV3backend.UserAdd.stepSpec (GF := GF) (hG := hG) := by
  intro E W p r log Pre Q Post info hs name hn hok
  wp_start as ⟨#Hb, #Hs, #Hr, Ho, HW, Hpre⟩
  iunfold apply.mPre at Hpre
  icases Hpre with ⟨Hkv, Hres, Hcs⟩
  iunfold apply.kvOwn at Hkv
  icases Hkv with ⟨Hrd, Hsw, Hknown, Hard⟩
  ihave #Hs' := Hs
  iunfold apply.backendAuthSteps at Hs'
  icases Hs' with ⟨%opts, #Hopts, #Hst⟩
  iunfold apply.isAuthSteps at Hst
  icases Hst with ⟨%ai, %Hai, -, -, #HM, -, -, -⟩
  iStructNamed Hopts
  wp_auto
  rw [Hai]
  wp_apply HM $$ %hs %Pre %Q %Post %r %name [$Ho $HW $Hcs] as %resp %err ⟨HPP, HW, #HeI, Hresp, Hout⟩
  · iframe Hr; isplitr
    · ipureintro; exact hn
    ipureintro; exact hok
  iunfold auth.respOk at Hresp
  icases Hresp with ⟨%Hnn, Hhdr⟩
  wp_if_destruct
  · -- no response
    iapply HΦ
    iframe
    iframe #
    iapply apply.mPost_backend
    iunfold apply.kvOwn
    iframe
  · -- a response: its header
    icases Hhdr with (%Hn | ⟨%h0, Hh⟩)
    · exact absurd Hn Hif
    wp_apply (hHdr E p log) $$ [$Hpkg $Hb $Hrd $Hsw] as %h ⟨Hrd, Hsw, -⟩
    iapply HΦ
    iframe
    iframe #
    iapply apply.mPost_backend
    iunfold apply.kvOwn
    iframe

theorem applierV3backend.UserDelete.wp_step
    (hHdr : apply.applierV3backend.newHeader.spec (GF := GF) (hG := hG)) :
    applierV3backend.UserDelete.stepSpec (GF := GF) (hG := hG) := by
  intro E W p r log Pre Q Post info hs name hok
  wp_start as ⟨#Hb, #Hs, #Hr, Ho, HW, Hpre⟩
  iunfold apply.mPre at Hpre
  icases Hpre with ⟨Hkv, Hres, Hcs⟩
  iunfold apply.kvOwn at Hkv
  icases Hkv with ⟨Hrd, Hsw, Hknown, Hard⟩
  ihave #Hs' := Hs
  iunfold apply.backendAuthSteps at Hs'
  icases Hs' with ⟨%opts, #Hopts, #Hst⟩
  iunfold apply.isAuthSteps at Hst
  icases Hst with ⟨%ai, %Hai, -, -, -, #HM, -, -⟩
  iStructNamed Hopts
  wp_auto
  rw [Hai]
  wp_apply HM $$ %hs %Pre %Q %Post %r %name [$Ho $HW $Hcs] as %resp %err ⟨HPP, HW, #HeI, Hresp, %en, #Hv, Hout⟩
  · iframe Hr; ipureintro; exact hok
  iunfold auth.respOk at Hresp
  icases Hresp with ⟨%Hnn, Hhdr⟩
  wp_if_destruct
  · -- no response
    iapply HΦ
    iframe
    iframe #
    iapply apply.mPost_backend
    iunfold apply.kvOwn
    iframe
  · -- a response: its header
    icases Hhdr with (%Hn | ⟨%h0, Hh⟩)
    · exact absurd Hn Hif
    wp_apply (hHdr E p log) $$ [$Hpkg $Hb $Hrd $Hsw] as %h ⟨Hrd, Hsw, -⟩
    iapply HΦ
    iframe
    iframe #
    iapply apply.mPost_backend
    iunfold apply.kvOwn
    iframe

theorem applierV3backend.UserChangePassword.wp_step
    (hHdr : apply.applierV3backend.newHeader.spec (GF := GF) (hG := hG)) :
    applierV3backend.UserChangePassword.stepSpec (GF := GF) (hG := hG) := by
  intro E W p r log Pre Q Post info hs name hn hok
  wp_start as ⟨#Hb, #Hs, #Hr, Ho, HW, Hpre⟩
  iunfold apply.mPre at Hpre
  icases Hpre with ⟨Hkv, Hres, Hcs⟩
  iunfold apply.kvOwn at Hkv
  icases Hkv with ⟨Hrd, Hsw, Hknown, Hard⟩
  ihave #Hs' := Hs
  iunfold apply.backendAuthSteps at Hs'
  icases Hs' with ⟨%opts, #Hopts, #Hst⟩
  iunfold apply.isAuthSteps at Hst
  icases Hst with ⟨%ai, %Hai, -, -, -, -, #HM, -⟩
  iStructNamed Hopts
  wp_auto
  rw [Hai]
  wp_apply HM $$ %hs %Pre %Q %Post %r %name [$Ho $HW $Hcs] as %resp %err ⟨HPP, HW, #HeI, Hresp, Hout⟩
  · iframe Hr; isplitr
    · ipureintro; exact hn
    ipureintro; exact hok
  iunfold auth.respOk at Hresp
  icases Hresp with ⟨%Hnn, Hhdr⟩
  wp_if_destruct
  · -- no response
    iapply HΦ
    iframe
    iframe #
    iapply apply.mPost_backend
    iunfold apply.kvOwn
    iframe
  · -- a response: its header
    icases Hhdr with (%Hn | ⟨%h0, Hh⟩)
    · exact absurd Hn Hif
    wp_apply (hHdr E p log) $$ [$Hpkg $Hb $Hrd $Hsw] as %h ⟨Hrd, Hsw, -⟩
    iapply HΦ
    iframe
    iframe #
    iapply apply.mPost_backend
    iunfold apply.kvOwn
    iframe

theorem applierV3backend.RoleAdd.wp_step
    (hHdr : apply.applierV3backend.newHeader.spec (GF := GF) (hG := hG)) :
    applierV3backend.RoleAdd.stepSpec (GF := GF) (hG := hG) := by
  intro E W p r log Pre Q Post info hs name hn hok
  wp_start as ⟨#Hb, #Hs, #Hr, Ho, HW, Hpre⟩
  iunfold apply.mPre at Hpre
  icases Hpre with ⟨Hkv, Hres, Hcs⟩
  iunfold apply.kvOwn at Hkv
  icases Hkv with ⟨Hrd, Hsw, Hknown, Hard⟩
  ihave #Hs' := Hs
  iunfold apply.backendAuthSteps at Hs'
  icases Hs' with ⟨%opts, #Hopts, #Hst⟩
  iunfold apply.isAuthSteps at Hst
  icases Hst with ⟨%ai, %Hai, -, -, -, -, -, #HM⟩
  iStructNamed Hopts
  wp_auto
  rw [Hai]
  wp_apply HM $$ %hs %Pre %Q %Post %r %name [$Ho $HW $Hcs] as %resp %err ⟨HPP, HW, #HeI, Hresp, Hout⟩
  · iframe Hr; isplitr
    · ipureintro; exact hn
    ipureintro; exact hok
  iunfold auth.respOk at Hresp
  icases Hresp with ⟨%Hnn, Hhdr⟩
  wp_if_destruct
  · -- no response
    iapply HΦ
    iframe
    iframe #
    iapply apply.mPost_backend
    iunfold apply.kvOwn
    iframe
  · -- a response: its header
    icases Hhdr with (%Hn | ⟨%h0, Hh⟩)
    · exact absurd Hn Hif
    wp_apply (hHdr E p log) $$ [$Hpkg $Hb $Hrd $Hsw] as %h ⟨Hrd, Hsw, -⟩
    iapply HΦ
    iframe
    iframe #
    iapply apply.mPost_backend
    iunfold apply.kvOwn
    iframe

theorem applierV3backend.AuthEnable.wp_step
    (hHdr : apply.applierV3backend.newHeader.spec (GF := GF) (hG := hG)) :
    applierV3backend.AuthEnable.stepSpec (GF := GF) (hG := hG) := by
  intro E W p log Pre Q Post info hs hon hok
  wp_start as ⟨#Hb, #Hs, Ho, HW, Hpre⟩
  iunfold apply.mPre at Hpre
  icases Hpre with ⟨Hkv, Hres, Hcs⟩
  iunfold apply.kvOwn at Hkv
  icases Hkv with ⟨Hrd, Hsw, Hknown, Hard⟩
  ihave #Hs' := Hs
  iunfold apply.backendAuthSteps at Hs'
  icases Hs' with ⟨%opts, #Hopts, #Hst⟩
  iunfold apply.isAuthSteps at Hst
  icases Hst with ⟨%ai, %Hai, #HM, -, -, -, -, -⟩
  iStructNamed Hopts
  wp_auto
  rw [Hai]
  wp_apply HM $$ %hs %Pre %Q %Post [$Ho $HW $Hcs] as %err ⟨HPP, HW, #HeI, %en, #Hv, Hout⟩
  · isplitr
    · ipureintro; exact hon
    ipureintro; exact hok
  rcases err with ei | _
  · -- the store's error
    wp_auto
    iapply HΦ
    iframe
    iframe #
    iapply apply.mPost_backend
    iunfold apply.kvOwn
    iframe
  · -- enabled: a fresh response with the header
    wp_auto
    wp_apply (hHdr E p log) $$ [$Hpkg $Hb $Hrd $Hsw] as %h ⟨Hrd, Hsw, -⟩
    wp_alloc l as Hl
    wp_auto
    iapply HΦ
    iframe
    iframe #
    iapply apply.mPost_backend
    iunfold apply.kvOwn
    iframe

theorem applierV3backend.AuthDisable.wp_step
    (hHdr : apply.applierV3backend.newHeader.spec (GF := GF) (hG := hG)) :
    applierV3backend.AuthDisable.stepSpec (GF := GF) (hG := hG) := by
  intro E W p log Pre Q Post info hs hok
  wp_start as ⟨#Hb, #Hs, Ho, HW, Hpre⟩
  iunfold apply.mPre at Hpre
  icases Hpre with ⟨Hkv, Hres, Hcs⟩
  iunfold apply.kvOwn at Hkv
  icases Hkv with ⟨Hrd, Hsw, Hknown, Hard⟩
  ihave #Hs' := Hs
  iunfold apply.backendAuthSteps at Hs'
  icases Hs' with ⟨%opts, #Hopts, #Hst⟩
  iunfold apply.isAuthSteps at Hst
  icases Hst with ⟨%ai, %Hai, -, #HM, -, -, -, -⟩
  iStructNamed Hopts
  wp_auto
  rw [Hai]
  wp_apply HM $$ %hs %Pre %Q %Post [$Ho $HW $Hcs] as ⟨HPP, HW, %en, #Hv, Hout⟩
  · ipureintro; exact hok
  wp_apply (hHdr E p log) $$ [$Hpkg $Hb $Hrd $Hsw] as %h ⟨Hrd, Hsw, -⟩
  wp_alloc l as Hl
  wp_auto
  iapply HΦ
  iframe
  iframe #
  isplitl
  · iapply apply.mPost_backend
    iunfold apply.kvOwn
    iframe
  ipureintro; rfl

end applier

end apply
end EtcdGrove
end Perennial
