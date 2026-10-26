/-
**The apply layer's admin steps carrying a resource of the history** (the auth plan's E2v,
2026-10-26; `notes/decisions.md`, "E2v of the auth plan"). Lean-first (no Rocq counterpart).

`AuthSteps.lean`'s `isAuthSteps` and `AuthFuel.lean`'s triples carry the store's write resource as a
constant `W`, and the step's result is the authority after the step (`auth.adminOut`,
`auth.adminOutFu`). E2s's tie of the admin side's halves of the flag and the cache to the latest
state (`auth.X.specT`) depends on the history the step produces, so here the five admin requests
`examples/authkv`'s `SetUp` sends carry, besides `W`, a resource `X` of the history alongside the
authority, given back at the history after (`auth.adminOutX`): `isAuthStepsX`, the backend's
`stepSpecX`, the fueled `fuelSpecX`. The real store meets `isAuthStepsX` with `X = auth.tieRes st M`
and `W = auth.authWB st M P f T ∗ auth.tpAdmin st M` (`isAuthStepsX_of_authInvT`, from E2s's
`X.specT`); `isAuthSteps` (any `W`) gives it with `X` empty (`isAuthStepsX_of_steps`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AuthFuel
public import Proof.go_etcd_io.etcd.server.v3.auth.TieRes

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

/-- The authority with the extra resource `X` of its history. -/
@[reducible] def ownX (M : auth.AuthMode) (X : List auth.AuthState → IProp GF)
    (h : List auth.AuthState) : IProp GF :=
  iprop(auth.authOwn M h ∗ X h)

/-- **The auth store `st`'s five `SetUp` admin operations as model steps carrying `X`** (see the
file header): as `isAuthSteps`'s, with `X hs` beside the authority and given back at the history
after (`auth.adminOutX`). -/
def isAuthStepsX (st : GoInterface) (P : IProp GF) (f : val) (M : auth.AuthMode)
    (X : List auth.AuthState → IProp GF) (W : IProp GF) : IProp GF :=
  iprop(∃ ai : GoInterfaceOk, ⌜st = GoInterface.ok ai⌝ ∗
    □ (∀ (hs : List auth.AuthState) (Pre Q Post : IProp GF),
      {{ ⌜M.isOn = true⌝ ∗ auth.authOwn M hs ∗ X hs ∗ W ∗ mvcc.csContract P f Pre Q Post ∗
          ⌜∀ en : Bool, auth.stepOk M hs (auth.stepOf (auth.authEnableF en))⌝ }}
        (App (Val #(methods ai.ty go!"AuthEnable" ai.v)) (Val #()))
      {{ (err : GoInterface), RET #err; (Post ∨ Pre) ∗ W ∗ applyErrIs err ∗
          ∃ en : Bool, auth.enabledVerdict M en ∗
            auth.adminOutX M (ownX M X) hs (auth.stepOf (auth.authEnableF en)) auth.noExtra err }}) ∗
    □ (∀ (hs : List auth.AuthState) (Pre Q Post : IProp GF) (r : Loc) (name : GoString),
      {{ auth.userAddReqIs r name ∗ ⌜name.length ≤ backend.maxKeySize⌝ ∗ auth.authOwn M hs ∗
          X hs ∗ W ∗ mvcc.csContract P f Pre Q Post ∗
          ⌜auth.stepOk M hs (auth.stepOf (auth.userAddF name))⌝ }}
        (App (Val #(methods ai.ty go!"UserAdd" ai.v)) (Val #r))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); (Post ∨ Pre) ∗ W ∗
          applyErrIs err ∗ auth.respOk etcdserverpb.AuthUserAddResponse resp err ∗
          auth.adminOutX M (ownX M X) hs (auth.stepOf (auth.userAddF name))
            (fun e => e = .noPasswordUser) err }}) ∗
    □ (∀ (hs : List auth.AuthState) (Pre Q Post : IProp GF) (r : Loc) (name : GoString),
      {{ auth.roleAddReqIs r name ∗ ⌜name.length ≤ backend.maxKeySize⌝ ∗ auth.authOwn M hs ∗
          X hs ∗ W ∗ mvcc.csContract P f Pre Q Post ∗
          ⌜auth.stepOk M hs (auth.stepOf (auth.roleAddF name))⌝ }}
        (App (Val #(methods ai.ty go!"RoleAdd" ai.v)) (Val #r))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); (Post ∨ Pre) ∗ W ∗
          applyErrIs err ∗ auth.respOk etcdserverpb.AuthRoleAddResponse resp err ∗
          auth.adminOutX M (ownX M X) hs (auth.stepOf (auth.roleAddF name)) auth.noExtra err }}) ∗
    □ (∀ (hs : List auth.AuthState) (Pre Q Post : IProp GF) (r : Loc) (user role : GoString),
      {{ auth.userGrantRoleReqIs r user role ∗ ⌜user.length ≤ backend.maxKeySize⌝ ∗
          auth.authOwn M hs ∗ X hs ∗ W ∗ mvcc.csContract P f Pre Q Post ∗
          ⌜∀ (sta : auth.AuthState) (u : auth.User), auth.histLast M hs sta →
            sta.users !! user = some u → u.length < 2 ^ 62⌝ ∗
          ⌜auth.stepOk M hs (auth.userGrantRoleR user role)⌝ }}
        (App (Val #(methods ai.ty go!"UserGrantRole" ai.v)) (Val #r))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); (Post ∨ Pre) ∗ W ∗
          applyErrIs err ∗ auth.respOk etcdserverpb.AuthUserGrantRoleResponse resp err ∗
          auth.adminOutX M (ownX M X) hs (auth.userGrantRoleR user role) auth.noExtra err }}) ∗
    □ (∀ (hs : List auth.AuthState) (Pre Q Post : IProp GF) (r : Loc) (name : GoString)
        (w : Option auth.PermW),
      {{ auth.roleGrantPermissionReqIs r name w ∗ ⌜name.length ≤ backend.maxKeySize⌝ ∗
          auth.authOwn M hs ∗ X hs ∗ W ∗ mvcc.csContract P f Pre Q Post ∗
          ⌜auth.stepOk M hs (auth.roleGrantPermissionR name w)⌝ }}
        (App (Val #(methods ai.ty go!"RoleGrantPermission" ai.v)) (Val #r))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); (Post ∨ Pre) ∗ W ∗
          applyErrIs err ∗ auth.respOk etcdserverpb.AuthRoleGrantPermissionResponse resp err ∗
          auth.adminOutX M (ownX M X) hs (auth.roleGrantPermissionR name w) auth.noExtra err }}))

instance isAuthStepsX_persistent (st : GoInterface) (P : IProp GF) (f : val) (M : auth.AuthMode)
    (X : List auth.AuthState → IProp GF) (W : IProp GF) :
    Persistent (isAuthStepsX st P f M X W) := by
  unfold isAuthStepsX; infer_instance

/-- **The `*applierV3backend` `p`'s auth store's admin steps carrying `X`**
(`backendAuthSteps`'s). -/
def backendAuthStepsX (E : AEnv GF) (p : Loc) (X : List auth.AuthState → IProp GF) (W : IProp GF) :
    IProp GF :=
  iprop(∃ opts : ApplierOptions, structFieldRef applierV3backend go!"options" p ↦□ opts ∗
    isAuthStepsX opts.AuthStore' E.P E.f E.authMode X W)

instance backendAuthStepsX_persistent (E : AEnv GF) (p : Loc) (X : List auth.AuthState → IProp GF)
    (W : IProp GF) : Persistent (backendAuthStepsX E p X W) := by
  unfold backendAuthStepsX; infer_instance

end defs

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **An admin operation's result's error** is one the apply layer can take (`adminOut_applyErrIs`
for an authority family). -/
theorem adminOutX_applyErrIs (M : auth.AuthMode) (Own : List auth.AuthState → IProp GF)
    (hs : List auth.AuthState) (R : auth.StepRel) (extra : auth.AuthErr → Prop) (err : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗
      auth.adminOutX M Own hs R extra err ⊢ auth.adminOutX M Own hs R extra err ∗ applyErrIs err := by
  iintro ⟨#Hpkg, H⟩
  unfold auth.adminOutX
  icases H with (⟨%e, %hx, Ho, #He⟩ | ⟨%s, %o, %ho, Hr⟩)
  · ihave #Ha := authErrOf_applyErrIs e err $$ [$Hpkg $He]
    isplitl
    · ileft; iexists e
      isplitr
      · ipureintro; exact hx
      iframe Ho He
    iexact Ha
  · cases o with
    | err e =>
      simp only [auth.outResX] at *
      icases Hr with ⟨Ho, #He⟩
      ihave #Ha := authErrOf_applyErrIs e err $$ [$Hpkg $He]
      isplitl
      · iright; iexists s, (auth.Outcome.err e)
        isplitr
        · ipureintro; exact ho
        simp only [auth.outResX]
        iframe Ho He
      iexact Ha
    | same =>
      simp only [auth.outResX] at *
      icases Hr with ⟨Ho, %Hn⟩
      subst Hn
      isplitl
      · iright; iexists s, auth.Outcome.same
        isplitr
        · ipureintro; exact ho
        simp only [auth.outResX]
        iframe Ho
      iapply applyErrIs_nil
    | next st' =>
      simp only [auth.outResX] at *
      icases Hr with ⟨Ho, %Hn⟩
      subst Hn
      isplitl
      · iright; iexists s, (auth.Outcome.next st')
        isplitr
        · ipureintro; exact ho
        simp only [auth.outResX]
        iframe Ho
      iapply applyErrIs_nil

/-- **`isAuthStepsX` of the real store** at `st`, with `X = auth.tieRes st M` and the write
resource but the halves (`auth.authWB`) with the provider's admin share, from E2s's `X.specT`. -/
theorem isAuthStepsX_of_authInvT
    (hEnable : auth.authStore.AuthEnable.specT (GF := GF) (hG := hG))
    (hUserAdd : auth.authStore.UserAdd.specT (GF := GF) (hG := hG))
    (hRoleAdd : auth.authStore.RoleAdd.specT (GF := GF) (hG := hG))
    (hUserGrantRole : auth.authStore.UserGrantRole.specT (GF := GF) (hG := hG))
    (hRoleGrantPermission : auth.authStore.RoleGrantPermission.specT (GF := GF) (hG := hG))
    (st : Loc) (R : IProp GF) (M : auth.AuthMode) (P : IProp GF) (f : val) (T : IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ auth.authInv st R M ⊢
      isAuthStepsX (auth.authIface st) P f M (auth.tieRes st M)
        iprop(auth.authWB st M P f T ∗ auth.tpAdmin st M) := by
  iintro ⟨#Hpkg, #Hinv⟩
  iunfold isAuthStepsX
  iexists (interface.mk (go.GoType.PointerType auth.authStore.ty) #st)
  isplitr
  · ipureintro; rfl
  isplitr
  · iintro !> %hs %Pre %Q %Post %Φ !> ⟨%Hon, Ho, HX, ⟨HW, HA⟩, Hcs, %Hok⟩ HΦ
    iunfold auth.tieRes at HX
    icases HX with ⟨%b0, %sc0, Hfl, #Hev, Hca, #Hs, %Ht⟩
    ihave HWR := auth.authWRx_join st M P f T b0 sc0 $$ [HW Hfl Hca]
    · iframe; iframe #
    iapply (hEnable st R M P f T hs Pre Q Post b0 sc0) $$ [Ho HWR HA Hcs]
    · iframe; iframe #; ipureintro; exact ⟨Hon, Hok⟩
    iintro !> %err ⟨%b, %sc, HA, HPP, HWR, %en, #Hv, Hout⟩
    icases auth.authWRx_split st M P f T b sc $$ HWR with ⟨HW, Hfl, #Hev', Hca, #Hs'⟩
    ihave Hout := auth.adminOutP_tieRes st M hs _ _ err b0 sc0 b sc Ht $$ [Hfl Hca Hout]
    · iframe; iframe #
    icases adminOutX_applyErrIs M _ hs _ _ err $$ [$Hpkg $Hout] with ⟨Hout, #Ha⟩
    iapply HΦ
    iframe HPP HW HA Ha
    iexists en; iframe Hv; iexact Hout
  isplitr
  · iintro !> %hs %Pre %Q %Post %r %name %Φ !> ⟨#Hr, %Hn, Ho, HX, ⟨HW, HA⟩, Hcs, %Hok⟩ HΦ
    iunfold auth.tieRes at HX
    icases HX with ⟨%b0, %sc0, Hfl, #Hev, Hca, #Hs, %Ht⟩
    ihave HWR := auth.authWRx_join st M P f T b0 sc0 $$ [HW Hfl Hca]
    · iframe; iframe #
    iapply (hUserAdd st R M P f T hs Pre Q Post r name b0 sc0) $$ [Ho HWR Hcs]
    · iframe; iframe #; isplitr
      · ipureintro; exact Hn
      ipureintro; exact Hok
    iintro !> %resp %err ⟨%b, %sc, HPP, HWR, Hresp, Hout⟩
    icases auth.authWRx_split st M P f T b sc $$ HWR with ⟨HW, Hfl, #Hev', Hca, #Hs'⟩
    ihave Hout := auth.adminOutP_tieRes st M hs _ _ err b0 sc0 b sc Ht $$ [Hfl Hca Hout]
    · iframe; iframe #
    icases adminOutX_applyErrIs M _ hs _ _ err $$ [$Hpkg $Hout] with ⟨Hout, #Ha⟩
    iapply HΦ
    iframe HPP HW HA Ha Hresp; iexact Hout
  isplitr
  · iintro !> %hs %Pre %Q %Post %r %name %Φ !> ⟨#Hr, %Hn, Ho, HX, ⟨HW, HA⟩, Hcs, %Hok⟩ HΦ
    iunfold auth.tieRes at HX
    icases HX with ⟨%b0, %sc0, Hfl, #Hev, Hca, #Hs, %Ht⟩
    ihave HWR := auth.authWRx_join st M P f T b0 sc0 $$ [HW Hfl Hca]
    · iframe; iframe #
    iapply (hRoleAdd st R M P f T hs Pre Q Post r name b0 sc0) $$ [Ho HWR Hcs]
    · iframe; iframe #; isplitr
      · ipureintro; exact Hn
      ipureintro; exact Hok
    iintro !> %resp %err ⟨%b, %sc, HPP, HWR, Hresp, Hout⟩
    icases auth.authWRx_split st M P f T b sc $$ HWR with ⟨HW, Hfl, #Hev', Hca, #Hs'⟩
    ihave Hout := auth.adminOutP_tieRes st M hs _ _ err b0 sc0 b sc Ht $$ [Hfl Hca Hout]
    · iframe; iframe #
    icases adminOutX_applyErrIs M _ hs _ _ err $$ [$Hpkg $Hout] with ⟨Hout, #Ha⟩
    iapply HΦ
    iframe HPP HW HA Ha Hresp; iexact Hout
  isplitr
  · iintro !> %hs %Pre %Q %Post %r %user %role %Φ !> ⟨#Hr, %Hn, Ho, HX, ⟨HW, HA⟩, Hcs, %Hb, %Hok⟩ HΦ
    iunfold auth.tieRes at HX
    icases HX with ⟨%b0, %sc0, Hfl, #Hev, Hca, #Hs, %Ht⟩
    ihave HWR := auth.authWRx_join st M P f T b0 sc0 $$ [HW Hfl Hca]
    · iframe; iframe #
    iapply (hUserGrantRole st R M P f T hs Pre Q Post r user role b0 sc0) $$ [Ho HWR Hcs]
    · iframe; iframe #; isplitr
      · ipureintro; exact Hn
      isplitr
      · ipureintro; exact Hb
      ipureintro; exact Hok
    iintro !> %resp %err ⟨%b, %sc, HPP, HWR, Hresp, Hout⟩
    icases auth.authWRx_split st M P f T b sc $$ HWR with ⟨HW, Hfl, #Hev', Hca, #Hs'⟩
    ihave Hout := auth.adminOutP_tieRes st M hs _ _ err b0 sc0 b sc Ht $$ [Hfl Hca Hout]
    · iframe; iframe #
    icases adminOutX_applyErrIs M _ hs _ _ err $$ [$Hpkg $Hout] with ⟨Hout, #Ha⟩
    iapply HΦ
    iframe HPP HW HA Ha Hresp; iexact Hout
  · iintro !> %hs %Pre %Q %Post %r %name %w %Φ !> ⟨#Hr, %Hn, Ho, HX, ⟨HW, HA⟩, Hcs, %Hok⟩ HΦ
    iunfold auth.tieRes at HX
    icases HX with ⟨%b0, %sc0, Hfl, #Hev, Hca, #Hs, %Ht⟩
    ihave HWR := auth.authWRx_join st M P f T b0 sc0 $$ [HW Hfl Hca]
    · iframe; iframe #
    iapply (hRoleGrantPermission st R M P f T hs Pre Q Post r name w b0 sc0) $$ [Ho HWR Hcs]
    · iframe; iframe #; isplitr
      · ipureintro; exact Hn
      ipureintro; exact Hok
    iintro !> %resp %err ⟨%b, %sc, HPP, HWR, Hresp, Hout⟩
    icases auth.authWRx_split st M P f T b sc $$ HWR with ⟨HW, Hfl, #Hev', Hca, #Hs'⟩
    ihave Hout := auth.adminOutP_tieRes st M hs _ _ err b0 sc0 b sc Ht $$ [Hfl Hca Hout]
    · iframe; iframe #
    icases adminOutX_applyErrIs M _ hs _ _ err $$ [$Hpkg $Hout] with ⟨Hout, #Ha⟩
    iapply HΦ
    iframe HPP HW HA Ha Hresp; iexact Hout

end proof


section stepSpecs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`a.UserAdd(r)` performs the model's step carrying `X`** (`UserAdd.stepSpec`'s). -/
abbrev applierV3backend.UserAdd.stepSpecX : Prop :=
  ∀ (E : AEnv GF) (X : List auth.AuthState → IProp GF) (W : IProp GF) (p r : Loc) (log : mvcc.Log)
    (Pre Q Post : IProp GF) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (hs : List auth.AuthState) (name : GoString),
    name.length ≤ backend.maxKeySize →
    auth.stepOk E.authMode hs (auth.stepOf (auth.userAddF name)) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
        apply.backendIs E p ∗ backendAuthStepsX E p X W ∗ auth.userAddReqIs r name ∗
        auth.authOwn E.authMode hs ∗ X hs ∗ W ∗
        apply.mPre E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) info log Pre Q Post }}
      (App (Val (p @!! go.GoType.PointerType applierV3backend.ty @!! go!"UserAdd")) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      apply.mPost E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) log Pre Post ∗
      applyErrIs err ∗ W ∗
      auth.adminOutX E.authMode (ownX E.authMode X) hs (auth.stepOf (auth.userAddF name)) (fun e => e = .noPasswordUser) err }}

/-- **`a.RoleAdd(r)` performs the model's step carrying `X`** (`RoleAdd.stepSpec`'s). -/
abbrev applierV3backend.RoleAdd.stepSpecX : Prop :=
  ∀ (E : AEnv GF) (X : List auth.AuthState → IProp GF) (W : IProp GF) (p r : Loc) (log : mvcc.Log)
    (Pre Q Post : IProp GF) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (hs : List auth.AuthState) (name : GoString),
    name.length ≤ backend.maxKeySize →
    auth.stepOk E.authMode hs (auth.stepOf (auth.roleAddF name)) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
        apply.backendIs E p ∗ backendAuthStepsX E p X W ∗ auth.roleAddReqIs r name ∗
        auth.authOwn E.authMode hs ∗ X hs ∗ W ∗
        apply.mPre E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) info log Pre Q Post }}
      (App (Val (p @!! go.GoType.PointerType applierV3backend.ty @!! go!"RoleAdd")) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      apply.mPost E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) log Pre Post ∗
      applyErrIs err ∗ W ∗
      auth.adminOutX E.authMode (ownX E.authMode X) hs (auth.stepOf (auth.roleAddF name)) auth.noExtra err }}

/-- **`a.UserGrantRole(r)` performs the model's step carrying `X`** (`UserGrantRole.stepSpec`'s). -/
abbrev applierV3backend.UserGrantRole.stepSpecX : Prop :=
  ∀ (E : AEnv GF) (X : List auth.AuthState → IProp GF) (W : IProp GF) (p r : Loc) (log : mvcc.Log)
    (Pre Q Post : IProp GF) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (hs : List auth.AuthState) (user role : GoString),
    user.length ≤ backend.maxKeySize →
    (∀ (sta : auth.AuthState) (u : auth.User), auth.histLast E.authMode hs sta →
      sta.users !! user = some u → u.length < 2 ^ 62) →
    auth.stepOk E.authMode hs (auth.userGrantRoleR user role) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
        apply.backendIs E p ∗ backendAuthStepsX E p X W ∗ auth.userGrantRoleReqIs r user role ∗
        auth.authOwn E.authMode hs ∗ X hs ∗ W ∗
        apply.mPre E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) info log Pre Q Post }}
      (App (Val (p @!! go.GoType.PointerType applierV3backend.ty @!! go!"UserGrantRole")) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      apply.mPost E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) log Pre Post ∗
      applyErrIs err ∗ W ∗
      auth.adminOutX E.authMode (ownX E.authMode X) hs (auth.userGrantRoleR user role) auth.noExtra err }}

/-- **`a.RoleGrantPermission(r)` performs the model's step carrying `X`** (`RoleGrantPermission.stepSpec`'s). -/
abbrev applierV3backend.RoleGrantPermission.stepSpecX : Prop :=
  ∀ (E : AEnv GF) (X : List auth.AuthState → IProp GF) (W : IProp GF) (p r : Loc) (log : mvcc.Log)
    (Pre Q Post : IProp GF) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (hs : List auth.AuthState) (name : GoString) (w : Option auth.PermW),
    name.length ≤ backend.maxKeySize →
    auth.stepOk E.authMode hs (auth.roleGrantPermissionR name w) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
        apply.backendIs E p ∗ backendAuthStepsX E p X W ∗ auth.roleGrantPermissionReqIs r name w ∗
        auth.authOwn E.authMode hs ∗ X hs ∗ W ∗
        apply.mPre E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) info log Pre Q Post }}
      (App (Val (p @!! go.GoType.PointerType applierV3backend.ty @!! go!"RoleGrantPermission")) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      apply.mPost E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) log Pre Post ∗
      applyErrIs err ∗ W ∗
      auth.adminOutX E.authMode (ownX E.authMode X) hs (auth.roleGrantPermissionR name w) auth.noExtra err }}

/-- **`a.AuthEnable()` performs the model's step carrying `X`** (`AuthEnable.stepSpec`'s). -/
abbrev applierV3backend.AuthEnable.stepSpecX : Prop :=
  ∀ (E : AEnv GF) (X : List auth.AuthState → IProp GF) (W : IProp GF) (p : Loc) (log : mvcc.Log)
    (Pre Q Post : IProp GF) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (hs : List auth.AuthState),
    E.authMode.isOn = true →
    (∀ en : Bool, auth.stepOk E.authMode hs (auth.stepOf (auth.authEnableF en))) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
        apply.backendIs E p ∗ backendAuthStepsX E p X W ∗ auth.authOwn E.authMode hs ∗ X hs ∗ W ∗
        apply.mPre E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) info log Pre Q Post }}
      (App (Val (p @!! go.GoType.PointerType applierV3backend.ty @!! go!"AuthEnable")) (Val #()))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      apply.mPost E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) log Pre Post ∗
      applyErrIs err ∗ W ∗
      ∃ en : Bool, auth.enabledVerdict E.authMode en ∗
        auth.adminOutX E.authMode (ownX E.authMode X) hs (auth.stepOf (auth.authEnableF en)) auth.noExtra err }}

/-- **`a.UserAdd(r)` in the mode `on γa`, from the fuel, carrying `X`** (`UserAdd.fuelSpec`'s). -/
abbrev applierV3backend.UserAdd.fuelSpecX : Prop :=
  ∀ (E : AEnv GF) (γa : auth.AuthNames) (X : List auth.AuthState → IProp GF) (W : IProp GF)
    (p r : Loc) (log : mvcc.Log) (Pre Q Post : IProp GF) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (hs : List auth.AuthState) (name : GoString),
    E.authMode = .on γa → receiptBound GF ≤ 2 ^ 48 → name.length ≤ backend.maxKeySize →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
        apply.backendIs E p ∗ backendAuthStepsX E p X W ∗ auth.userAddReqIs r name ∗
        auth.authOwnFu γa hs ∗ X hs ∗ ⧗ 1 ∗ W ∗
        apply.mPre E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) info log Pre Q Post }}
      (App (Val (p @!! go.GoType.PointerType applierV3backend.ty @!! go!"UserAdd")) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      apply.mPost E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) log Pre Post ∗
      applyErrIs err ∗ W ∗
      auth.adminOutX (.on γa) (fun h => iprop(auth.authOwnFu γa h ∗ X h)) hs (auth.stepOf (auth.userAddF name)) (fun e => e = .noPasswordUser) err }}

/-- **`a.RoleAdd(r)` in the mode `on γa`, from the fuel, carrying `X`** (`RoleAdd.fuelSpec`'s). -/
abbrev applierV3backend.RoleAdd.fuelSpecX : Prop :=
  ∀ (E : AEnv GF) (γa : auth.AuthNames) (X : List auth.AuthState → IProp GF) (W : IProp GF)
    (p r : Loc) (log : mvcc.Log) (Pre Q Post : IProp GF) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (hs : List auth.AuthState) (name : GoString),
    E.authMode = .on γa → receiptBound GF ≤ 2 ^ 48 → name.length ≤ backend.maxKeySize →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
        apply.backendIs E p ∗ backendAuthStepsX E p X W ∗ auth.roleAddReqIs r name ∗
        auth.authOwnFu γa hs ∗ X hs ∗ ⧗ 1 ∗ W ∗
        apply.mPre E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) info log Pre Q Post }}
      (App (Val (p @!! go.GoType.PointerType applierV3backend.ty @!! go!"RoleAdd")) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      apply.mPost E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) log Pre Post ∗
      applyErrIs err ∗ W ∗
      auth.adminOutX (.on γa) (fun h => iprop(auth.authOwnFu γa h ∗ X h)) hs (auth.stepOf (auth.roleAddF name)) auth.noExtra err }}

/-- **`a.UserGrantRole(r)` in the mode `on γa`, from the fuel, carrying `X`** (`UserGrantRole.fuelSpec`'s). -/
abbrev applierV3backend.UserGrantRole.fuelSpecX : Prop :=
  ∀ (E : AEnv GF) (γa : auth.AuthNames) (X : List auth.AuthState → IProp GF) (W : IProp GF)
    (p r : Loc) (log : mvcc.Log) (Pre Q Post : IProp GF) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (hs : List auth.AuthState) (user role : GoString),
    E.authMode = .on γa → receiptBound GF ≤ 2 ^ 48 → user.length ≤ backend.maxKeySize →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
        apply.backendIs E p ∗ backendAuthStepsX E p X W ∗ auth.userGrantRoleReqIs r user role ∗
        auth.authOwnFu γa hs ∗ X hs ∗ ⧗ 1 ∗ W ∗
        apply.mPre E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) info log Pre Q Post }}
      (App (Val (p @!! go.GoType.PointerType applierV3backend.ty @!! go!"UserGrantRole")) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      apply.mPost E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) log Pre Post ∗
      applyErrIs err ∗ W ∗
      auth.adminOutX (.on γa) (fun h => iprop(auth.authOwnFu γa h ∗ X h)) hs (auth.userGrantRoleR user role) auth.noExtra err }}

/-- **`a.RoleGrantPermission(r)` in the mode `on γa`, from the fuel, carrying `X`** (`RoleGrantPermission.fuelSpec`'s). -/
abbrev applierV3backend.RoleGrantPermission.fuelSpecX : Prop :=
  ∀ (E : AEnv GF) (γa : auth.AuthNames) (X : List auth.AuthState → IProp GF) (W : IProp GF)
    (p r : Loc) (log : mvcc.Log) (Pre Q Post : IProp GF) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (hs : List auth.AuthState) (name : GoString) (w : Option auth.PermW),
    E.authMode = .on γa → receiptBound GF ≤ 2 ^ 48 → name.length ≤ backend.maxKeySize →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
        apply.backendIs E p ∗ backendAuthStepsX E p X W ∗ auth.roleGrantPermissionReqIs r name w ∗
        auth.authOwnFu γa hs ∗ X hs ∗ ⧗ 1 ∗ W ∗
        apply.mPre E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) info log Pre Q Post }}
      (App (Val (p @!! go.GoType.PointerType applierV3backend.ty @!! go!"RoleGrantPermission")) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      apply.mPost E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) log Pre Post ∗
      applyErrIs err ∗ W ∗
      auth.adminOutX (.on γa) (fun h => iprop(auth.authOwnFu γa h ∗ X h)) hs (auth.roleGrantPermissionR name w) auth.noExtra err }}

/-- **`a.AuthEnable()` in the mode `on γa`, from the fuel, carrying `X`**. -/
abbrev applierV3backend.AuthEnable.fuelSpecX : Prop :=
  ∀ (E : AEnv GF) (γa : auth.AuthNames) (X : List auth.AuthState → IProp GF) (W : IProp GF)
    (p : Loc) (log : mvcc.Log) (Pre Q Post : IProp GF) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (hs : List auth.AuthState),
    E.authMode = .on γa → receiptBound GF ≤ 2 ^ 48 →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
        apply.backendIs E p ∗ backendAuthStepsX E p X W ∗ auth.authOwnFu γa hs ∗ X hs ∗ ⧗ 1 ∗ W ∗
        apply.mPre E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) info log Pre Q Post }}
      (App (Val (p @!! go.GoType.PointerType applierV3backend.ty @!! go!"AuthEnable")) (Val #()))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      apply.mPost E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) log Pre Post ∗
      applyErrIs err ∗ W ∗
      ∃ en : Bool, auth.enabledVerdict E.authMode en ∗
        auth.adminOutX (.on γa) (fun h => iprop(auth.authOwnFu γa h ∗ X h)) hs
          (auth.stepOf (auth.authEnableF en)) auth.noExtra err }}

end stepSpecs

section applier
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

theorem applierV3backend.UserAdd.wp_stepX
    (hHdr : apply.applierV3backend.newHeader.spec (GF := GF) (hG := hG)) :
    applierV3backend.UserAdd.stepSpecX (GF := GF) (hG := hG) := by
  intro E X W p r log Pre Q Post info hs name hn hok
  wp_start as ⟨#Hb, #Hs, #Hr, Ho, HX, HW, Hpre⟩
  iunfold apply.mPre at Hpre
  icases Hpre with ⟨Hkv, Hres, Hcs⟩
  iunfold apply.kvOwn at Hkv
  icases Hkv with ⟨Hrd, Hsw, Hknown, Hard⟩
  ihave #Hs' := Hs
  iunfold apply.backendAuthStepsX at Hs'
  icases Hs' with ⟨%opts, #Hopts, #Hst⟩
  iunfold apply.isAuthStepsX at Hst
  icases Hst with ⟨%ai, %Hai, -, #HM, -, -, -⟩
  iStructNamed Hopts
  wp_auto
  rw [Hai]
  wp_apply HM $$ %hs %Pre %Q %Post %r %name [$Ho $HX $HW $Hcs] as %resp %err ⟨HPP, HW, #HeI, Hresp, Hout⟩
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

theorem applierV3backend.RoleAdd.wp_stepX
    (hHdr : apply.applierV3backend.newHeader.spec (GF := GF) (hG := hG)) :
    applierV3backend.RoleAdd.stepSpecX (GF := GF) (hG := hG) := by
  intro E X W p r log Pre Q Post info hs name hn hok
  wp_start as ⟨#Hb, #Hs, #Hr, Ho, HX, HW, Hpre⟩
  iunfold apply.mPre at Hpre
  icases Hpre with ⟨Hkv, Hres, Hcs⟩
  iunfold apply.kvOwn at Hkv
  icases Hkv with ⟨Hrd, Hsw, Hknown, Hard⟩
  ihave #Hs' := Hs
  iunfold apply.backendAuthStepsX at Hs'
  icases Hs' with ⟨%opts, #Hopts, #Hst⟩
  iunfold apply.isAuthStepsX at Hst
  icases Hst with ⟨%ai, %Hai, -, -, #HM, -, -⟩
  iStructNamed Hopts
  wp_auto
  rw [Hai]
  wp_apply HM $$ %hs %Pre %Q %Post %r %name [$Ho $HX $HW $Hcs] as %resp %err ⟨HPP, HW, #HeI, Hresp, Hout⟩
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

theorem applierV3backend.UserGrantRole.wp_stepX
    (hHdr : apply.applierV3backend.newHeader.spec (GF := GF) (hG := hG)) :
    applierV3backend.UserGrantRole.stepSpecX (GF := GF) (hG := hG) := by
  intro E X W p r log Pre Q Post info hs user role hn hb hok
  wp_start as ⟨#Hb, #Hs, #Hr, Ho, HX, HW, Hpre⟩
  iunfold apply.mPre at Hpre
  icases Hpre with ⟨Hkv, Hres, Hcs⟩
  iunfold apply.kvOwn at Hkv
  icases Hkv with ⟨Hrd, Hsw, Hknown, Hard⟩
  ihave #Hs' := Hs
  iunfold apply.backendAuthStepsX at Hs'
  icases Hs' with ⟨%opts, #Hopts, #Hst⟩
  iunfold apply.isAuthStepsX at Hst
  icases Hst with ⟨%ai, %Hai, -, -, -, #HM, -⟩
  iStructNamed Hopts
  wp_auto
  rw [Hai]
  wp_apply HM $$ %hs %Pre %Q %Post %r %user %role [$Ho $HX $HW $Hcs] as %resp %err ⟨HPP, HW, #HeI, Hresp, Hout⟩
  · iframe Hr; isplitr
    · ipureintro; exact hn
    isplitr
    · ipureintro; exact hb
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

theorem applierV3backend.RoleGrantPermission.wp_stepX
    (hHdr : apply.applierV3backend.newHeader.spec (GF := GF) (hG := hG)) :
    applierV3backend.RoleGrantPermission.stepSpecX (GF := GF) (hG := hG) := by
  intro E X W p r log Pre Q Post info hs name w hn hok
  wp_start as ⟨#Hb, #Hs, #Hr, Ho, HX, HW, Hpre⟩
  iunfold apply.mPre at Hpre
  icases Hpre with ⟨Hkv, Hres, Hcs⟩
  iunfold apply.kvOwn at Hkv
  icases Hkv with ⟨Hrd, Hsw, Hknown, Hard⟩
  ihave #Hs' := Hs
  iunfold apply.backendAuthStepsX at Hs'
  icases Hs' with ⟨%opts, #Hopts, #Hst⟩
  iunfold apply.isAuthStepsX at Hst
  icases Hst with ⟨%ai, %Hai, -, -, -, -, #HM⟩
  iStructNamed Hopts
  wp_auto
  rw [Hai]
  wp_apply HM $$ %hs %Pre %Q %Post %r %name %w [$Ho $HX $HW $Hcs] as %resp %err ⟨HPP, HW, #HeI, Hresp, Hout⟩
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

theorem applierV3backend.AuthEnable.wp_stepX
    (hHdr : apply.applierV3backend.newHeader.spec (GF := GF) (hG := hG)) :
    applierV3backend.AuthEnable.stepSpecX (GF := GF) (hG := hG) := by
  intro E X W p log Pre Q Post info hs hon hok
  wp_start as ⟨#Hb, #Hs, Ho, HX, HW, Hpre⟩
  iunfold apply.mPre at Hpre
  icases Hpre with ⟨Hkv, Hres, Hcs⟩
  iunfold apply.kvOwn at Hkv
  icases Hkv with ⟨Hrd, Hsw, Hknown, Hard⟩
  ihave #Hs' := Hs
  iunfold apply.backendAuthStepsX at Hs'
  icases Hs' with ⟨%opts, #Hopts, #Hst⟩
  iunfold apply.isAuthStepsX at Hst
  icases Hst with ⟨%ai, %Hai, #HM, -, -, -, -⟩
  iStructNamed Hopts
  wp_auto
  rw [Hai]
  wp_apply HM $$ %hs %Pre %Q %Post [$Ho $HX $HW $Hcs] as %err ⟨HPP, HW, #HeI, %en, #Hv, Hout⟩
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

theorem applierV3backend.UserAdd.wp_fuelX
    (h : applierV3backend.UserAdd.stepSpecX (GF := GF) (hG := hG)) :
    applierV3backend.UserAdd.fuelSpecX (GF := GF) (hG := hG) := by
  intro E γa X W p r log Pre Q Post info hs name hM hb hn
  iintro %Φ ⟨#Hpkg, #Hb, #Hs, Hr, HOF, HX, Hrc, HW, Hpre⟩ HΦ
  iunfold auth.authOwnFu at HOF
  icases HOF with ⟨Ho, Hf⟩
  ihave Hf := auth.authFuel_charge hs $$ [Hf Hrc]
  · iframe
  icases auth.authFuelT_fuel hs hb $$ Hf with ⟨Hf, %Hk⟩
  obtain ⟨k, Hfk, Hlt⟩ := Hk
  have hok : auth.stepOk E.authMode hs (auth.stepOf (auth.userAddF name)) :=
    hM ▸ auth.stepOk_of_fuel γa hs _ k (auth.stepSmall_userAdd name hn) Hfk Hlt
  iapply (h E X W p r log Pre Q Post info hs name hn hok) $$ [Hr Ho HX HW Hpre]
  · rw [hM]; iframe; iframe #
  iintro !> %resp %err ⟨Hpost, #He, HW, Hout⟩
  rw [hM]
  ihave Hout := auth.adminOutX_fu γa X hs _ _ err (auth.stepSmall_userAdd name hn) $$ [Hf Hout]
  · iframe
  iapply HΦ
  iframe; iframe #

theorem applierV3backend.RoleAdd.wp_fuelX
    (h : applierV3backend.RoleAdd.stepSpecX (GF := GF) (hG := hG)) :
    applierV3backend.RoleAdd.fuelSpecX (GF := GF) (hG := hG) := by
  intro E γa X W p r log Pre Q Post info hs name hM hb hn
  iintro %Φ ⟨#Hpkg, #Hb, #Hs, Hr, HOF, HX, Hrc, HW, Hpre⟩ HΦ
  iunfold auth.authOwnFu at HOF
  icases HOF with ⟨Ho, Hf⟩
  ihave Hf := auth.authFuel_charge hs $$ [Hf Hrc]
  · iframe
  icases auth.authFuelT_fuel hs hb $$ Hf with ⟨Hf, %Hk⟩
  obtain ⟨k, Hfk, Hlt⟩ := Hk
  have hok : auth.stepOk E.authMode hs (auth.stepOf (auth.roleAddF name)) :=
    hM ▸ auth.stepOk_of_fuel γa hs _ k (auth.stepSmall_roleAdd name) Hfk Hlt
  iapply (h E X W p r log Pre Q Post info hs name hn hok) $$ [Hr Ho HX HW Hpre]
  · rw [hM]; iframe; iframe #
  iintro !> %resp %err ⟨Hpost, #He, HW, Hout⟩
  rw [hM]
  ihave Hout := auth.adminOutX_fu γa X hs _ _ err (auth.stepSmall_roleAdd name) $$ [Hf Hout]
  · iframe
  iapply HΦ
  iframe; iframe #

theorem applierV3backend.UserGrantRole.wp_fuelX
    (h : applierV3backend.UserGrantRole.stepSpecX (GF := GF) (hG := hG)) :
    applierV3backend.UserGrantRole.fuelSpecX (GF := GF) (hG := hG) := by
  intro E γa X W p r log Pre Q Post info hs user role hM hb hn
  iintro %Φ ⟨#Hpkg, #Hb, #Hs, Hr, HOF, HX, Hrc, HW, Hpre⟩ HΦ
  iunfold auth.authOwnFu at HOF
  icases HOF with ⟨Ho, Hf⟩
  ihave Hf := auth.authFuel_charge hs $$ [Hf Hrc]
  · iframe
  icases auth.authFuelT_fuel hs hb $$ Hf with ⟨Hf, %Hk⟩
  obtain ⟨k, Hfk, Hlt⟩ := Hk
  have hok : auth.stepOk E.authMode hs (auth.userGrantRoleR user role) :=
    hM ▸ auth.stepOk_of_fuel γa hs _ k (auth.stepSmall_userGrantRole user role) Hfk Hlt
  have hroles : ∀ (sta : auth.AuthState) (u : auth.User), auth.histLast E.authMode hs sta →
      sta.users !! user = some u → u.length < 2 ^ 62 := by
    intro sta u hl hu
    rw [hM] at hl
    obtain ⟨h1, h2⟩ := auth.fuelOk_last γa hs k sta Hfk hl
    have := h2.roles user u hu
    omega
  iapply (h E X W p r log Pre Q Post info hs user role hn hroles hok) $$ [Hr Ho HX HW Hpre]
  · rw [hM]; iframe; iframe #
  iintro !> %resp %err ⟨Hpost, #He, HW, Hout⟩
  rw [hM]
  ihave Hout := auth.adminOutX_fu γa X hs _ _ err (auth.stepSmall_userGrantRole user role) $$ [Hf Hout]
  · iframe
  iapply HΦ
  iframe; iframe #

theorem applierV3backend.RoleGrantPermission.wp_fuelX
    (h : applierV3backend.RoleGrantPermission.stepSpecX (GF := GF) (hG := hG)) :
    applierV3backend.RoleGrantPermission.fuelSpecX (GF := GF) (hG := hG) := by
  intro E γa X W p r log Pre Q Post info hs name w hM hb hn
  iintro %Φ ⟨#Hpkg, #Hb, #Hs, Hr, HOF, HX, Hrc, HW, Hpre⟩ HΦ
  iunfold auth.authOwnFu at HOF
  icases HOF with ⟨Ho, Hf⟩
  ihave Hf := auth.authFuel_charge hs $$ [Hf Hrc]
  · iframe
  icases auth.authFuelT_fuel hs hb $$ Hf with ⟨Hf, %Hk⟩
  obtain ⟨k, Hfk, Hlt⟩ := Hk
  have hok : auth.stepOk E.authMode hs (auth.roleGrantPermissionR name w) :=
    hM ▸ auth.stepOk_of_fuel γa hs _ k (auth.stepSmall_roleGrantPermission name w) Hfk Hlt
  iapply (h E X W p r log Pre Q Post info hs name w hn hok) $$ [Hr Ho HX HW Hpre]
  · rw [hM]; iframe; iframe #
  iintro !> %resp %err ⟨Hpost, #He, HW, Hout⟩
  rw [hM]
  ihave Hout := auth.adminOutX_fu γa X hs _ _ err (auth.stepSmall_roleGrantPermission name w) $$ [Hf Hout]
  · iframe
  iapply HΦ
  iframe; iframe #

theorem applierV3backend.AuthEnable.wp_fuelX
    (h : applierV3backend.AuthEnable.stepSpecX (GF := GF) (hG := hG)) :
    applierV3backend.AuthEnable.fuelSpecX (GF := GF) (hG := hG) := by
  intro E γa X W p log Pre Q Post info hs hM hb
  iintro %Φ ⟨#Hpkg, #Hb, #Hs, HOF, HX, Hrc, HW, Hpre⟩ HΦ
  iunfold auth.authOwnFu at HOF
  icases HOF with ⟨Ho, Hf⟩
  ihave Hf := auth.authFuel_charge hs $$ [Hf Hrc]
  · iframe
  icases auth.authFuelT_fuel hs hb $$ Hf with ⟨Hf, %Hk⟩
  obtain ⟨k, Hfk, Hlt⟩ := Hk
  have hok : ∀ en : Bool, auth.stepOk E.authMode hs (auth.stepOf (auth.authEnableF en)) :=
    fun en => hM ▸ auth.stepOk_of_fuel γa hs _ k (auth.stepSmall_authEnable en) Hfk Hlt
  have hon : E.authMode.isOn = true := by rw [hM]; rfl
  iapply (h E X W p log Pre Q Post info hs hon hok) $$ [Ho HX HW Hpre]
  · rw [hM]; iframe; iframe #
  iintro !> %resp %err ⟨Hpost, #He, HW, %en, #Hv, Hout⟩
  rw [hM]
  ihave Hout := auth.adminOutX_fu γa X hs _ _ err (auth.stepSmall_authEnable en) $$ [Hf Hout]
  · iframe
  iapply HΦ
  iframe; iframe #

end applier

end apply
end EtcdGrove
end Perennial
