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
`X.specT`; `UserAdd`'s from E2y's `specTSure`: E3a, its request's password choice cannot fail,
`auth.userAddSure`, and the outcome is the step's alone).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AuthFuel
public import Proof.go_etcd_io.etcd.server.v3.auth.TieRes
public import Proof.go_etcd_io.etcd.server.v3.auth.authStore__UserAdd_tieSure
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__newHeader
public import Spec.context.WithValue

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

section pure

/-- **`AuthEnable`'s step at the flag `en` its check read** (the auth plan's E3c), that flag the
latest state's in the mode `on` (`auth.stepOf (auth.authEnableF en)` alone allows the flag of any
recorded state, which is all `AuthEnable.spec` says; with the tie, `AuthEnable.specT`, it is the
admin side's half, the latest state's). -/
def authEnableR (M : auth.AuthMode) (en : Bool) : auth.StepRel :=
  fun st o => (∀ γa, M = .on γa → st.enabled = en) ∧ auth.stepOf (auth.authEnableF en) st o

theorem stepSmall_authEnableR (M : auth.AuthMode) (en : Bool) : auth.StepSmall (authEnableR M en) :=
  fun st st' h hR => auth.stepSmall_authEnable en st st' h hR.2

/-- In the mode `on`, `authEnableR` is the model's step at the state's own flag. -/
theorem authEnableR_on (γa : auth.AuthNames) (en : Bool) (st : auth.AuthState) (o : auth.Outcome)
    (h : authEnableR (.on γa) en st o) : auth.stepOf (auth.authEnableF st.enabled) st o := by
  rw [h.1 γa rfl]; exact h.2

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The authority with the extra resource `X` of its history. -/
@[reducible] def ownX (M : auth.AuthMode) (X : List auth.AuthState → IProp GF)
    (h : List auth.AuthState) : IProp GF :=
  iprop(auth.authOwn M h ∗ X h)

/-- **The auth store `st`'s five `SetUp` admin operations as model steps carrying `X`** (see the
file header): as `isAuthSteps`'s, with `X hs` beside the authority and given back at the history
after (`auth.adminOutX`); and (C1's A2) its `Authenticate`, at the reader resource `RD` the apply
thread lends (`kvOwn`'s `E.RD`; the real store's `auth.authRd`). -/
def isAuthStepsX (st : GoInterface) (P : IProp GF) (f : val) (M : auth.AuthMode)
    (X : List auth.AuthState → IProp GF) (W RD : IProp GF) : IProp GF :=
  iprop(∃ ai : GoInterfaceOk, ⌜st = GoInterface.ok ai⌝ ∗
    □ (∀ (hs : List auth.AuthState) (Pre Q Post : IProp GF),
      {{ ⌜M.isOn = true⌝ ∗ auth.authOwn M hs ∗ X hs ∗ W ∗ mvcc.csContract P f Pre Q Post ∗
          ⌜∀ en : Bool, auth.stepOk M hs (auth.stepOf (auth.authEnableF en))⌝ ∗
          auth.capNextM M hs auth.authEnableOwnR }}
        (App (Val #(methods ai.ty go!"AuthEnable" ai.v)) (Val #()))
      {{ (err : GoInterface), RET #err; (Post ∨ Pre) ∗ W ∗ applyErrIs err ∗
          ∃ en : Bool, auth.enabledVerdict M en ∗
            auth.adminOutX M (ownX M X) hs (authEnableR M en) auth.noExtra err }}) ∗
    □ (∀ (hs : List auth.AuthState) (Pre Q Post : IProp GF) (r : Loc) (name : GoString),
      {{ auth.userAddReqIs r name ∗ auth.userAddSure r ∗ ⌜name.length ≤ backend.maxKeySize⌝ ∗
          auth.authOwn M hs ∗ X hs ∗ W ∗ mvcc.csContract P f Pre Q Post ∗
          ⌜auth.stepOk M hs (auth.stepOf (auth.userAddF name))⌝ ∗
          auth.capNextM M hs (auth.stepOf (auth.userAddF name)) }}
        (App (Val #(methods ai.ty go!"UserAdd" ai.v)) (Val #r))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); (Post ∨ Pre) ∗ W ∗
          applyErrIs err ∗ auth.respOk etcdserverpb.AuthUserAddResponse resp err ∗
          auth.adminOutX M (ownX M X) hs (auth.stepOf (auth.userAddF name)) auth.noExtra err }}) ∗
    □ (∀ (hs : List auth.AuthState) (Pre Q Post : IProp GF) (r : Loc) (name : GoString),
      {{ auth.roleAddReqIs r name ∗ ⌜name.length ≤ backend.maxKeySize⌝ ∗ auth.authOwn M hs ∗
          X hs ∗ W ∗ mvcc.csContract P f Pre Q Post ∗
          ⌜auth.stepOk M hs (auth.stepOf (auth.roleAddF name))⌝ ∗
          auth.capNextM M hs (auth.stepOf (auth.roleAddF name)) }}
        (App (Val #(methods ai.ty go!"RoleAdd" ai.v)) (Val #r))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); (Post ∨ Pre) ∗ W ∗
          applyErrIs err ∗ auth.respOk etcdserverpb.AuthRoleAddResponse resp err ∗
          auth.adminOutX M (ownX M X) hs (auth.stepOf (auth.roleAddF name)) auth.noExtra err }}) ∗
    □ (∀ (hs : List auth.AuthState) (Pre Q Post : IProp GF) (r : Loc) (user role : GoString),
      {{ auth.userGrantRoleReqIs r user role ∗ ⌜user.length ≤ backend.maxKeySize⌝ ∗
          auth.authOwn M hs ∗ X hs ∗ W ∗ mvcc.csContract P f Pre Q Post ∗
          ⌜∀ (sta : auth.AuthState) (u : auth.User), auth.histLast M hs sta →
            sta.users !! user = some u → u.length < 2 ^ 62⌝ ∗
          ⌜auth.stepOk M hs (auth.userGrantRoleR user role)⌝ ∗
          auth.capNextM M hs (auth.userGrantRoleR user role) }}
        (App (Val #(methods ai.ty go!"UserGrantRole" ai.v)) (Val #r))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); (Post ∨ Pre) ∗ W ∗
          applyErrIs err ∗ auth.respOk etcdserverpb.AuthUserGrantRoleResponse resp err ∗
          auth.adminOutX M (ownX M X) hs (auth.userGrantRoleR user role) auth.noExtra err }}) ∗
    □ (∀ (hs : List auth.AuthState) (Pre Q Post : IProp GF) (r : Loc) (name : GoString)
        (w : Option auth.PermW),
      {{ auth.roleGrantPermissionReqIs r name w ∗ ⌜name.length ≤ backend.maxKeySize⌝ ∗
          auth.authOwn M hs ∗ X hs ∗ W ∗ mvcc.csContract P f Pre Q Post ∗
          ⌜auth.stepOk M hs (auth.roleGrantPermissionR name w)⌝ ∗
          auth.capNextM M hs (auth.roleGrantPermissionR name w) }}
        (App (Val #(methods ai.ty go!"RoleGrantPermission" ai.v)) (Val #r))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); (Post ∨ Pre) ∗ W ∗
          applyErrIs err ∗ auth.respOk etcdserverpb.AuthRoleGrantPermissionResponse resp err ∗
          auth.adminOutX M (ownX M X) hs (auth.roleGrantPermissionR name w) auth.noExtra err }}) ∗
    -- (C1's A2) `Authenticate`, which writes nothing: at the reader resource `RD` (`IsAuthEnabled`
    -- read-locks the flag) and the context `authnCtx` (the token's index, prefix and right); its
    -- error one of the auth package's
    □ (∀ (hs : List auth.AuthState) (Pre Q Post : IProp GF) (ctx : GoInterface)
        (name pw : GoString),
      {{ ⌜M.isOn = true⌝ ∗ RD ∗ auth.authOwn M hs ∗ X hs ∗ W ∗ mvcc.csContract P f Pre Q Post ∗
          auth.authnCtx M ctx }}
        (App (App (App (Val #(methods ai.ty go!"Authenticate" ai.v)) (Val #ctx)) (Val #name))
          (Val #pw))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); (Post ∨ Pre) ∗ RD ∗
          auth.authOwn M hs ∗ X hs ∗ W ∗ auth.authenticated M hs name resp err ∗
          (⌜err = GoInterface.nil⌝ ∨ ∃ e : auth.AuthErr, auth.authErrOf e err) }}))

instance isAuthStepsX_persistent (st : GoInterface) (P : IProp GF) (f : val) (M : auth.AuthMode)
    (X : List auth.AuthState → IProp GF) (W RD : IProp GF) :
    Persistent (isAuthStepsX st P f M X W RD) := by
  unfold isAuthStepsX; infer_instance

/-- **The `*applierV3backend` `p`'s auth store's admin steps carrying `X`**
(`backendAuthSteps`'s). -/
def backendAuthStepsX (E : AEnv GF) (p : Loc) (X : List auth.AuthState → IProp GF) (W : IProp GF) :
    IProp GF :=
  iprop(∃ opts : ApplierOptions, structFieldRef applierV3backend go!"options" p ↦□ opts ∗
    isAuthStepsX opts.AuthStore' E.P E.f E.authMode X W E.RD)

instance backendAuthStepsX_persistent (E : AEnv GF) (p : Loc) (X : List auth.AuthState → IProp GF)
    (W : IProp GF) : Persistent (backendAuthStepsX E p X W) := by
  unfold backendAuthStepsX; infer_instance

end defs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
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

/-- **An admin result's relation weakened at the latest state**. -/
theorem adminOutX_rel (M : auth.AuthMode) (Own : List auth.AuthState → IProp GF)
    (hs : List auth.AuthState) (R R' : auth.StepRel) (extra : auth.AuthErr → Prop) (err : GoInterface)
    (h : ∀ st o, auth.histLast M hs st → R st o → R' st o) :
    auth.adminOutX M Own hs R extra err ⊢ auth.adminOutX M Own hs R' extra err := by
  unfold auth.adminOutX
  iintro (⟨%e, %hx, Ho, He⟩ | ⟨%st, %o, %ho, Hr⟩)
  · ileft; iexists e; iframe Ho He; ipureintro; exact hx
  · iright; iexists st, o; iframe Hr; ipureintro; exact ⟨ho.1, h st o ho.1 ho.2⟩

/-- **`isAuthStepsX` of the real store** at `st`, with `X = auth.tieRes st M` and the write
resource but the halves (`auth.authWB`) with the provider's admin share, from E2s's `X.specT`. -/
theorem isAuthStepsX_of_authInvT
    (hEnable : auth.authStore.AuthEnable.specT (GF := GF) (hG := hG))
    (hUserAdd : auth.authStore.UserAdd.specTSure (GF := GF) (hG := hG))
    (hRoleAdd : auth.authStore.RoleAdd.specT (GF := GF) (hG := hG))
    (hUserGrantRole : auth.authStore.UserGrantRole.specT (GF := GF) (hG := hG))
    (hRoleGrantPermission : auth.authStore.RoleGrantPermission.specT (GF := GF) (hG := hG))
    (hAuthn : auth.authStore.Authenticate.specTB (GF := GF) (hG := hG))
    (st : Loc) (R : IProp GF) (M : auth.AuthMode) (P : IProp GF) (f : val) (T : IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ auth.authInv st R M ⊢
      isAuthStepsX (auth.authIface st) P f M (auth.tieRes st M)
        iprop(auth.authWB st M P f T ∗ auth.tpAdmin st M) (auth.authRd st R M) := by
  iintro ⟨#Hpkg, #Hinv⟩
  iunfold isAuthStepsX
  iexists (interface.mk (go.GoType.PointerType auth.authStore.ty) #st)
  isplitr
  · ipureintro; rfl
  isplitr
  · iintro !> %hs %Pre %Q %Post %Φ !> ⟨%Hon, Ho, HX, ⟨HW, HA⟩, Hcs, %Hok, #Hcap⟩ HΦ
    iunfold auth.tieRes at HX
    icases HX with ⟨%b0, %sc0, Hfl, #Hev, Hca, #Hs, %Ht⟩
    ihave #Hcap := auth.capNextM_authEnableOwn_at M hs b0
      (fun γa hM stl hl => by subst hM; exact ((Ht stl hl).1).symm) $$ Hcap
    ihave HWR := auth.authWRx_join st M P f T b0 sc0 $$ [HW Hfl Hca]
    · iframe; iframe #
    iapply (hEnable st R M P f T hs Pre Q Post b0 sc0) $$ [Ho HWR HA Hcs]
    · iframe; iframe #; ipureintro; exact ⟨Hon, Hok⟩
    iintro !> %err ⟨%b, %sc, HA, HPP, HWR, %en, %Hen, #Hv, Hout⟩
    icases auth.authWRx_split st M P f T b sc $$ HWR with ⟨HW, Hfl, #Hev', Hca, #Hs'⟩
    ihave Hout := auth.adminOutP_tieRes st M hs _ _ err b0 sc0 b sc Ht $$ [Hfl Hca Hout]
    · iframe; iframe #
    -- (E3c) the flag read is the admin side's half, tied to the latest state
    ihave Hout := adminOutX_rel M _ hs _ (authEnableR M en) _ err
      (fun stl o hl hR => ⟨fun γa hM => by
        subst hM; subst Hen; exact ((Ht stl hl).1).symm, hR⟩) $$ Hout
    icases adminOutX_applyErrIs M _ hs _ _ err $$ [$Hpkg $Hout] with ⟨Hout, #Ha⟩
    iapply HΦ
    iframe HPP HW HA Ha
    iexists en; iframe Hv; iexact Hout
  isplitr
  · iintro !> %hs %Pre %Q %Post %r %name %Φ !> ⟨#Hr, #Hsure, %Hn, Ho, HX, ⟨HW, HA⟩, Hcs, %Hok, #Hcap⟩ HΦ
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
  · iintro !> %hs %Pre %Q %Post %r %name %Φ !> ⟨#Hr, %Hn, Ho, HX, ⟨HW, HA⟩, Hcs, %Hok, #Hcap⟩ HΦ
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
  · iintro !> %hs %Pre %Q %Post %r %user %role %Φ !> ⟨#Hr, %Hn, Ho, HX, ⟨HW, HA⟩, Hcs, %Hb, %Hok, #Hcap⟩ HΦ
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
  isplitr
  · iintro !> %hs %Pre %Q %Post %r %name %w %Φ !> ⟨#Hr, %Hn, Ho, HX, ⟨HW, HA⟩, Hcs, %Hok, #Hcap⟩ HΦ
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
  -- (C1's A2) `Authenticate`: the store's `specTB` at the halves the tie holds, which it keeps
  · iintro !> %hs %Pre %Q %Post %ctx %name %pw %Φ !> ⟨%Hon, HRD, Ho, HX, ⟨HW, HA⟩, Hcs, Hctx⟩ HΦ
    iunfold auth.authRd at HRD
    icases HRD with ⟨Hen, HRD'⟩
    iunfold auth.tieRes at HX
    icases HX with ⟨%b0, %sc0, Hfl, #Hev, Hca, #Hs, %Ht⟩
    iunfold auth.authWB at HW
    icases HW with ⟨⟨%be, Hbe⟩, HT⟩
    ihave HWR : auth.authWRxB st M P f T b0 sc0 be $$ [Hbe HT Hfl Hca]
    · iunfold auth.authWRxB; iframe; iframe #
    iapply (hAuthn st R M P f T hs Pre Q Post ctx name pw b0 sc0 be) $$ [Hen Ho HWR Hcs Hctx]
    · iframe; iframe #
    iintro !> %resp %err ⟨HPP, Hen, Ho, HWR, Hau, #He⟩
    iunfold auth.authWRxB at HWR
    icases HWR with ⟨Hbe, HT, Hfl, -, Hca, -⟩
    iapply HΦ
    iframe HPP Ho Hau He HA
    isplitl [Hen HRD']
    · iunfold auth.authRd; iframe
    isplitl [Hfl Hca]
    · iunfold auth.tieRes; iexists b0, sc0; iframe; iframe #; ipureintro; exact Ht
    iunfold auth.authWB; iframe HT; iexists be; iframe Hbe

/-- **`isAuthStepsX` of the real store, keeping its backend** (the auth plan's E3l): as
`isAuthStepsX_of_authInvT`, with the write resource's backend `be` kept by each step (E3l's
`X.specTB`) and a persistent fact `Ψ be` of it carried along (the server's: the half of `be` it
lent is its rest's, `authBeOn`). -/
theorem isAuthStepsX_of_authInvTB
    (hEnable : auth.authStore.AuthEnable.specTB (GF := GF) (hG := hG))
    (hUserAdd : auth.authStore.UserAdd.specTSureB (GF := GF) (hG := hG))
    (hRoleAdd : auth.authStore.RoleAdd.specTB (GF := GF) (hG := hG))
    (hUserGrantRole : auth.authStore.UserGrantRole.specTB (GF := GF) (hG := hG))
    (hRoleGrantPermission : auth.authStore.RoleGrantPermission.specTB (GF := GF) (hG := hG))
    (hAuthn : auth.authStore.Authenticate.specTB (GF := GF) (hG := hG))
    (st : Loc) (R : IProp GF) (M : auth.AuthMode) (P : IProp GF) (f : val) (T : IProp GF)
    (Ψ : go_etcd_io.etcd.server.v3.auth.AuthBackend → IProp GF) [hΨ : ∀ be, Persistent (Ψ be)] :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ auth.authInv st R M ⊢
      isAuthStepsX (auth.authIface st) P f M (auth.tieRes st M)
        iprop((∃ be : go_etcd_io.etcd.server.v3.auth.AuthBackend, ((auth.aF go!"be" st ↦{DFrac.own (1 : Qp).half} be ∗
          auth.authWBackendOk be M P f T) ∗ T) ∗ Ψ be) ∗ auth.tpAdmin st M) (auth.authRd st R M) := by
  iintro ⟨#Hpkg, #Hinv⟩
  iunfold isAuthStepsX
  iexists (interface.mk (go.GoType.PointerType auth.authStore.ty) #st)
  isplitr
  · ipureintro; rfl
  isplitr
  · iintro !> %hs %Pre %Q %Post %Φ !> ⟨%Hon, Ho, HX, ⟨⟨%be, ⟨Hbe, HT⟩, #HΨ⟩, HA⟩, Hcs, %Hok, #Hcap⟩ HΦ
    iunfold auth.tieRes at HX
    icases HX with ⟨%b0, %sc0, Hfl, #Hev, Hca, #Hs, %Ht⟩
    ihave #Hcap := auth.capNextM_authEnableOwn_at M hs b0
      (fun γa hM stl hl => by subst hM; exact ((Ht stl hl).1).symm) $$ Hcap
    ihave HWR : auth.authWRxB st M P f T b0 sc0 be $$ [Hbe HT Hfl Hca]
    · iunfold auth.authWRxB; iframe; iframe #
    iapply (hEnable st R M P f T hs Pre Q Post b0 sc0 be) $$ [Ho HWR HA Hcs]
    · iframe; iframe #; ipureintro; exact ⟨Hon, Hok⟩
    iintro !> %err ⟨%b, %sc, HA, HPP, HWR, %en, %Hen, #Hv, Hout⟩
    iunfold auth.authWRxB at HWR
    icases HWR with ⟨Hbe, HT, Hfl, #Hev', Hca, #Hs'⟩
    ihave Hout := auth.adminOutP_tieRes st M hs _ _ err b0 sc0 b sc Ht $$ [Hfl Hca Hout]
    · iframe; iframe #
    -- (E3c) the flag read is the admin side's half, tied to the latest state
    ihave Hout := adminOutX_rel M _ hs _ (authEnableR M en) _ err
      (fun stl o hl hR => ⟨fun γa hM => by
        subst hM; subst Hen; exact ((Ht stl hl).1).symm, hR⟩) $$ Hout
    icases adminOutX_applyErrIs M _ hs _ _ err $$ [$Hpkg $Hout] with ⟨Hout, #Ha⟩
    iapply HΦ
    iframe HPP HA Ha
    isplitl [Hbe HT]
    · iexists be; iframe Hbe HT HΨ
    iexists en; iframe Hv; iexact Hout
  isplitr
  · iintro !> %hs %Pre %Q %Post %r %name %Φ !> ⟨#Hr, #Hsure, %Hn, Ho, HX, ⟨⟨%be, ⟨Hbe, HT⟩, #HΨ⟩, HA⟩, Hcs, %Hok, #Hcap⟩ HΦ
    iunfold auth.tieRes at HX
    icases HX with ⟨%b0, %sc0, Hfl, #Hev, Hca, #Hs, %Ht⟩
    ihave HWR : auth.authWRxB st M P f T b0 sc0 be $$ [Hbe HT Hfl Hca]
    · iunfold auth.authWRxB; iframe; iframe #
    iapply (hUserAdd st R M P f T hs Pre Q Post r name b0 sc0 be) $$ [Ho HWR Hcs]
    · iframe; iframe #; isplitr
      · ipureintro; exact Hn
      ipureintro; exact Hok
    iintro !> %resp %err ⟨%b, %sc, HPP, HWR, Hresp, Hout⟩
    iunfold auth.authWRxB at HWR
    icases HWR with ⟨Hbe, HT, Hfl, #Hev', Hca, #Hs'⟩
    ihave Hout := auth.adminOutP_tieRes st M hs _ _ err b0 sc0 b sc Ht $$ [Hfl Hca Hout]
    · iframe; iframe #
    icases adminOutX_applyErrIs M _ hs _ _ err $$ [$Hpkg $Hout] with ⟨Hout, #Ha⟩
    iapply HΦ
    iframe HPP HA Ha Hresp
    isplitl [Hbe HT]
    · iexists be; iframe Hbe HT HΨ
    iexact Hout
  isplitr
  · iintro !> %hs %Pre %Q %Post %r %name %Φ !> ⟨#Hr, %Hn, Ho, HX, ⟨⟨%be, ⟨Hbe, HT⟩, #HΨ⟩, HA⟩, Hcs, %Hok, #Hcap⟩ HΦ
    iunfold auth.tieRes at HX
    icases HX with ⟨%b0, %sc0, Hfl, #Hev, Hca, #Hs, %Ht⟩
    ihave HWR : auth.authWRxB st M P f T b0 sc0 be $$ [Hbe HT Hfl Hca]
    · iunfold auth.authWRxB; iframe; iframe #
    iapply (hRoleAdd st R M P f T hs Pre Q Post r name b0 sc0 be) $$ [Ho HWR Hcs]
    · iframe; iframe #; isplitr
      · ipureintro; exact Hn
      ipureintro; exact Hok
    iintro !> %resp %err ⟨%b, %sc, HPP, HWR, Hresp, Hout⟩
    iunfold auth.authWRxB at HWR
    icases HWR with ⟨Hbe, HT, Hfl, #Hev', Hca, #Hs'⟩
    ihave Hout := auth.adminOutP_tieRes st M hs _ _ err b0 sc0 b sc Ht $$ [Hfl Hca Hout]
    · iframe; iframe #
    icases adminOutX_applyErrIs M _ hs _ _ err $$ [$Hpkg $Hout] with ⟨Hout, #Ha⟩
    iapply HΦ
    iframe HPP HA Ha Hresp
    isplitl [Hbe HT]
    · iexists be; iframe Hbe HT HΨ
    iexact Hout
  isplitr
  · iintro !> %hs %Pre %Q %Post %r %user %role %Φ !> ⟨#Hr, %Hn, Ho, HX, ⟨⟨%be, ⟨Hbe, HT⟩, #HΨ⟩, HA⟩, Hcs, %Hb, %Hok, #Hcap⟩ HΦ
    iunfold auth.tieRes at HX
    icases HX with ⟨%b0, %sc0, Hfl, #Hev, Hca, #Hs, %Ht⟩
    ihave HWR : auth.authWRxB st M P f T b0 sc0 be $$ [Hbe HT Hfl Hca]
    · iunfold auth.authWRxB; iframe; iframe #
    iapply (hUserGrantRole st R M P f T hs Pre Q Post r user role b0 sc0 be) $$ [Ho HWR Hcs]
    · iframe; iframe #; isplitr
      · ipureintro; exact Hn
      isplitr
      · ipureintro; exact Hb
      ipureintro; exact Hok
    iintro !> %resp %err ⟨%b, %sc, HPP, HWR, Hresp, Hout⟩
    iunfold auth.authWRxB at HWR
    icases HWR with ⟨Hbe, HT, Hfl, #Hev', Hca, #Hs'⟩
    ihave Hout := auth.adminOutP_tieRes st M hs _ _ err b0 sc0 b sc Ht $$ [Hfl Hca Hout]
    · iframe; iframe #
    icases adminOutX_applyErrIs M _ hs _ _ err $$ [$Hpkg $Hout] with ⟨Hout, #Ha⟩
    iapply HΦ
    iframe HPP HA Ha Hresp
    isplitl [Hbe HT]
    · iexists be; iframe Hbe HT HΨ
    iexact Hout
  isplitr
  · iintro !> %hs %Pre %Q %Post %r %name %w %Φ !> ⟨#Hr, %Hn, Ho, HX, ⟨⟨%be, ⟨Hbe, HT⟩, #HΨ⟩, HA⟩, Hcs, %Hok, #Hcap⟩ HΦ
    iunfold auth.tieRes at HX
    icases HX with ⟨%b0, %sc0, Hfl, #Hev, Hca, #Hs, %Ht⟩
    ihave HWR : auth.authWRxB st M P f T b0 sc0 be $$ [Hbe HT Hfl Hca]
    · iunfold auth.authWRxB; iframe; iframe #
    iapply (hRoleGrantPermission st R M P f T hs Pre Q Post r name w b0 sc0 be) $$ [Ho HWR Hcs]
    · iframe; iframe #; isplitr
      · ipureintro; exact Hn
      ipureintro; exact Hok
    iintro !> %resp %err ⟨%b, %sc, HPP, HWR, Hresp, Hout⟩
    iunfold auth.authWRxB at HWR
    icases HWR with ⟨Hbe, HT, Hfl, #Hev', Hca, #Hs'⟩
    ihave Hout := auth.adminOutP_tieRes st M hs _ _ err b0 sc0 b sc Ht $$ [Hfl Hca Hout]
    · iframe; iframe #
    icases adminOutX_applyErrIs M _ hs _ _ err $$ [$Hpkg $Hout] with ⟨Hout, #Ha⟩
    iapply HΦ
    iframe HPP HA Ha Hresp
    isplitl [Hbe HT]
    · iexists be; iframe Hbe HT HΨ
    iexact Hout
  -- (C1's A2) `Authenticate`: the store's `specTB`, which keeps the backend and the halves
  · iintro !> %hs %Pre %Q %Post %ctx %name %pw %Φ !> ⟨%Hon, HRD, Ho, HX, ⟨⟨%be, ⟨Hbe, HT⟩, #HΨ⟩, HA⟩, Hcs, Hctx⟩ HΦ
    iunfold auth.authRd at HRD
    icases HRD with ⟨Hen, HRD'⟩
    iunfold auth.tieRes at HX
    icases HX with ⟨%b0, %sc0, Hfl, #Hev, Hca, #Hs, %Ht⟩
    ihave HWR : auth.authWRxB st M P f T b0 sc0 be $$ [Hbe HT Hfl Hca]
    · iunfold auth.authWRxB; iframe; iframe #
    iapply (hAuthn st R M P f T hs Pre Q Post ctx name pw b0 sc0 be) $$ [Hen Ho HWR Hcs Hctx]
    · iframe; iframe #
    iintro !> %resp %err ⟨HPP, Hen, Ho, HWR, Hau, #He⟩
    iunfold auth.authWRxB at HWR
    icases HWR with ⟨Hbe, HT, Hfl, -, Hca, -⟩
    iapply HΦ
    iframe HPP Ho Hau He HA
    isplitl [Hen HRD']
    · iunfold auth.authRd; iframe
    isplitl [Hfl Hca]
    · iunfold auth.tieRes; iexists b0, sc0; iframe; iframe #; ipureintro; exact Ht
    iexists be; iframe Hbe HT HΨ

end proof


section stepSpecs
variable [GooseExts] [GooseSemantics] [GooseInterp]
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
        auth.userAddSure r ∗ auth.authOwn E.authMode hs ∗ X hs ∗ W ∗
        auth.capNextM E.authMode hs (auth.stepOf (auth.userAddF name)) ∗
        apply.mPre E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) info log Pre Q Post }}
      (App (Val (p @!! go.GoType.PointerType applierV3backend.ty @!! go!"UserAdd")) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      apply.mPost E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) log Pre Post ∗
      applyErrIs err ∗ W ∗
      auth.adminOutX E.authMode (ownX E.authMode X) hs (auth.stepOf (auth.userAddF name)) auth.noExtra err }}

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
        auth.capNextM E.authMode hs (auth.stepOf (auth.roleAddF name)) ∗
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
        auth.capNextM E.authMode hs (auth.userGrantRoleR user role) ∗
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
        auth.capNextM E.authMode hs (auth.roleGrantPermissionR name w) ∗
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
        auth.capNextM E.authMode hs auth.authEnableOwnR ∗
        apply.mPre E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) info log Pre Q Post }}
      (App (Val (p @!! go.GoType.PointerType applierV3backend.ty @!! go!"AuthEnable")) (Val #()))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      apply.mPost E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) log Pre Post ∗
      applyErrIs err ∗ W ∗
      ∃ en : Bool, auth.enabledVerdict E.authMode en ∗
        auth.adminOutX E.authMode (ownX E.authMode X) hs (authEnableR E.authMode en) auth.noExtra err }}

/-- **`a.UserAdd(r)` in the mode `on γa`, from the fuel, carrying `X`** (`UserAdd.fuelSpec`'s). -/
abbrev applierV3backend.UserAdd.fuelSpecX : Prop :=
  ∀ (E : AEnv GF) (γa : auth.AuthNames) (X : List auth.AuthState → IProp GF) (W : IProp GF)
    (p r : Loc) (log : mvcc.Log) (Pre Q Post : IProp GF) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (hs : List auth.AuthState) (name : GoString),
    E.authMode = .on γa → receiptBound GF ≤ 2 ^ 48 → name.length ≤ backend.maxKeySize →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
        apply.backendIs E p ∗ backendAuthStepsX E p X W ∗ auth.userAddReqIs r name ∗
        auth.userAddSure r ∗ auth.authOwnFu γa hs ∗ X hs ∗ ⧗ 1 ∗ W ∗
        auth.capNextM (.on γa) hs (auth.stepOf (auth.userAddF name)) ∗
        apply.mPre E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) info log Pre Q Post }}
      (App (Val (p @!! go.GoType.PointerType applierV3backend.ty @!! go!"UserAdd")) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      apply.mPost E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) log Pre Post ∗
      applyErrIs err ∗ W ∗
      auth.adminOutX (.on γa) (fun h => iprop(auth.authOwnFu γa h ∗ X h)) hs (auth.stepOf (auth.userAddF name)) auth.noExtra err }}

/-- **`a.RoleAdd(r)` in the mode `on γa`, from the fuel, carrying `X`** (`RoleAdd.fuelSpec`'s). -/
abbrev applierV3backend.RoleAdd.fuelSpecX : Prop :=
  ∀ (E : AEnv GF) (γa : auth.AuthNames) (X : List auth.AuthState → IProp GF) (W : IProp GF)
    (p r : Loc) (log : mvcc.Log) (Pre Q Post : IProp GF) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (hs : List auth.AuthState) (name : GoString),
    E.authMode = .on γa → receiptBound GF ≤ 2 ^ 48 → name.length ≤ backend.maxKeySize →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
        apply.backendIs E p ∗ backendAuthStepsX E p X W ∗ auth.roleAddReqIs r name ∗
        auth.authOwnFu γa hs ∗ X hs ∗ ⧗ 1 ∗ W ∗
        auth.capNextM (.on γa) hs (auth.stepOf (auth.roleAddF name)) ∗
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
        auth.capNextM (.on γa) hs (auth.userGrantRoleR user role) ∗
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
        auth.capNextM (.on γa) hs (auth.roleGrantPermissionR name w) ∗
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
        auth.capNextM (.on γa) hs auth.authEnableOwnR ∗
        apply.mPre E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) info log Pre Q Post }}
      (App (Val (p @!! go.GoType.PointerType applierV3backend.ty @!! go!"AuthEnable")) (Val #()))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      apply.mPost E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) log Pre Post ∗
      applyErrIs err ∗ W ∗
      ∃ en : Bool, auth.enabledVerdict E.authMode en ∗
        auth.adminOutX (.on γa) (fun h => iprop(auth.authOwnFu γa h ∗ X h)) hs
          (authEnableR E.authMode en) auth.noExtra err }}

/-- **What an `Authenticate` returns, with auth on** (C1's A2, 2026-10-28): an error (one of the
auth package's, `auth.authErrOf`) and no response; or no error and the response, owned (the reply
the server sends), whose token is issued to `name` (`auth.tokIssued`). (The margin: the token is
`<prefix>.<x>` at the entry's index, `auth.simpleTok`; no client needs it.) -/
def authnOut (γa : auth.AuthNames) (name : GoString) (resp : Loc) (err : GoInterface) : IProp GF :=
  iprop((⌜err ≠ GoInterface.nil ∧ resp = null⌝ ∗ ∃ e : auth.AuthErr, auth.authErrOf e err) ∨
    ⌜err = GoInterface.nil⌝ ∗ ∃ v : etcdserverpb.AuthenticateResponse,
      resp ↦ v ∗ auth.tokIssued γa v.Token' name)

/-- **`a.Authenticate(r)` with auth on, carrying `X`** (C1's A2, 2026-10-28): the store's
`Authenticate` (`isAuthStepsX`'s) at a context holding the consistent index `x` that
`ConsistentIndex()` returns under the resource it borrows from the critical section's precondition
(`ciSplitAt`) and the request's token prefix, with the right to issue `<prefix>.<x>`
(`auth.tokFresh`); the authority, `X` and `W` back as they were (it writes nothing), the result
`authnOut`. -/
abbrev applierV3backend.Authenticate.specX : Prop :=
  ∀ (E : AEnv GF) (γa : auth.AuthNames) (X : List auth.AuthState → IProp GF) (W : IProp GF)
    (p r : Loc) (log : mvcc.Log) (Pre Q Post : IProp GF) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (hs : List auth.AuthState) (am : AuthenticateModel) (x : w64),
    E.authMode = .on γa →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
        apply.backendIs E p ∗ backendAuthStepsX E p X W ∗ authenticateIs r am ∗
        ciSplitAt E Pre x ∗ auth.tokFresh γa (auth.simpleTok am.simpleToken x) ∗
        auth.authOwn E.authMode hs ∗ X hs ∗ W ∗
        apply.mPre E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) info log Pre Q Post }}
      (App (Val (p @!! go.GoType.PointerType applierV3backend.ty @!! go!"Authenticate")) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      apply.mPost E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) log Pre Post ∗
      applyErrIs err ∗ auth.authOwn E.authMode hs ∗ X hs ∗ W ∗
      authnOut γa am.name resp err }}

end stepSpecs

section applier
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

theorem applierV3backend.UserAdd.wp_stepX
    (hHdr : apply.applierV3backend.newHeader.spec (GF := GF) (hG := hG)) :
    applierV3backend.UserAdd.stepSpecX (GF := GF) (hG := hG) := by
  intro E X W p r log Pre Q Post info hs name hn hok
  wp_start as ⟨#Hb, #Hs, #Hr, #Hsure, Ho, HX, HW, #Hcap, Hpre⟩
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
  · iframe Hcap Hr Hsure; isplitr
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
  wp_start as ⟨#Hb, #Hs, #Hr, Ho, HX, HW, #Hcap, Hpre⟩
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
  · iframe Hcap Hr; isplitr
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
  wp_start as ⟨#Hb, #Hs, #Hr, Ho, HX, HW, #Hcap, Hpre⟩
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
  · iframe Hcap Hr; isplitr
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
  wp_start as ⟨#Hb, #Hs, #Hr, Ho, HX, HW, #Hcap, Hpre⟩
  iunfold apply.mPre at Hpre
  icases Hpre with ⟨Hkv, Hres, Hcs⟩
  iunfold apply.kvOwn at Hkv
  icases Hkv with ⟨Hrd, Hsw, Hknown, Hard⟩
  ihave #Hs' := Hs
  iunfold apply.backendAuthStepsX at Hs'
  icases Hs' with ⟨%opts, #Hopts, #Hst⟩
  iunfold apply.isAuthStepsX at Hst
  icases Hst with ⟨%ai, %Hai, -, -, -, -, #HM, -⟩
  iStructNamed Hopts
  wp_auto
  rw [Hai]
  wp_apply HM $$ %hs %Pre %Q %Post %r %name %w [$Ho $HX $HW $Hcs] as %resp %err ⟨HPP, HW, #HeI, Hresp, Hout⟩
  · iframe Hcap Hr; isplitr
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
  wp_start as ⟨#Hb, #Hs, Ho, HX, HW, #Hcap, Hpre⟩
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
  · iframe Hcap; isplitr
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
    irename «$r0» => Hl
    generalize «$r0_ptr» = l at *
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
  iintro %Φ ⟨#Hpkg, #Hb, #Hs, Hr, Hsure, HOF, HX, Hrc, HW, #Hcap, Hpre⟩ HΦ
  iunfold auth.authOwnFu at HOF
  icases HOF with ⟨Ho, Hf⟩
  ihave Hf := auth.authFuel_charge hs $$ [Hf Hrc]
  · iframe
  icases auth.authFuelT_fuel hs hb $$ Hf with ⟨Hf, %Hk⟩
  obtain ⟨k, Hfk, Hlt⟩ := Hk
  have hok : auth.stepOk E.authMode hs (auth.stepOf (auth.userAddF name)) :=
    hM ▸ auth.stepOk_of_fuel γa hs _ k (auth.stepSmall_userAdd name hn) Hfk Hlt
  iapply (h E X W p r log Pre Q Post info hs name hn hok) $$ [Hr Hsure Ho HX HW Hpre]
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
  iintro %Φ ⟨#Hpkg, #Hb, #Hs, Hr, HOF, HX, Hrc, HW, #Hcap, Hpre⟩ HΦ
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
  iintro %Φ ⟨#Hpkg, #Hb, #Hs, Hr, HOF, HX, Hrc, HW, #Hcap, Hpre⟩ HΦ
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
  iintro %Φ ⟨#Hpkg, #Hb, #Hs, Hr, HOF, HX, Hrc, HW, #Hcap, Hpre⟩ HΦ
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
  iintro %Φ ⟨#Hpkg, #Hb, #Hs, HOF, HX, Hrc, HW, #Hcap, Hpre⟩ HΦ
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
  ihave Hout := auth.adminOutX_fu γa X hs _ _ err (stepSmall_authEnableR _ en) $$ [Hf Hout]
  · iframe
  iapply HΦ
  iframe; iframe #

/-- **`Authenticate.specX`** (C1's A2): the context's two values from `context.WithValue`'s
`Value` (the index at the inner one, the prefix at the outer one, whose key is of another type),
the store's `Authenticate` at the reader resource `kvOwn` lends; the header written into a
response. -/
theorem applierV3backend.Authenticate.wp_specX
    (hWV : context.WithValue.spec (GF := GF) (hG := hG))
    (hHdr : apply.applierV3backend.newHeader.spec (GF := GF) (hG := hG)) :
    applierV3backend.Authenticate.specX (GF := GF) (hG := hG) := by
  intro E γa X W p r log Pre Q Post info hs am x hM
  wp_start as ⟨#Hb, #Hs, #Hr, #HSplit, Hfr, Ho, HX, HW, Hpre⟩
  iunfold apply.mPre at Hpre
  icases Hpre with ⟨Hkv, Hres, Hcs⟩
  iunfold apply.kvOwn at Hkv
  icases Hkv with ⟨Hrd, Hsw, Hknown, HRD, Hwo⟩
  ihave #Hb' := Hb
  iunfold apply.backendIs at Hb'
  icases Hb' with ⟨%opts, #Hopts, #Hok⟩
  iunfold apply.backendOptsOk at Hok
  icases Hok with ⟨-, -, -, -, -, -, -, -, -, #Hci⟩
  iunfold apply.isConsistentIndexer at Hci
  icases Hci with ⟨%cii, %Hcii, #HCI⟩
  ihave #Hs' := Hs
  iunfold apply.backendAuthStepsX at Hs'
  icases Hs' with ⟨%opts', #Hopts', #Hst⟩
  ihave %Hoo := typedPointsto_agree_wand _ _ _ _ _ $$ Hopts Hopts'
  subst Hoo
  iunfold apply.isAuthStepsX at Hst
  icases Hst with ⟨%ai, %Hai, -, -, -, -, -, #HA⟩
  iunfold apply.authenticateIs at Hr
  icases Hr with ⟨%Hrnn, #Hname, #Hpw, #Htok⟩
  iStructNamed Hopts
  wp_auto
  wp_apply context.wp_Background
  rw [Hcii]
  -- the consistent index's resource, lent out of the critical section's precondition
  iunfold mvcc.csContract at Hcs
  icases Hcs with ⟨HPre, #Hhk, Hfin⟩
  iunfold apply.ciSplitAt at HSplit
  icases HSplit $$ HPre with ⟨%C, %HC, HC, HCb⟩
  ihave #HCIC := HCI $$ %C %x
  ihave #HCIC := HCIC $$ []
  · ipureintro; exact HC
  wp_bind (App (Val #(methods cii.ty go!"ConsistentIndex" cii.v)) (Val #()))
  iapply HCIC $$ HC
  inext
  iintro HC
  (try wp_auto)
  ihave HPre := HCb $$ HC
  ihave Hcs : mvcc.csContract E.P E.f Pre Q Post $$ [HPre Hfin]
  · iunfold mvcc.csContract; iframe HPre Hhk Hfin
  wp_apply (hWV context.backgroundCtxVal
      ⟨go_etcd_io.etcd.server.v3.auth.AuthenticateParamIndex.ty, _⟩ _)
    as %c1 ⟨%Hc1, -, -, %c1', %vs1, %Hc1e, -, -, -, -, -, #HV1⟩
  · ipureintro; exact Or.inl rfl
  subst Hc1e
  wp_apply (hWV c1'
      ⟨go_etcd_io.etcd.server.v3.auth.AuthenticateParamSimpleTokenPrefix.ty, _⟩ _)
    as %c2 ⟨%Hc2, -, -, %c2', %vs2, %Hc2e, -, -, -, -, -, #HV2⟩
  · ipureintro; exact Or.inr (Or.inl rfl)
  subst Hc2e
  -- the context the store's `assign` reads: the index at the inner key, the prefix at the outer
  have hty : go_etcd_io.etcd.server.v3.auth.AuthenticateParamIndex.ty ≠
      go_etcd_io.etcd.server.v3.auth.AuthenticateParamSimpleTokenPrefix.ty := by
    simp [go_etcd_io.etcd.server.v3.auth.AuthenticateParamIndex.ty,
      go_etcd_io.etcd.server.v3.auth.AuthenticateParamSimpleTokenPrefix.ty]
  ihave Hctx : auth.authnCtx E.authMode (GoInterface.ok c2') $$ [Hfr]
  · rw [hM]
    iunfold auth.authnCtx
    iexists c2', x, am.simpleToken
    isplitr
    · ipureintro; rfl
    isplitr
    · iintro !> %xk
      iapply HV2 $$ %(interface.mkOk go_etcd_io.etcd.server.v3.auth.AuthenticateParamIndex.ty #xk)
        %(fun w => w = interface.mkOk go.uint64 #x) [] [] []
      · ipureintro; right; intro k' hk'; have h := GoInterface.ok.inj hk'; subst h; exact hty
      · ipureintro; intro h; exact absurd (congrArg GoInterfaceOk.ty (GoInterface.ok.inj h)) hty
      · iintro %hne
        iapply HV1 $$ %(interface.mkOk go_etcd_io.etcd.server.v3.auth.AuthenticateParamIndex.ty #xk)
          %(fun w => w = interface.mkOk go.uint64 #x) [] [] []
        · ipureintro; left; cases xk; rfl
        · ipureintro; intro _; rfl
        · iintro %hne'; exfalso; cases xk; exact hne' rfl
    isplitr
    · iintro !> %xk
      iapply HV2 $$ %(interface.mkOk go_etcd_io.etcd.server.v3.auth.AuthenticateParamSimpleTokenPrefix.ty #xk)
        %(fun w => w = interface.mkOk go.string #am.simpleToken) [] [] []
      · ipureintro; left; cases xk; rfl
      · ipureintro; intro _; rfl
      · iintro %hne; exfalso; cases xk; exact hne rfl
    iunfold auth.freshOk; iexact Hfr
  rw [Hai]
  wp_apply HA $$ %hs %Pre %Q %Post %(GoInterface.ok c2') %am.name %am.password
      [$HRD $Ho $HX $HW $Hcs $Hctx] as %resp %err ⟨HPP, HRD, Ho, HX, HW, Hau, #He⟩
  · ipureintro; rw [hM]; rfl
  ihave #HeI : applyErrIs err $$ []
  · icases He with (%He | ⟨%e, #He⟩)
    · subst He; iapply applyErrIs_nil
    · ihave #Hapk : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth $$ []
      · iPkgInit
      iapply authErrOf_applyErrIs e err $$ [Hapk He]
      iframe #
  rw [hM]
  iunfold auth.authenticated at Hau
  wp_if_destruct
  · -- no response: an error
    icases Hau with (⟨%Hne, -⟩ | ⟨-, %tok, %v, Hv, -⟩)
    · iapply HΦ
      iframe HeI Ho HX HW
      isplitl [Hrd Hsw Hknown HRD Hwo HPP]
      · iapply apply.mPost_backend; iunfold apply.kvOwn; iframe
      iunfold apply.authnOut
      ileft
      isplitr
      · ipureintro; exact ⟨Hne, rfl⟩
      icases He with (%He | He)
      · exact absurd He Hne
      iexact He
    · ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hv
      exact absurd rfl Hnn
  · -- a response: the token issued, the header written
    icases Hau with (⟨-, %Hn⟩ | ⟨%He0, %tok, %v, Hv, %Htv, #Hiss, -⟩)
    · exact absurd Hn Hif
    wp_apply (hHdr E p log) $$ [$Hpkg $Hb $Hrd $Hsw] as %h ⟨Hrd, Hsw, -⟩
    iapply HΦ
    iframe HeI Ho HX HW
    isplitl [Hrd Hsw Hknown HRD Hwo HPP]
    · iapply apply.mPost_backend; iunfold apply.kvOwn; iframe
    iunfold apply.authnOut
    iright
    isplitr
    · ipureintro; exact He0
    iexists _
    iframe Hv
    subst Htv
    iunfold auth.tokOk at Hiss
    iexact Hiss

end applier

end apply
end EtcdGrove
end Perennial
