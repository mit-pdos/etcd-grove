/-
**The apply thread's tie kept across the admin operations** (the auth plan's E2s, 2026-10-26;
`notes/decisions.md`, "E2s of the auth plan"). E2r's checks at the latest state (`Latest.lean`)
take the admin side's halves of the flag (`flagAt`) and the cache (`cacheAt`) tied to the latest
state (`latestTie`). The admin operations' specs give `authWR` back with those halves' values
hidden; `X.specT` gives them exposed (`authWRx`), with the tie carried from the history before to
the history after (`tieStep`, inside the result: `adminOutP`): an operation sets the flag
(`AuthEnable`, `AuthDisable`) and refreshes the cache from the state it commits, except `RoleAdd`,
whose new role has no permission and no user (`cacheAt_congr`). `X.spec` follows (`X.spec_of_T`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.LatestAdmin
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__AuthEnable
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__AuthDisable
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__UserAdd
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__UserDelete
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__UserChangePassword
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__UserGrantRole
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__UserRevokeRole
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__RoleAdd
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__RoleDelete
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__RoleGrantPermission
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__RoleRevokePermission

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth auth go_etcd_io.etcd.api.v3

namespace auth

section pure
variable [ext : FfiSyntax]

/-- The history after an outcome: the next state appended, else the same. -/
def histAfter (hs : List AuthState) : Outcome → List AuthState
  | .next st' => hs ++ [st']
  | _ => hs

/-- **The tie carried by a step**: if the halves before (`b0`, `sc0`) were tied to the latest state
of `hs`, those after (`b`, `sc`) are tied to the latest state of the history after, `hs'`. -/
def tieStep (M : AuthMode) (hs : List AuthState) (b0 : Bool) (sc0 : AuthState) (b : Bool)
    (sc : AuthState) (hs' : List AuthState) : Prop :=
  latestTie M hs b0 sc0 → latestTie M hs' b sc

theorem tieStep_same (M : AuthMode) (hs : List AuthState) (b : Bool) (sc : AuthState) :
    tieStep M hs b sc b sc hs := fun h => h

/-- The cache refreshed from the state after (`sc`, the latest of `hs'`), the flag kept: the step
kept the flag. -/
theorem tieStep_refresh (M : AuthMode) (hs hs' : List AuthState) (b0 : Bool) (sc0 sc st0 : AuthState)
    (hl0 : histLast M hs st0) (hl' : histLast M hs' sc) (he : sc.enabled = st0.enabled) :
    tieStep M hs b0 sc0 b0 sc hs' := by
  cases M with
  | on γa =>
    intro ht stl hl
    have h1 : hs'.getLast? = some sc := hl'
    rw [h1] at hl; cases hl
    refine ⟨?_, fun _ => rfl⟩
    rw [he]; exact (ht st0 hl0).1
  | off => intro _; trivial
  | any => intro _; trivial

/-- The flag set to the state after's (`b`), the cache that state's when the flag is set. -/
theorem tieStep_set (M : AuthMode) (hs hs' : List AuthState) (b0 : Bool) (sc0 : AuthState)
    (b : Bool) (sc s' : AuthState) (hl' : histLast M hs' s') (hb : b = s'.enabled)
    (hc : b = true → sc = s') : tieStep M hs b0 sc0 b sc hs' := by
  cases M with
  | on γa =>
    intro _ stl hl
    have h1 : hs'.getLast? = some s' := hl'
    rw [h1] at hl; cases hl
    exact ⟨hb, hc⟩
  | off => intro _; trivial
  | any => intro _; trivial

/-- The flag and the cache kept, auth disabled: the step kept the flag. -/
theorem tieStep_keep (M : AuthMode) (hs hs' : List AuthState) (b0 : Bool) (sc0 st0 s' : AuthState)
    (hl0 : histLast M hs st0) (hl' : histLast M hs' s') (he : s'.enabled = st0.enabled)
    (hb : b0 = false) : tieStep M hs b0 sc0 b0 sc0 hs' := by
  cases M with
  | on γa =>
    intro ht stl hl
    have h1 : hs'.getLast? = some s' := hl'
    rw [h1] at hl; cases hl
    refine ⟨?_, fun h => absurd (hb ▸ h) (by simp)⟩
    rw [he]; exact (ht st0 hl0).1
  | off => intro _; trivial
  | any => intro _; trivial

/-- The flag and the cache kept, unless the cache was the state before's with the flag set (then
the step must refresh it, `cacheAt_congr`): the step kept the flag. -/
theorem tieStep_keep' (M : AuthMode) (hs hs' : List AuthState) (b0 : Bool) (sc0 st0 s' : AuthState)
    (hl0 : histLast M hs st0) (hl' : histLast M hs' s') (he : s'.enabled = st0.enabled)
    (hc : ¬ (b0 = true ∧ sc0 = st0)) : tieStep M hs b0 sc0 b0 sc0 hs' := by
  cases M with
  | on γa =>
    intro ht stl hl
    have h1 : hs'.getLast? = some s' := hl'
    rw [h1] at hl; cases hl
    obtain ⟨hb, hcs⟩ := ht st0 hl0
    refine ⟨by rw [he]; exact hb, fun h => absurd ⟨h, hcs h⟩ hc⟩
  | off => intro _; trivial
  | any => intro _; trivial

/-- A new role without permissions changes no user's permissions. -/
theorem userPerms_putRole_empty (st : AuthState) (name : GoString) (h : st.roles !! name = none)
    (u : User) : userPerms (putRole st name []) u = userPerms st u := by
  unfold userPerms
  congr 1; funext r
  by_cases hr : r = name
  · subst hr; simp only [putRole, GMap.lookup_insert, h, Option.getD_some, Option.getD_none]
  · simp only [putRole, GMap.lookup_insert_ne _ _ (Ne.symm hr)]

/-- The tie gives the latest state's flag. -/
theorem latestTie_flag (M : AuthMode) (hs : List AuthState) (b : Bool) (sc st0 : AuthState)
    (ht : latestTie M hs b sc) (hl : histLast M hs st0) (hon : M.isOn = true) (hany : M ≠ .any) :
    b = st0.enabled ∧ (b = true → sc = st0) := by
  cases M with
  | on γa => exact ht st0 hl
  | off => cases hon
  | any => exact absurd rfl hany

end pure

section res
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- **`authWR` with the halves' values exposed**: the flag's half at `b` (with its verdict) and
the cache's half at `sc` (a recorded state). -/
def authWRx (st : Loc) (M : AuthMode) (P : IProp GF) (f : val) (T : IProp GF) (b : Bool)
    (sc : AuthState) : IProp GF :=
  iprop((∃ be : AuthBackend, aF go!"be" st ↦{DFrac.own (1 : Qp).half} be ∗ authWBackendOk be M P f T) ∗
    T ∗ flagAt st M b ∗ enabledVerdict M b ∗ cacheAt st sc ∗ authSnap M sc)

theorem authWR_of_x (st : Loc) (M : AuthMode) (P : IProp GF) (f : val) (T : IProp GF) (b : Bool)
    (sc : AuthState) : authWRx (GF := GF) st M P f T b sc ⊢ authWR st M P f T := by
  unfold authWRx authWR
  iintro ⟨Hbe, HT, Hfl, #Hev, Hca, #Hs⟩
  iframe Hbe HT
  isplitl [Hfl]
  · iapply flagAt_enabledHalf; iframe Hfl Hev
  · iapply (cacheHalf_of_at st M sc) $$ Hca Hs

theorem authWR_to_x (st : Loc) (M : AuthMode) (P : IProp GF) (f : val) (T : IProp GF) :
    authWR (GF := GF) st M P f T ⊢ ∃ b sc, authWRx st M P f T b sc := by
  unfold authWRx authWR
  iintro ⟨Hbe, HT, Hen, Hca⟩
  ihave ⟨%b, Hfl, #Hev⟩ := enabledHalf_flagAt st M $$ Hen
  iunfold cacheHalf at Hca
  icases Hca with ⟨%sc, Hca, #Hs⟩
  iexists b, sc
  iframe Hbe HT Hfl Hev Hca Hs

/-- The admin side's authority records its latest state (`authOwn_latestSnap`), as `authSnap`. -/
theorem authSnap_of_own_last (M : AuthMode) (hs : List AuthState) (s : AuthState)
    (hl : histLast M hs s) : authOwn (GF := GF) M hs ⊢ authOwn M hs ∗ authSnap M s := by
  iintro Hown
  ihave ⟨Hown, #Hs⟩ := authOwn_latestSnap M hs $$ Hown
  iframe Hown
  cases M with
  | on γa =>
    simp only [latestSnap, authSnap]
    icases Hs with ⟨%i, %stl, %Hl, #Hst⟩
    have h1 : hs.getLast? = some s := hl
    rw [h1] at Hl; cases Hl
    iexists i; iexact Hst
  | off => simp only [authSnap]; ipureintro; exact hl
  | any => simp only [authSnap]; itrivial

/-- **An admin operation's result with the property `Pt` of the history after** (`adminOut`'s,
`Steps.lean`). -/
def adminOutP (M : AuthMode) (hs : List AuthState) (R : StepRel) (extra : AuthErr → Prop)
    (err : GoInterface) (Pt : List AuthState → Prop) : IProp GF :=
  iprop((∃ e : AuthErr, ⌜Pt hs⌝ ∗ ⌜extra e⌝ ∗ authOwn M hs ∗ authErrOf e err) ∨
    (∃ (st : AuthState) (o : Outcome), ⌜Pt (histAfter hs o)⌝ ∗ ⌜histLast M hs st ∧ R st o⌝ ∗
      outRes M hs o err))

theorem adminOutP_adminOut (M : AuthMode) (hs : List AuthState) (R : StepRel)
    (extra : AuthErr → Prop) (err : GoInterface) (Pt : List AuthState → Prop) :
    adminOutP (GF := GF) M hs R extra err Pt ⊢ adminOut M hs R extra err := by
  unfold adminOutP adminOut
  iintro (⟨%e, -, %H, Ho, He⟩ | ⟨%st, %o, -, %H, Ho⟩)
  · ileft; iexists e; iframe Ho He; ipureintro; exact H
  · iright; iexists st, o; iframe Ho; ipureintro; exact H

set_option synthInstance.maxSize 512 in
/-- The cache's map of a state is that of another with the same users and permissions. -/
theorem cacheAt_congr (st : Loc) (sa sb : AuthState) (hu : sa.users = sb.users)
    (hp : ∀ u : User, userPerms sa u = userPerms sb u) :
    cacheAt (GF := GF) st sa ⊢ cacheAt st sb := by
  unfold cacheAt cacheOf
  iintro ⟨%mp, %Mp, Hf, #HM, %Hdom, #Hall⟩
  iexists mp, Mp
  iframe Hf HM
  isplitr
  · ipureintro; intro u; rw [← hu]; exact Hdom u
  iapply (BigSepM.bigSepM_mono (Φ := fun (u : GoString) (p : Loc) =>
      iprop(∃ Lr Lw, permsAt p Lr Lw ∗ ⌜cacheEntryIs sa u Lr Lw⌝))) ?_ $$ Hall
  intro u p _
  iintro ⟨%Lr, %Lw, Hp, %He⟩
  iexists Lr, Lw
  iframe Hp
  ipureintro
  obtain ⟨roles, hr, h1, h2⟩ := He
  exact ⟨roles, hu ▸ hr, hp roles ▸ h1, hp roles ▸ h2⟩

end res

end auth

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- `AuthEnable.spec` with the admin side's halves of the flag and the cache at `b0`/`sc0` exposed (the
flag it read the admin side's half, `en = b0`: the auth plan's E3c) and
kept tied to the latest state (`tieStep`). -/
abbrev auth.authStore.AuthEnable.specT : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : AuthMode) (P : IProp GF) (f : val) (T : IProp GF)
    (hs : List AuthState) (Pre Q Post : IProp GF) (b0 : Bool) (sc0 : AuthState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗ ⌜M.isOn = true⌝ ∗ authOwn M hs ∗ authWRx st M P f T b0 sc0 ∗ tpAdmin st M ∗ mvcc.csContract P f Pre Q Post ∗
      ⌜∀ en : Bool, stepOk M hs (stepOf (authEnableF en))⌝ }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"AuthEnable")) (Val #()))
  {{ (err : GoInterface), RET #err; ∃ (b : Bool) (sc : AuthState), tpAdmin st M ∗ (Post ∨ Pre) ∗ authWRx st M P f T b sc ∗
      ∃ en : Bool, ⌜en = b0⌝ ∗ enabledVerdict M en ∗ adminOutP M hs (stepOf (authEnableF en)) noExtra err (tieStep M hs b0 sc0 b sc) }}

/-- `AuthDisable.spec` with the admin side's halves of the flag and the cache at `b0`/`sc0` exposed and
kept tied to the latest state (`tieStep`). -/
abbrev auth.authStore.AuthDisable.specT : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : AuthMode) (P : IProp GF) (f : val) (T : IProp GF)
    (hs : List AuthState) (Pre Q Post : IProp GF) (b0 : Bool) (sc0 : AuthState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗ authOwn M hs ∗ authWRx st M P f T b0 sc0 ∗ tpAdmin st M ∗ mvcc.csContract P f Pre Q Post ∗
      ⌜∀ en : Bool, stepOk M hs (stepOf (authDisableF en))⌝ }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"AuthDisable")) (Val #()))
  {{ RET #(); ∃ (b : Bool) (sc : AuthState), tpAdmin st M ∗ (Post ∨ Pre) ∗ authWRx st M P f T b sc ∗
      ∃ en : Bool, enabledVerdict M en ∗ adminOutP M hs (stepOf (authDisableF en)) noExtra GoInterface.nil (tieStep M hs b0 sc0 b sc) }}

/-- `UserAdd.spec` with the admin side's halves of the flag and the cache at `b0`/`sc0` exposed and
kept tied to the latest state (`tieStep`). -/
abbrev auth.authStore.UserAdd.specT : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : AuthMode) (P : IProp GF) (f : val) (T : IProp GF)
    (hs : List AuthState) (Pre Q Post : IProp GF) (r : Loc) (name : GoString) (b0 : Bool) (sc0 : AuthState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗ userAddReqIs r name ∗ ⌜name.length ≤ backend.maxKeySize⌝ ∗ authOwn M hs ∗ authWRx st M P f T b0 sc0 ∗ mvcc.csContract P f Pre Q Post ∗
      ⌜stepOk M hs (stepOf (userAddF name))⌝ }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"UserAdd")) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); ∃ (b : Bool) (sc : AuthState), (Post ∨ Pre) ∗ authWRx st M P f T b sc ∗
      respOk etcdserverpb.AuthUserAddResponse resp err ∗ adminOutP M hs (stepOf (userAddF name)) (fun e => e = .noPasswordUser) err (tieStep M hs b0 sc0 b sc) }}

/-- `UserDelete.spec` with the admin side's halves of the flag and the cache at `b0`/`sc0` exposed and
kept tied to the latest state (`tieStep`). -/
abbrev auth.authStore.UserDelete.specT : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : AuthMode) (P : IProp GF) (f : val) (T : IProp GF)
    (hs : List AuthState) (Pre Q Post : IProp GF) (r : Loc) (name : GoString) (b0 : Bool) (sc0 : AuthState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗ userDeleteReqIs r name ∗ authOwn M hs ∗ authWRx st M P f T b0 sc0 ∗ tpAdmin st M ∗ mvcc.csContract P f Pre Q Post ∗
      ⌜∀ en : Bool, stepOk M hs (stepOf (userDeleteF en name))⌝ }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"UserDelete")) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); ∃ (b : Bool) (sc : AuthState), tpAdmin st M ∗ (Post ∨ Pre) ∗ authWRx st M P f T b sc ∗
      respOk etcdserverpb.AuthUserDeleteResponse resp err ∗ ∃ en : Bool, enabledVerdict M en ∗ adminOutP M hs (stepOf (userDeleteF en name)) noExtra err (tieStep M hs b0 sc0 b sc) }}

/-- `UserChangePassword.spec` with the admin side's halves of the flag and the cache at `b0`/`sc0` exposed and
kept tied to the latest state (`tieStep`). -/
abbrev auth.authStore.UserChangePassword.specT : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : AuthMode) (P : IProp GF) (f : val) (T : IProp GF)
    (hs : List AuthState) (Pre Q Post : IProp GF) (r : Loc) (name : GoString) (b0 : Bool) (sc0 : AuthState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗ userChangePasswordReqIs r name ∗ ⌜name.length ≤ backend.maxKeySize⌝ ∗ authOwn M hs ∗ authWRx st M P f T b0 sc0 ∗ tpAdmin st M ∗ mvcc.csContract P f Pre Q Post ∗
      ⌜stepOk M hs (stepOf (userChangePasswordF name))⌝ }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"UserChangePassword")) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); ∃ (b : Bool) (sc : AuthState), tpAdmin st M ∗ (Post ∨ Pre) ∗ authWRx st M P f T b sc ∗
      respOk etcdserverpb.AuthUserChangePasswordResponse resp err ∗ adminOutP M hs (stepOf (userChangePasswordF name)) (fun e => e = .noPasswordUser) err (tieStep M hs b0 sc0 b sc) }}

/-- `UserGrantRole.spec` with the admin side's halves of the flag and the cache at `b0`/`sc0` exposed and
kept tied to the latest state (`tieStep`). -/
abbrev auth.authStore.UserGrantRole.specT : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : AuthMode) (P : IProp GF) (f : val) (T : IProp GF)
    (hs : List AuthState) (Pre Q Post : IProp GF) (r : Loc) (user role : GoString) (b0 : Bool) (sc0 : AuthState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗
      userGrantRoleReqIs r user role ∗ ⌜user.length ≤ backend.maxKeySize⌝ ∗ authOwn M hs ∗
      authWRx st M P f T b0 sc0 ∗ mvcc.csContract P f Pre Q Post ∗
      ⌜∀ (sta : AuthState) (u : User), histLast M hs sta → sta.users !! user = some u →
        u.length < 2 ^ 62⌝ ∗
      ⌜stepOk M hs (userGrantRoleR user role)⌝ }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"UserGrantRole")) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); ∃ (b : Bool) (sc : AuthState), (Post ∨ Pre) ∗ authWRx st M P f T b sc ∗
      respOk etcdserverpb.AuthUserGrantRoleResponse resp err ∗
      adminOutP M hs (userGrantRoleR user role) noExtra err (tieStep M hs b0 sc0 b sc) }}

/-- `UserRevokeRole.spec` with the admin side's halves of the flag and the cache at `b0`/`sc0` exposed and
kept tied to the latest state (`tieStep`). -/
abbrev auth.authStore.UserRevokeRole.specT : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : AuthMode) (P : IProp GF) (f : val) (T : IProp GF)
    (hs : List AuthState) (Pre Q Post : IProp GF) (r : Loc) (name role : GoString) (b0 : Bool) (sc0 : AuthState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗
      userRevokeRoleReqIs r name role ∗ ⌜name.length ≤ backend.maxKeySize⌝ ∗ authOwn M hs ∗
      authWRx st M P f T b0 sc0 ∗ mvcc.csContract P f Pre Q Post ∗
      ⌜∀ en : Bool, stepOk M hs (stepOf (userRevokeRoleF en name role))⌝ }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"UserRevokeRole")) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); ∃ (b : Bool) (sc : AuthState), (Post ∨ Pre) ∗ authWRx st M P f T b sc ∗
      respOk etcdserverpb.AuthUserRevokeRoleResponse resp err ∗ ∃ en : Bool, enabledVerdict M en ∗
      adminOutP M hs (stepOf (userRevokeRoleF en name role)) noExtra err (tieStep M hs b0 sc0 b sc) }}

/-- `RoleAdd.spec` with the admin side's halves of the flag and the cache at `b0`/`sc0` exposed and
kept tied to the latest state (`tieStep`). -/
abbrev auth.authStore.RoleAdd.specT : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : AuthMode) (P : IProp GF) (f : val) (T : IProp GF)
    (hs : List AuthState) (Pre Q Post : IProp GF) (r : Loc) (name : GoString) (b0 : Bool) (sc0 : AuthState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗ roleAddReqIs r name ∗ ⌜name.length ≤ backend.maxKeySize⌝ ∗ authOwn M hs ∗ authWRx st M P f T b0 sc0 ∗ mvcc.csContract P f Pre Q Post ∗
      ⌜stepOk M hs (stepOf (roleAddF name))⌝ }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"RoleAdd")) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); ∃ (b : Bool) (sc : AuthState), (Post ∨ Pre) ∗ authWRx st M P f T b sc ∗
      respOk etcdserverpb.AuthRoleAddResponse resp err ∗ adminOutP M hs (stepOf (roleAddF name)) noExtra err (tieStep M hs b0 sc0 b sc) }}

/-- `RoleDelete.spec` with the admin side's halves of the flag and the cache at `b0`/`sc0` exposed and
kept tied to the latest state (`tieStep`). -/
abbrev auth.authStore.RoleDelete.specT : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : AuthMode) (P : IProp GF) (f : val) (T : IProp GF)
    (hs : List AuthState) (Pre Q Post : IProp GF) (r : Loc) (role : GoString) (b0 : Bool) (sc0 : AuthState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗
      roleDeleteReqIs r role ∗ authOwn M hs ∗ authWRx st M P f T b0 sc0 ∗ mvcc.csContract P f Pre Q Post ∗
      ⌜∀ en : Bool, stepOk M hs (stepOf (roleDeleteF en role))⌝ ∗
      ⌜∀ s : AuthState, histLast M hs s → ∀ n : GoString, (s.users !! n).isSome →
        n.length ≤ backend.maxKeySize⌝ }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"RoleDelete")) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); ∃ (b : Bool) (sc : AuthState), (Post ∨ Pre) ∗ authWRx st M P f T b sc ∗
      respOk etcdserverpb.AuthRoleDeleteResponse resp err ∗ ∃ en : Bool, enabledVerdict M en ∗
      adminOutP M hs (stepOf (roleDeleteF en role)) noExtra err (tieStep M hs b0 sc0 b sc) }}

/-- `RoleGrantPermission.spec` with the admin side's halves of the flag and the cache at `b0`/`sc0` exposed and
kept tied to the latest state (`tieStep`). -/
abbrev auth.authStore.RoleGrantPermission.specT : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : AuthMode) (P : IProp GF) (f : val) (T : IProp GF)
    (hs : List AuthState) (Pre Q Post : IProp GF) (r : Loc) (name : GoString) (w : Option PermW) (b0 : Bool) (sc0 : AuthState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗
      roleGrantPermissionReqIs r name w ∗ ⌜name.length ≤ backend.maxKeySize⌝ ∗
      authOwn M hs ∗ authWRx st M P f T b0 sc0 ∗ mvcc.csContract P f Pre Q Post ∗
      ⌜stepOk M hs (roleGrantPermissionR name w)⌝ }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"RoleGrantPermission")) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); ∃ (b : Bool) (sc : AuthState), (Post ∨ Pre) ∗ authWRx st M P f T b sc ∗
      respOk etcdserverpb.AuthRoleGrantPermissionResponse resp err ∗
      adminOutP M hs (roleGrantPermissionR name w) noExtra err (tieStep M hs b0 sc0 b sc) }}

/-- `RoleRevokePermission.spec` with the admin side's halves of the flag and the cache at `b0`/`sc0` exposed and
kept tied to the latest state (`tieStep`). -/
abbrev auth.authStore.RoleRevokePermission.specT : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : AuthMode) (P : IProp GF) (f : val) (T : IProp GF)
    (hs : List AuthState) (Pre Q Post : IProp GF) (r : Loc) (role key rangeEnd : GoString) (b0 : Bool) (sc0 : AuthState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗
      roleRevokePermissionReqIs r role key rangeEnd ∗ ⌜role.length ≤ backend.maxKeySize⌝ ∗
      authOwn M hs ∗ authWRx st M P f T b0 sc0 ∗ mvcc.csContract P f Pre Q Post ∗
      ⌜stepOk M hs (roleRevokePermissionR role key rangeEnd)⌝ }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"RoleRevokePermission")) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); ∃ (b : Bool) (sc : AuthState), (Post ∨ Pre) ∗ authWRx st M P f T b sc ∗
      respOk etcdserverpb.AuthRoleRevokePermissionResponse resp err ∗
      adminOutP M hs (roleRevokePermissionR role key rangeEnd) noExtra err (tieStep M hs b0 sc0 b sc) }}

end spec

section derive
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.authStore.AuthEnable.spec_of_T (h : auth.authStore.AuthEnable.specT (GF := GF) (hG := hG)) :
    auth.authStore.AuthEnable.spec (GF := GF) (hG := hG) := by
  intro st R M P f T hs Pre Q Post
  iintro %Φ ⟨#Hpkg, #Hinv, %HisOn, Hown, HWR, Htpa, Hcs, %Hok⟩ HΦ
  ihave ⟨%b0, %sc0, HWR⟩ := authWR_to_x st M P f T $$ HWR
  iapply (h st R M P f T hs Pre Q Post b0 sc0) $$ [Hown HWR Htpa Hcs]
  · iframe; iframe #; ipureintro; exact ⟨HisOn, Hok⟩
  iintro !> %err ⟨%b, %sc, Htpa, HPP, HWR, %en, -, #Hev, Hout⟩
  iapply HΦ
  iframe Htpa HPP
  try iframe Hresp
  isplitl [HWR]
  · iapply authWR_of_x $$ HWR
  · iexists en; iframe Hev; iapply adminOutP_adminOut $$ Hout

theorem auth.authStore.AuthDisable.spec_of_T (h : auth.authStore.AuthDisable.specT (GF := GF) (hG := hG)) :
    auth.authStore.AuthDisable.spec (GF := GF) (hG := hG) := by
  intro st R M P f T hs Pre Q Post
  iintro %Φ ⟨#Hpkg, #Hinv, Hown, HWR, Htpa, Hcs, %Hok⟩ HΦ
  ihave ⟨%b0, %sc0, HWR⟩ := authWR_to_x st M P f T $$ HWR
  iapply (h st R M P f T hs Pre Q Post b0 sc0) $$ [Hown HWR Htpa Hcs]
  · iframe; iframe #; ipureintro; exact Hok
  iintro !> ⟨%b, %sc, Htpa, HPP, HWR, %en, #Hev, Hout⟩
  iapply HΦ
  iframe Htpa HPP
  try iframe Hresp
  isplitl [HWR]
  · iapply authWR_of_x $$ HWR
  · iexists en; iframe Hev; iapply adminOutP_adminOut $$ Hout

theorem auth.authStore.UserAdd.spec_of_T (h : auth.authStore.UserAdd.specT (GF := GF) (hG := hG)) :
    auth.authStore.UserAdd.spec (GF := GF) (hG := hG) := by
  intro st R M P f T hs Pre Q Post r name
  iintro %Φ ⟨#Hpkg, #Hinv, #Hr, %Hlen, Hown, HWR, Hcs, %Hok⟩ HΦ
  ihave ⟨%b0, %sc0, HWR⟩ := authWR_to_x st M P f T $$ HWR
  iapply (h st R M P f T hs Pre Q Post r name b0 sc0) $$ [Hown HWR Hcs]
  · iframe; iframe #; ipureintro; exact ⟨Hlen, Hok⟩
  iintro !> %resp %err ⟨%b, %sc, HPP, HWR, Hresp, Hout⟩
  iapply HΦ
  iframe HPP Hresp
  isplitl [HWR]
  · iapply authWR_of_x $$ HWR
  · iapply adminOutP_adminOut $$ Hout

theorem auth.authStore.UserDelete.spec_of_T (h : auth.authStore.UserDelete.specT (GF := GF) (hG := hG)) :
    auth.authStore.UserDelete.spec (GF := GF) (hG := hG) := by
  intro st R M P f T hs Pre Q Post r name
  iintro %Φ ⟨#Hpkg, #Hinv, #Hr, Hown, HWR, Htpa, Hcs, %Hok⟩ HΦ
  ihave ⟨%b0, %sc0, HWR⟩ := authWR_to_x st M P f T $$ HWR
  iapply (h st R M P f T hs Pre Q Post r name b0 sc0) $$ [Hown HWR Htpa Hcs]
  · iframe; iframe #; ipureintro; exact Hok
  iintro !> %resp %err ⟨%b, %sc, Htpa, HPP, HWR, Hresp, %en, #Hev, Hout⟩
  iapply HΦ
  iframe Htpa HPP
  try iframe Hresp
  isplitl [HWR]
  · iapply authWR_of_x $$ HWR
  · iexists en; iframe Hev; iapply adminOutP_adminOut $$ Hout

theorem auth.authStore.UserChangePassword.spec_of_T (h : auth.authStore.UserChangePassword.specT (GF := GF) (hG := hG)) :
    auth.authStore.UserChangePassword.spec (GF := GF) (hG := hG) := by
  intro st R M P f T hs Pre Q Post r name
  iintro %Φ ⟨#Hpkg, #Hinv, #Hr, %Hlen, Hown, HWR, Htpa, Hcs, %Hok⟩ HΦ
  ihave ⟨%b0, %sc0, HWR⟩ := authWR_to_x st M P f T $$ HWR
  iapply (h st R M P f T hs Pre Q Post r name b0 sc0) $$ [Hown HWR Htpa Hcs]
  · iframe; iframe #; ipureintro; exact ⟨Hlen, Hok⟩
  iintro !> %resp %err ⟨%b, %sc, Htpa, HPP, HWR, Hresp, Hout⟩
  iapply HΦ
  iframe Htpa HPP Hresp
  isplitl [HWR]
  · iapply authWR_of_x $$ HWR
  · iapply adminOutP_adminOut $$ Hout

theorem auth.authStore.UserGrantRole.spec_of_T (h : auth.authStore.UserGrantRole.specT (GF := GF) (hG := hG)) :
    auth.authStore.UserGrantRole.spec (GF := GF) (hG := hG) := by
  intro st R M P f T hs Pre Q Post r user role
  iintro %Φ ⟨#Hpkg, #Hinv, #Hr, %Hlen, Hown, HWR, Hcs, %Hb, %Hok⟩ HΦ
  ihave ⟨%b0, %sc0, HWR⟩ := authWR_to_x st M P f T $$ HWR
  iapply (h st R M P f T hs Pre Q Post r user role b0 sc0) $$ [Hown HWR Hcs]
  · iframe; iframe #; ipureintro; exact ⟨Hlen, Hb, Hok⟩
  iintro !> %resp %err ⟨%b, %sc, HPP, HWR, Hresp, Hout⟩
  iapply HΦ
  iframe HPP Hresp
  isplitl [HWR]
  · iapply authWR_of_x $$ HWR
  · iapply adminOutP_adminOut $$ Hout

theorem auth.authStore.UserRevokeRole.spec_of_T (h : auth.authStore.UserRevokeRole.specT (GF := GF) (hG := hG)) :
    auth.authStore.UserRevokeRole.spec (GF := GF) (hG := hG) := by
  intro st R M P f T hs Pre Q Post r name role
  iintro %Φ ⟨#Hpkg, #Hinv, #Hr, %Hlen, Hown, HWR, Hcs, %Hok⟩ HΦ
  ihave ⟨%b0, %sc0, HWR⟩ := authWR_to_x st M P f T $$ HWR
  iapply (h st R M P f T hs Pre Q Post r name role b0 sc0) $$ [Hown HWR Hcs]
  · iframe; iframe #; ipureintro; exact ⟨Hlen, Hok⟩
  iintro !> %resp %err ⟨%b, %sc, HPP, HWR, Hresp, %en, #Hev, Hout⟩
  iapply HΦ
  iframe HPP Hresp
  isplitl [HWR]
  · iapply authWR_of_x $$ HWR
  · iexists en; iframe Hev; iapply adminOutP_adminOut $$ Hout

theorem auth.authStore.RoleAdd.spec_of_T (h : auth.authStore.RoleAdd.specT (GF := GF) (hG := hG)) :
    auth.authStore.RoleAdd.spec (GF := GF) (hG := hG) := by
  intro st R M P f T hs Pre Q Post r name
  iintro %Φ ⟨#Hpkg, #Hinv, #Hr, %Hlen, Hown, HWR, Hcs, %Hok⟩ HΦ
  ihave ⟨%b0, %sc0, HWR⟩ := authWR_to_x st M P f T $$ HWR
  iapply (h st R M P f T hs Pre Q Post r name b0 sc0) $$ [Hown HWR Hcs]
  · iframe; iframe #; ipureintro; exact ⟨Hlen, Hok⟩
  iintro !> %resp %err ⟨%b, %sc, HPP, HWR, Hresp, Hout⟩
  iapply HΦ
  iframe HPP Hresp
  isplitl [HWR]
  · iapply authWR_of_x $$ HWR
  · iapply adminOutP_adminOut $$ Hout

theorem auth.authStore.RoleDelete.spec_of_T (h : auth.authStore.RoleDelete.specT (GF := GF) (hG := hG)) :
    auth.authStore.RoleDelete.spec (GF := GF) (hG := hG) := by
  intro st R M P f T hs Pre Q Post r role
  iintro %Φ ⟨#Hpkg, #Hinv, #Hr, Hown, HWR, Hcs, %Hok, %Hn⟩ HΦ
  ihave ⟨%b0, %sc0, HWR⟩ := authWR_to_x st M P f T $$ HWR
  iapply (h st R M P f T hs Pre Q Post r role b0 sc0) $$ [Hown HWR Hcs]
  · iframe; iframe #; ipureintro; exact ⟨Hok, Hn⟩
  iintro !> %resp %err ⟨%b, %sc, HPP, HWR, Hresp, %en, #Hev, Hout⟩
  iapply HΦ
  iframe HPP Hresp
  isplitl [HWR]
  · iapply authWR_of_x $$ HWR
  · iexists en; iframe Hev; iapply adminOutP_adminOut $$ Hout

theorem auth.authStore.RoleGrantPermission.spec_of_T (h : auth.authStore.RoleGrantPermission.specT (GF := GF) (hG := hG)) :
    auth.authStore.RoleGrantPermission.spec (GF := GF) (hG := hG) := by
  intro st R M P f T hs Pre Q Post r name w
  iintro %Φ ⟨#Hpkg, #Hinv, #Hr, %Hlen, Hown, HWR, Hcs, %Hok⟩ HΦ
  ihave ⟨%b0, %sc0, HWR⟩ := authWR_to_x st M P f T $$ HWR
  iapply (h st R M P f T hs Pre Q Post r name w b0 sc0) $$ [Hown HWR Hcs]
  · iframe; iframe #; ipureintro; exact ⟨Hlen, Hok⟩
  iintro !> %resp %err ⟨%b, %sc, HPP, HWR, Hresp, Hout⟩
  iapply HΦ
  iframe HPP Hresp
  isplitl [HWR]
  · iapply authWR_of_x $$ HWR
  · iapply adminOutP_adminOut $$ Hout

theorem auth.authStore.RoleRevokePermission.spec_of_T (h : auth.authStore.RoleRevokePermission.specT (GF := GF) (hG := hG)) :
    auth.authStore.RoleRevokePermission.spec (GF := GF) (hG := hG) := by
  intro st R M P f T hs Pre Q Post r role key rangeEnd
  iintro %Φ ⟨#Hpkg, #Hinv, #Hr, %Hlen, Hown, HWR, Hcs, %Hok⟩ HΦ
  ihave ⟨%b0, %sc0, HWR⟩ := authWR_to_x st M P f T $$ HWR
  iapply (h st R M P f T hs Pre Q Post r role key rangeEnd b0 sc0) $$ [Hown HWR Hcs]
  · iframe; iframe #; ipureintro; exact ⟨Hlen, Hok⟩
  iintro !> %resp %err ⟨%b, %sc, HPP, HWR, Hresp, Hout⟩
  iapply HΦ
  iframe HPP Hresp
  isplitl [HWR]
  · iapply authWR_of_x $$ HWR
  · iapply adminOutP_adminOut $$ Hout

end derive

end EtcdGrove
end Perennial
