/-
**Per-type instances: the Auth service's messages at registered types** (stage A's per-type
instances of `InvAuthConn.lean`'s and `InvClientAuth.lean`'s `ProtoMsg`s). For each message type,
its normalizing store (`tree`: what protobuf-go's decoder leaves in a fresh message decoding the
sender's bytes), the satisfiability of its model (`ReqSat` for a request, `RepSat` for a reply),
`wireLen_ok` for a request, and its registration.

The requests: `AuthUserAddRequest`, `AuthUserGrantRoleRequest`, `AuthRoleAddRequest`,
`AuthRoleGrantPermissionRequest`, `AuthEnableRequest`, `AuthenticateRequest`. The replies:
`AuthUserAddResponse`, `AuthUserGrantRoleResponse`, `AuthRoleAddResponse`,
`AuthRoleGrantPermissionResponse`, `AuthEnableResponse`, `AuthenticateResponse`.

The models drop what the client does not read, so the stores cannot hold it: a reply's `Header`
is left `nil` (the server always sends one), and `AuthUserAddRequest`'s `Options` is a fresh empty
message (what etcd's client always sends: `&authpb.UserAddOptions{NoPassword: false}`; the model
does not say whether the sender's `Options` was `nil`).
-/
module

public import Proof.google_golang_org.grpc.InvGrpcStream
public import Proof.go_etcd_io.etcd.client.v3.InvClientAuth

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-! ## Requests -/

/-- **The store of a user addition's `Options`**: a fresh empty `UserAddOptions` (`NoPassword`
false, as etcd's client sends it; see the file header). -/
def userOptsTree : VTree :=
  .ptr authpb.UserAddOptions.ty (.strct authpb.UserAddOptions.ty [] [])

theorem treeWp_userOpts (Φ : val → IProp GF) :
    (∀ o : Loc, userOptsFalse o -∗ Φ #o) ⊢ treeWp userOptsTree Φ := by
  iintro H
  unfold userOptsTree
  iapply (treeWp_ptr_fupd (V := authpb.UserAddOptions))
  simp only [treeWp, treeWpL]
  simp [litBody, strctKes, kesσ]
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  iintro %p Hp
  ihave %Hnn := typedPointsto_not_null $$ Hp
  imod (typedPointsto_dfractional (GF := GF) p _).dfractional_persist _ $$ Hp with #Hp
  imodintro
  iapply H
  unfold userOptsFalse auth.userOptsAt
  iright
  isplitr
  · ipureintro; exact Hnn
  iexists _, _, _
  iexact Hp

/-- **The store of a user addition**: its name and password (`HashedPassword` empty, as the
client sends it), its `Options`. -/
def userAddReqTree (m : UserAddW) : VTree :=
  .strct etcdserverpb.AuthUserAddRequest.ty
    [(go!"Name", go.string), (go!"Password", go.string),
     (go!"Options", go.GoType.PointerType authpb.UserAddOptions.ty)]
    [.leaf #m.name, .leaf #m.pw, userOptsTree]

/-- **`pbAuthUserAddRequest` with its store.** -/
def pbAuthUserAddRequestT : ProtoMsgT GF :=
  { pbAuthUserAddRequest with tree := userAddReqTree }

theorem pbAuthUserAddRequestT_reqSat : (pbAuthUserAddRequestT (GF := GF)).ReqSat := by
  refine ⟨⟨etcdserverpb.AuthUserAddRequest, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.AuthUserAddRequest etcdserverpb.AuthUserAddRequest.ty),
      fun l => .rfl⟩,
    ⟨etcdserverpb.AuthUserAddRequest, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.AuthUserAddRequest etcdserverpb.AuthUserAddRequest.ty),
      fun l => .rfl⟩,
    ?_, ?_⟩
  · intro m
    simp only [pbAuthUserAddRequestT, pbAuthUserAddRequest]
    iintro ⟨%req, Hp, -⟩
    ihave %H := typedPointsto_not_null $$ Hp
    exact absurd rfl H
  intro ls l m
  simp only [pbAuthUserAddRequestT, pbAuthUserAddRequest]
  iintro ⟨Hs, %Hw, Hl⟩
  iapply wp_fupd
  iapply (storeInto_wp_typed (V := etcdserverpb.AuthUserAddRequest)
    (ty := etcdserverpb.AuthUserAddRequest.ty) l (zero_val etcdserverpb.AuthUserAddRequest))
  simp only [userAddReqTree, treeWp, treeWpL]
  repeat (isplitr; · ipureintro; exact isPanic_intoVal _)
  iapply treeWp_userOpts
  iintro %o #Ho
  isplitr
  · ipureintro; exact isPanic_intoVal o
  simp [litBody, strctKes, kesσ, envσ]
  repeat (isplitr; · ipureintro; trivial)
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  iframe Hl
  iintro Hl
  ihave %Hnn := typedPointsto_not_null $$ Hl
  icases typedPointsto_split _ _ _ $$ Hl with Hl
  simp only [TypedPointsto.typedPointstoDef]
  icases Hl with ⟨-, HN, HP, HO, HH, -, -, -⟩
  imod (typedPointsto_dfractional (GF := GF) _ m.name).dfractional_persist _ $$ HN with #HN
  imod (typedPointsto_dfractional (GF := GF) _ o).dfractional_persist _ $$ HO with #HO
  imodintro
  iframe Hs
  isplitr [HP HH]
  · isplitr
    · ipureintro; exact Hnn
    iframe HN
    iexists o
    iframe HO Ho
  iframe HP
  iexact HH

theorem pbAuthUserAddRequestT_wireLen_ok :
    ∃ m, (pbAuthUserAddRequestT (GF := GF)).wireLen m < grpcMsgMax :=
  ⟨⟨[], []⟩, by simp [pbAuthUserAddRequestT, pbAuthUserAddRequest, wireSlack, grpcMsgMax]⟩

/-- **The store of a role grant to a user**: the user and the role. -/
def userGrantRoleReqTree (m : GoString × GoString) : VTree :=
  .strct etcdserverpb.AuthUserGrantRoleRequest.ty
    [(go!"User", go.string), (go!"Role", go.string)] [.leaf #m.1, .leaf #m.2]

/-- **`pbAuthUserGrantRoleRequest` with its store.** -/
def pbAuthUserGrantRoleRequestT : ProtoMsgT GF :=
  { pbAuthUserGrantRoleRequest with tree := userGrantRoleReqTree }

theorem pbAuthUserGrantRoleRequestT_reqSat : (pbAuthUserGrantRoleRequestT (GF := GF)).ReqSat := by
  refine ⟨⟨etcdserverpb.AuthUserGrantRoleRequest, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.AuthUserGrantRoleRequest
        etcdserverpb.AuthUserGrantRoleRequest.ty), fun l => .rfl⟩,
    ⟨etcdserverpb.AuthUserGrantRoleRequest, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.AuthUserGrantRoleRequest
        etcdserverpb.AuthUserGrantRoleRequest.ty), fun l => .rfl⟩,
    ?_, ?_⟩
  · intro m
    simp only [pbAuthUserGrantRoleRequestT, pbAuthUserGrantRoleRequest]
    iintro ⟨%req, Hp, -⟩
    ihave %H := typedPointsto_not_null $$ Hp
    exact absurd rfl H
  intro ls l m
  simp only [pbAuthUserGrantRoleRequestT, pbAuthUserGrantRoleRequest]
  iintro ⟨Hs, %Hw, Hl⟩
  iapply wp_fupd
  iapply (storeInto_wp_typed (V := etcdserverpb.AuthUserGrantRoleRequest)
    (ty := etcdserverpb.AuthUserGrantRoleRequest.ty) l (zero_val etcdserverpb.AuthUserGrantRoleRequest))
  simp only [userGrantRoleReqTree, treeWp, treeWpL]
  repeat (isplitr; · ipureintro; exact isPanic_intoVal _)
  simp [litBody, strctKes, kesσ, envσ]
  repeat (isplitr; · ipureintro; trivial)
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  iframe Hl
  iintro Hl
  ihave %Hnn := typedPointsto_not_null $$ Hl
  icases typedPointsto_split _ _ _ $$ Hl with Hl
  simp only [TypedPointsto.typedPointstoDef]
  icases Hl with ⟨-, HU, HR, -, -, -⟩
  imod (typedPointsto_dfractional (GF := GF) _ m.1).dfractional_persist _ $$ HU with #HU
  imod (typedPointsto_dfractional (GF := GF) _ m.2).dfractional_persist _ $$ HR with #HR
  imodintro
  iframe Hs
  isplitr
  · unfold auth.userGrantRoleReqIs
    isplitr
    · ipureintro; exact Hnn
    iframe HU HR
  · ipureintro; trivial

theorem pbAuthUserGrantRoleRequestT_wireLen_ok :
    ∃ m, (pbAuthUserGrantRoleRequestT (GF := GF)).wireLen m < grpcMsgMax :=
  ⟨([], []), by simp [pbAuthUserGrantRoleRequestT, pbAuthUserGrantRoleRequest, wireSlack, grpcMsgMax]⟩

/-- **The store of a role addition**: the role's name. -/
def roleAddReqTree (m : GoString) : VTree :=
  .strct etcdserverpb.AuthRoleAddRequest.ty [(go!"Name", go.string)] [.leaf #m]

/-- **`pbAuthRoleAddRequest` with its store.** -/
def pbAuthRoleAddRequestT : ProtoMsgT GF :=
  { pbAuthRoleAddRequest with tree := roleAddReqTree }

theorem pbAuthRoleAddRequestT_reqSat : (pbAuthRoleAddRequestT (GF := GF)).ReqSat := by
  refine ⟨⟨etcdserverpb.AuthRoleAddRequest, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.AuthRoleAddRequest etcdserverpb.AuthRoleAddRequest.ty),
      fun l => .rfl⟩,
    ⟨etcdserverpb.AuthRoleAddRequest, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.AuthRoleAddRequest etcdserverpb.AuthRoleAddRequest.ty),
      fun l => .rfl⟩,
    ?_, ?_⟩
  · intro m
    simp only [pbAuthRoleAddRequestT, pbAuthRoleAddRequest]
    iintro ⟨%req, Hp, -⟩
    ihave %H := typedPointsto_not_null $$ Hp
    exact absurd rfl H
  intro ls l m
  change GoString at m
  simp only [pbAuthRoleAddRequestT, pbAuthRoleAddRequest]
  iintro ⟨Hs, %Hw, Hl⟩
  iapply wp_fupd
  iapply (storeInto_wp_typed (V := etcdserverpb.AuthRoleAddRequest)
    (ty := etcdserverpb.AuthRoleAddRequest.ty) l (zero_val etcdserverpb.AuthRoleAddRequest))
  simp only [roleAddReqTree, treeWp, treeWpL]
  repeat (isplitr; · ipureintro; exact isPanic_intoVal _)
  simp [litBody, strctKes, kesσ, envσ]
  repeat (isplitr; · ipureintro; trivial)
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  iframe Hl
  iintro Hl
  ihave %Hnn := typedPointsto_not_null $$ Hl
  icases typedPointsto_split _ _ _ $$ Hl with Hl
  simp only [TypedPointsto.typedPointstoDef]
  icases Hl with ⟨-, HN, -, -, -⟩
  imod (typedPointsto_dfractional (GF := GF) _ m).dfractional_persist _ $$ HN with #HN
  imodintro
  iframe Hs
  isplitr
  · unfold auth.roleAddReqIs
    isplitr
    · ipureintro; exact Hnn
    iframe HN
  · ipureintro; trivial

theorem pbAuthRoleAddRequestT_wireLen_ok :
    ∃ m, (pbAuthRoleAddRequestT (GF := GF)).wireLen m < grpcMsgMax :=
  ⟨[], by simp [pbAuthRoleAddRequestT, pbAuthRoleAddRequest, wireSlack, grpcMsgMax]⟩

/-- **The store of a wire permission**: a fresh `Permission` holding its type, its key and range
end (`nil` if empty). -/
def permWTree (w : auth.PermW) : VTree :=
  .ptr authpb.Permission.ty (.strct authpb.Permission.ty
    [(go!"PermType", authpb.Permission_Type.ty), (go!"Key", go.GoType.SliceType go.byte),
     (go!"RangeEnd", go.GoType.SliceType go.byte)]
    [.leaf #w.ty, bytesTree go.byte w.key, bytesTree go.byte w.rangeEnd])

theorem treeWp_permW (w : auth.PermW) (Hk : w.key.length < 2 ^ 63 - 1) (Φ : val → IProp GF) :
    (∀ p : Loc, auth.ownPermW p w -∗ Φ #p) ⊢ treeWp (permWTree w) Φ := by
  iintro H
  unfold permWTree
  iapply (treeWp_ptr_fupd (V := authpb.Permission))
  simp only [treeWp, treeWpL]
  repeat (isplitr; · ipureintro; exact isPanic_intoVal _)
  iapply treeWp_bytes
  iintro %ksl %Hks Hks -
  repeat (isplitr; · ipureintro; exact isPanic_intoVal _)
  iapply treeWp_bytes
  iintro %rsl %Hrs Hrs -
  repeat (isplitr; · ipureintro; exact isPanic_intoVal _)
  simp [litBody, strctKes, kesσ, envσ]
  repeat (isplitr; · ipureintro; trivial)
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  iintro %p Hp
  ihave %Hnn := typedPointsto_not_null $$ Hp
  imod (typedPointsto_dfractional (GF := GF) p _).dfractional_persist _ $$ Hp with #Hp
  imod ownSlice_persist _ _ _ $$ Hks with #Hks
  imod ownSlice_persist _ _ _ $$ Hrs with #Hrs
  imodintro
  iapply H
  unfold auth.ownPermW
  isplitr
  · ipureintro; exact ⟨Hnn, Hk⟩
  iexists _, ksl, rsl, _, _
  iframe Hp Hks Hrs

/-- **The store of a permission grant to a role**: the role's name and the permission (always
present: the sender's is not nil). -/
def roleGrantPermissionReqTree (m : GoString × auth.PermW) : VTree :=
  .strct etcdserverpb.AuthRoleGrantPermissionRequest.ty
    [(go!"Name", go.string), (go!"Perm", go.GoType.PointerType authpb.Permission.ty)]
    [.leaf #m.1, permWTree m.2]

/-- **`pbAuthRoleGrantPermissionRequest` with its store.** -/
def pbAuthRoleGrantPermissionRequestT : ProtoMsgT GF :=
  { pbAuthRoleGrantPermissionRequest with tree := roleGrantPermissionReqTree }

theorem pbAuthRoleGrantPermissionRequestT_reqSat :
    (pbAuthRoleGrantPermissionRequestT (GF := GF)).ReqSat := by
  refine ⟨⟨etcdserverpb.AuthRoleGrantPermissionRequest, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.AuthRoleGrantPermissionRequest
        etcdserverpb.AuthRoleGrantPermissionRequest.ty), fun l => .rfl⟩,
    ⟨etcdserverpb.AuthRoleGrantPermissionRequest, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.AuthRoleGrantPermissionRequest
        etcdserverpb.AuthRoleGrantPermissionRequest.ty), fun l => .rfl⟩,
    ?_, ?_⟩
  · intro m
    simp only [pbAuthRoleGrantPermissionRequestT, pbAuthRoleGrantPermissionRequest]
    iintro ⟨%req, Hp, -⟩
    ihave %H := typedPointsto_not_null $$ Hp
    exact absurd rfl H
  intro ls l m
  simp only [pbAuthRoleGrantPermissionRequestT, pbAuthRoleGrantPermissionRequest]
  iintro ⟨Hs, %Hw, Hl⟩
  have Hk : m.2.key.length < 2 ^ 63 - 1 := by
    simp only [grpcMsgMax] at Hw; omega
  iapply wp_fupd
  iapply (storeInto_wp_typed (V := etcdserverpb.AuthRoleGrantPermissionRequest)
    (ty := etcdserverpb.AuthRoleGrantPermissionRequest.ty) l
    (zero_val etcdserverpb.AuthRoleGrantPermissionRequest))
  simp only [roleGrantPermissionReqTree, treeWp, treeWpL]
  repeat (isplitr; · ipureintro; exact isPanic_intoVal _)
  iapply treeWp_permW m.2 Hk
  iintro %p #Hp
  isplitr
  · ipureintro; exact isPanic_intoVal p
  simp [litBody, strctKes, kesσ, envσ]
  repeat (isplitr; · ipureintro; trivial)
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  iframe Hl
  iintro Hl
  ihave %Hnn := typedPointsto_not_null $$ Hl
  icases typedPointsto_split _ _ _ $$ Hl with Hl
  simp only [TypedPointsto.typedPointstoDef]
  icases Hl with ⟨-, HN, HP, -, -, -⟩
  imod (typedPointsto_dfractional (GF := GF) _ m.1).dfractional_persist _ $$ HN with #HN
  imod (typedPointsto_dfractional (GF := GF) _ p).dfractional_persist _ $$ HP with #HP
  imodintro
  iframe Hs
  isplitr
  · unfold auth.roleGrantPermissionReqIs
    isplitr
    · ipureintro; exact Hnn
    iframe HN
    iexists p
    iframe HP Hp
  · ipureintro; trivial

theorem pbAuthRoleGrantPermissionRequestT_wireLen_ok :
    ∃ m, (pbAuthRoleGrantPermissionRequestT (GF := GF)).wireLen m < grpcMsgMax :=
  ⟨([], ⟨W32 0, [], []⟩), by
    simp [pbAuthRoleGrantPermissionRequestT, pbAuthRoleGrantPermissionRequest, wireSlack, grpcMsgMax]⟩

/-- **The store of an auth enable request**: nothing. -/
def authEnableReqTree (_ : Unit) : VTree :=
  .strct etcdserverpb.AuthEnableRequest.ty [] []

/-- **`pbAuthEnableRequest` with its store.** -/
def pbAuthEnableRequestT : ProtoMsgT GF :=
  { pbAuthEnableRequest with tree := authEnableReqTree }

theorem pbAuthEnableRequestT_reqSat : (pbAuthEnableRequestT (GF := GF)).ReqSat := by
  refine ⟨⟨etcdserverpb.AuthEnableRequest, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.AuthEnableRequest etcdserverpb.AuthEnableRequest.ty),
      fun l => .rfl⟩,
    ⟨etcdserverpb.AuthEnableRequest, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.AuthEnableRequest etcdserverpb.AuthEnableRequest.ty),
      fun l => .rfl⟩,
    ?_, ?_⟩
  · intro m
    simp only [pbAuthEnableRequestT, pbAuthEnableRequest]
    iintro ⟨%req, Hp, -⟩
    ihave %H := typedPointsto_not_null $$ Hp
    exact absurd rfl H
  intro ls l m
  simp only [pbAuthEnableRequestT, pbAuthEnableRequest]
  iintro ⟨Hs, %Hw, Hl⟩
  iapply (storeInto_wp_typed (V := etcdserverpb.AuthEnableRequest)
    (ty := etcdserverpb.AuthEnableRequest.ty) l (zero_val etcdserverpb.AuthEnableRequest))
  simp only [authEnableReqTree, treeWp, treeWpL]
  simp [litBody, strctKes, kesσ]
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  iframe Hl
  iintro Hl
  ihave %Hnn := typedPointsto_not_null $$ Hl
  iframe Hs
  ipureintro; exact ⟨Hnn, trivial⟩

theorem pbAuthEnableRequestT_wireLen_ok :
    ∃ m, (pbAuthEnableRequestT (GF := GF)).wireLen m < grpcMsgMax :=
  ⟨(), by simp [pbAuthEnableRequestT, pbAuthEnableRequest, wireSlack, grpcMsgMax]⟩

/-- **The store of an authentication request**: the user's name and password. -/
def authenticateReqTree (m : GoString × GoString) : VTree :=
  .strct etcdserverpb.AuthenticateRequest.ty
    [(go!"Name", go.string), (go!"Password", go.string)] [.leaf #m.1, .leaf #m.2]

/-- **`pbAuthenticateRequest` with its store.** -/
def pbAuthenticateRequestT : ProtoMsgT GF :=
  { pbAuthenticateRequest with tree := authenticateReqTree }

theorem pbAuthenticateRequestT_reqSat : (pbAuthenticateRequestT (GF := GF)).ReqSat := by
  refine ⟨⟨etcdserverpb.AuthenticateRequest, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.AuthenticateRequest etcdserverpb.AuthenticateRequest.ty),
      fun l => .rfl⟩,
    ⟨etcdserverpb.AuthenticateRequest, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.AuthenticateRequest etcdserverpb.AuthenticateRequest.ty),
      fun l => .rfl⟩,
    ?_, ?_⟩
  · intro m
    simp only [pbAuthenticateRequestT, pbAuthenticateRequest]
    iintro ⟨%req, Hp, -⟩
    ihave %H := typedPointsto_not_null $$ Hp
    exact absurd rfl H
  intro ls l m
  simp only [pbAuthenticateRequestT, pbAuthenticateRequest]
  iintro ⟨Hs, %Hw, Hl⟩
  iapply wp_fupd
  iapply (storeInto_wp_typed (V := etcdserverpb.AuthenticateRequest)
    (ty := etcdserverpb.AuthenticateRequest.ty) l (zero_val etcdserverpb.AuthenticateRequest))
  simp only [authenticateReqTree, treeWp, treeWpL]
  repeat (isplitr; · ipureintro; exact isPanic_intoVal _)
  simp [litBody, strctKes, kesσ, envσ]
  repeat (isplitr; · ipureintro; trivial)
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  iframe Hl
  iintro Hl
  ihave %Hnn := typedPointsto_not_null $$ Hl
  icases typedPointsto_split _ _ _ $$ Hl with Hl
  simp only [TypedPointsto.typedPointstoDef]
  icases Hl with ⟨-, HN, HP, -, -, -⟩
  imod (typedPointsto_dfractional (GF := GF) _ m.1).dfractional_persist _ $$ HN with #HN
  imodintro
  iframe Hs HP
  isplitr
  · ipureintro; exact Hnn
  iframe HN

theorem pbAuthenticateRequestT_wireLen_ok :
    ∃ m, (pbAuthenticateRequestT (GF := GF)).wireLen m < grpcMsgMax :=
  ⟨([], []), by simp [pbAuthenticateRequestT, pbAuthenticateRequest, wireSlack, grpcMsgMax]⟩

/-! ## Replies -/

/-- **The store of a reply the client does not read**: nothing (its `Header` left `nil`: the model
does not hold it; see the file header). -/
def emptyRepTree (ty : go.GoType) (_ : Unit) : VTree := .strct ty [] []

/-- **`pbAuthUserAddResponse` with its store** (its `send` is the sender's `⌜l ≠ null⌝`, which
`RepSat`'s `send null m ⊢ False` needs). -/
def pbAuthUserAddResponseT : ProtoMsgT GF :=
  { pbAuthUserAddResponse with
    tree := emptyRepTree etcdserverpb.AuthUserAddResponse.ty }

theorem pbAuthUserAddResponseT_repSat : (pbAuthUserAddResponseT (GF := GF)).RepSat := by
  refine ⟨⟨etcdserverpb.AuthUserAddResponse, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.AuthUserAddResponse etcdserverpb.AuthUserAddResponse.ty),
      fun l => .rfl⟩,
    ⟨etcdserverpb.AuthUserAddResponse, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.AuthUserAddResponse etcdserverpb.AuthUserAddResponse.ty),
      fun l => .rfl⟩,
    ?_, ?_⟩
  · intro m
    simp only [pbAuthUserAddResponseT]
    iintro %H
    exact absurd rfl H
  intro ls l m
  simp only [pbAuthUserAddResponseT, pbAuthUserAddResponse]
  iintro ⟨Hs, ⟨%x0, Hl⟩⟩
  iapply (storeInto_wp_typed (V := etcdserverpb.AuthUserAddResponse)
    (ty := etcdserverpb.AuthUserAddResponse.ty) l x0)
  simp only [emptyRepTree, treeWp, treeWpL]
  simp [litBody, strctKes, kesσ]
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  iframe Hl
  iintro -
  iframe Hs

/-- **`pbAuthUserGrantRoleResponse` with its store** (as `pbAuthUserAddResponseT`). -/
def pbAuthUserGrantRoleResponseT : ProtoMsgT GF :=
  { pbAuthUserGrantRoleResponse with
    tree := emptyRepTree etcdserverpb.AuthUserGrantRoleResponse.ty }

theorem pbAuthUserGrantRoleResponseT_repSat : (pbAuthUserGrantRoleResponseT (GF := GF)).RepSat := by
  refine ⟨⟨etcdserverpb.AuthUserGrantRoleResponse, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.AuthUserGrantRoleResponse
        etcdserverpb.AuthUserGrantRoleResponse.ty), fun l => .rfl⟩,
    ⟨etcdserverpb.AuthUserGrantRoleResponse, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.AuthUserGrantRoleResponse
        etcdserverpb.AuthUserGrantRoleResponse.ty), fun l => .rfl⟩,
    ?_, ?_⟩
  · intro m
    simp only [pbAuthUserGrantRoleResponseT]
    iintro %H
    exact absurd rfl H
  intro ls l m
  simp only [pbAuthUserGrantRoleResponseT, pbAuthUserGrantRoleResponse]
  iintro ⟨Hs, ⟨%x0, Hl⟩⟩
  iapply (storeInto_wp_typed (V := etcdserverpb.AuthUserGrantRoleResponse)
    (ty := etcdserverpb.AuthUserGrantRoleResponse.ty) l x0)
  simp only [emptyRepTree, treeWp, treeWpL]
  simp [litBody, strctKes, kesσ]
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  iframe Hl
  iintro -
  iframe Hs

/-- **`pbAuthRoleAddResponse` with its store** (as `pbAuthUserAddResponseT`). -/
def pbAuthRoleAddResponseT : ProtoMsgT GF :=
  { pbAuthRoleAddResponse with
    tree := emptyRepTree etcdserverpb.AuthRoleAddResponse.ty }

theorem pbAuthRoleAddResponseT_repSat : (pbAuthRoleAddResponseT (GF := GF)).RepSat := by
  refine ⟨⟨etcdserverpb.AuthRoleAddResponse, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.AuthRoleAddResponse etcdserverpb.AuthRoleAddResponse.ty),
      fun l => .rfl⟩,
    ⟨etcdserverpb.AuthRoleAddResponse, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.AuthRoleAddResponse etcdserverpb.AuthRoleAddResponse.ty),
      fun l => .rfl⟩,
    ?_, ?_⟩
  · intro m
    simp only [pbAuthRoleAddResponseT]
    iintro %H
    exact absurd rfl H
  intro ls l m
  simp only [pbAuthRoleAddResponseT, pbAuthRoleAddResponse]
  iintro ⟨Hs, ⟨%x0, Hl⟩⟩
  iapply (storeInto_wp_typed (V := etcdserverpb.AuthRoleAddResponse)
    (ty := etcdserverpb.AuthRoleAddResponse.ty) l x0)
  simp only [emptyRepTree, treeWp, treeWpL]
  simp [litBody, strctKes, kesσ]
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  iframe Hl
  iintro -
  iframe Hs

/-- **`pbAuthRoleGrantPermissionResponse` with its store** (as `pbAuthUserAddResponseT`). -/
def pbAuthRoleGrantPermissionResponseT : ProtoMsgT GF :=
  { pbAuthRoleGrantPermissionResponse with
    tree := emptyRepTree etcdserverpb.AuthRoleGrantPermissionResponse.ty }

theorem pbAuthRoleGrantPermissionResponseT_repSat :
    (pbAuthRoleGrantPermissionResponseT (GF := GF)).RepSat := by
  refine ⟨⟨etcdserverpb.AuthRoleGrantPermissionResponse, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.AuthRoleGrantPermissionResponse
        etcdserverpb.AuthRoleGrantPermissionResponse.ty), fun l => .rfl⟩,
    ⟨etcdserverpb.AuthRoleGrantPermissionResponse, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.AuthRoleGrantPermissionResponse
        etcdserverpb.AuthRoleGrantPermissionResponse.ty), fun l => .rfl⟩,
    ?_, ?_⟩
  · intro m
    simp only [pbAuthRoleGrantPermissionResponseT]
    iintro %H
    exact absurd rfl H
  intro ls l m
  simp only [pbAuthRoleGrantPermissionResponseT, pbAuthRoleGrantPermissionResponse]
  iintro ⟨Hs, ⟨%x0, Hl⟩⟩
  iapply (storeInto_wp_typed (V := etcdserverpb.AuthRoleGrantPermissionResponse)
    (ty := etcdserverpb.AuthRoleGrantPermissionResponse.ty) l x0)
  simp only [emptyRepTree, treeWp, treeWpL]
  simp [litBody, strctKes, kesσ]
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  iframe Hl
  iintro -
  iframe Hs

/-- **`pbAuthEnableResponse` with its store** (as `pbAuthUserAddResponseT`). -/
def pbAuthEnableResponseT : ProtoMsgT GF :=
  { pbAuthEnableResponse with
    tree := emptyRepTree etcdserverpb.AuthEnableResponse.ty }

theorem pbAuthEnableResponseT_repSat : (pbAuthEnableResponseT (GF := GF)).RepSat := by
  refine ⟨⟨etcdserverpb.AuthEnableResponse, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.AuthEnableResponse etcdserverpb.AuthEnableResponse.ty),
      fun l => .rfl⟩,
    ⟨etcdserverpb.AuthEnableResponse, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.AuthEnableResponse etcdserverpb.AuthEnableResponse.ty),
      fun l => .rfl⟩,
    ?_, ?_⟩
  · intro m
    simp only [pbAuthEnableResponseT]
    iintro %H
    exact absurd rfl H
  intro ls l m
  simp only [pbAuthEnableResponseT, pbAuthEnableResponse]
  iintro ⟨Hs, ⟨%x0, Hl⟩⟩
  iapply (storeInto_wp_typed (V := etcdserverpb.AuthEnableResponse)
    (ty := etcdserverpb.AuthEnableResponse.ty) l x0)
  simp only [emptyRepTree, treeWp, treeWpL]
  simp [litBody, strctKes, kesσ]
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  iframe Hl
  iintro -
  iframe Hs

/-- **The store of an authentication reply**: its token (its `Header` left `nil`: the model does
not hold it). -/
def authenticateRepTree (t : GoString) : VTree :=
  .strct etcdserverpb.AuthenticateResponse.ty [(go!"Token", go.string)] [.leaf #t]

/-- **`pbAuthenticateResponse` with its store.** -/
def pbAuthenticateResponseT : ProtoMsgT GF :=
  { pbAuthenticateResponse with tree := authenticateRepTree }

theorem pbAuthenticateResponseT_repSat : (pbAuthenticateResponseT (GF := GF)).RepSat := by
  refine ⟨⟨etcdserverpb.AuthenticateResponse, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.AuthenticateResponse
        etcdserverpb.AuthenticateResponse.ty), fun l => .rfl⟩,
    ⟨etcdserverpb.AuthenticateResponse, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.AuthenticateResponse
        etcdserverpb.AuthenticateResponse.ty), fun l => .rfl⟩,
    ?_, ?_⟩
  · intro m
    simp only [pbAuthenticateResponseT, pbAuthenticateResponse]
    iintro ⟨%v, Hp, -⟩
    ihave %H := typedPointsto_not_null $$ Hp
    exact absurd rfl H
  intro ls l m
  change GoString at m
  simp only [pbAuthenticateResponseT, pbAuthenticateResponse]
  iintro ⟨Hs, ⟨%x0, Hl⟩⟩
  iapply wp_fupd
  iapply (storeInto_wp_typed (V := etcdserverpb.AuthenticateResponse)
    (ty := etcdserverpb.AuthenticateResponse.ty) l x0)
  simp only [authenticateRepTree, treeWp, treeWpL]
  repeat (isplitr; · ipureintro; exact isPanic_intoVal _)
  simp [litBody, strctKes, kesσ, envσ]
  repeat (isplitr; · ipureintro; trivial)
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  iframe Hl
  iintro Hl
  ihave %Hnn := typedPointsto_not_null $$ Hl
  icases typedPointsto_split _ _ _ $$ Hl with Hl
  simp only [TypedPointsto.typedPointstoDef]
  icases Hl with ⟨-, -, HT, -, -, -⟩
  imod (typedPointsto_dfractional (GF := GF) _ m).dfractional_persist _ $$ HT with #HT
  imodintro
  iframe Hs
  isplitr
  · ipureintro; exact Hnn
  iframe HT

/-! ## Registrations -/

/-- **`AuthUserAddRequest`'s registration** (stage A: the one model of the Go type
`AuthUserAddRequest` as a method's request). -/
axiom pbAuthUserAddRequestT_reg :
    grpcReqModelOf GF etcdserverpb.AuthUserAddRequest.ty = some (pbAuthUserAddRequestT (GF := GF))

/-- **`AuthUserGrantRoleRequest`'s registration** (stage A: the one model of the Go type
`AuthUserGrantRoleRequest` as a method's request). -/
axiom pbAuthUserGrantRoleRequestT_reg :
    grpcReqModelOf GF etcdserverpb.AuthUserGrantRoleRequest.ty =
      some (pbAuthUserGrantRoleRequestT (GF := GF))

/-- **`AuthRoleAddRequest`'s registration** (stage A: the one model of the Go type
`AuthRoleAddRequest` as a method's request). -/
axiom pbAuthRoleAddRequestT_reg :
    grpcReqModelOf GF etcdserverpb.AuthRoleAddRequest.ty = some (pbAuthRoleAddRequestT (GF := GF))

/-- **`AuthRoleGrantPermissionRequest`'s registration** (stage A: the one model of the Go type
`AuthRoleGrantPermissionRequest` as a method's request). -/
axiom pbAuthRoleGrantPermissionRequestT_reg :
    grpcReqModelOf GF etcdserverpb.AuthRoleGrantPermissionRequest.ty =
      some (pbAuthRoleGrantPermissionRequestT (GF := GF))

/-- **`AuthEnableRequest`'s registration** (stage A: the one model of the Go type
`AuthEnableRequest` as a method's request). -/
axiom pbAuthEnableRequestT_reg :
    grpcReqModelOf GF etcdserverpb.AuthEnableRequest.ty = some (pbAuthEnableRequestT (GF := GF))

/-- **`AuthenticateRequest`'s registration** (stage A: the one model of the Go type
`AuthenticateRequest` as a method's request). -/
axiom pbAuthenticateRequestT_reg :
    grpcReqModelOf GF etcdserverpb.AuthenticateRequest.ty = some (pbAuthenticateRequestT (GF := GF))

/-- **`AuthUserAddResponse`'s registration** (stage A: the one model of the Go type
`AuthUserAddResponse` as a method's reply). -/
axiom pbAuthUserAddResponseT_reg :
    grpcRepModelOf GF etcdserverpb.AuthUserAddResponse.ty = some (pbAuthUserAddResponseT (GF := GF))

/-- **`AuthUserGrantRoleResponse`'s registration** (stage A: the one model of the Go type
`AuthUserGrantRoleResponse` as a method's reply). -/
axiom pbAuthUserGrantRoleResponseT_reg :
    grpcRepModelOf GF etcdserverpb.AuthUserGrantRoleResponse.ty =
      some (pbAuthUserGrantRoleResponseT (GF := GF))

/-- **`AuthRoleAddResponse`'s registration** (stage A: the one model of the Go type
`AuthRoleAddResponse` as a method's reply). -/
axiom pbAuthRoleAddResponseT_reg :
    grpcRepModelOf GF etcdserverpb.AuthRoleAddResponse.ty = some (pbAuthRoleAddResponseT (GF := GF))

/-- **`AuthRoleGrantPermissionResponse`'s registration** (stage A: the one model of the Go type
`AuthRoleGrantPermissionResponse` as a method's reply). -/
axiom pbAuthRoleGrantPermissionResponseT_reg :
    grpcRepModelOf GF etcdserverpb.AuthRoleGrantPermissionResponse.ty =
      some (pbAuthRoleGrantPermissionResponseT (GF := GF))

/-- **`AuthEnableResponse`'s registration** (stage A: the one model of the Go type
`AuthEnableResponse` as a method's reply). -/
axiom pbAuthEnableResponseT_reg :
    grpcRepModelOf GF etcdserverpb.AuthEnableResponse.ty = some (pbAuthEnableResponseT (GF := GF))

/-- **`AuthenticateResponse`'s registration** (stage A: the one model of the Go type
`AuthenticateResponse` as a method's reply). -/
axiom pbAuthenticateResponseT_reg :
    grpcRepModelOf GF etcdserverpb.AuthenticateResponse.ty =
      some (pbAuthenticateResponseT (GF := GF))

end defs

end EtcdGrove
end Perennial
