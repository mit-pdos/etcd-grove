/-
Package initialization of `go_etcd_io.etcd.server.v3.auth`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`authInit`, `Base.lean`): its error variables `ErrUserEmpty`, `ErrUserNotFound`,
`ErrPermissionDenied`, `ErrAuthOldRevision`, `ErrInvalidAuthToken`, and the admin side's eleven
(the auth plan's S4, 2026-10-24: `ErrRootUserNotExist`, ..., `ErrInvalidAuthMgmt`), and S5's two
(`ErrAuthFailed`, `ErrAuthNotEnabled`; translated
`errors.New` calls: leaf pointer errors without `Is`, by `EtcdGrove.ErrorStringLeaf`, whose
`Error()` returns), and `rpctypes`' token keys (from `rpctypes`' fact). Its other variables'
initializers are untranslated (`opaqueInitsOk`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.Base
public import Perennial.Proof.bytes.Link
public import Perennial.Proof.context.Link
public import Perennial.Proof.errors.Link
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.sort.Link
public import Perennial.Proof.strconv.Link
public import Perennial.Proof.strings.Link
public import Perennial.Proof.sync.Link
public import Perennial.Proof.sync.atomic.Link
public import Perennial.Proof.time.Link
public import Proof.go_etcd_io.etcd.api.v3.authpb.Init
public import Proof.go_etcd_io.etcd.api.v3.etcdserverpb.Init
public import Proof.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Init
public import Proof.go_etcd_io.etcd.pkg.v3.adt.Init
public import Proof.go_uber_org.zap.Init
public import Proof.google_golang_org.grpc.metadata.Init
public import Proof.errors.NewVar
public import Perennial.Proof.context.NewErrorString
public import Proof.runtime.PkgInitExt

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

/-- `x ∈ [a, ..., x, ...]`, linear in the list (`simp` overflows on the long ones). -/
local macro "mem_tac" : tactic =>
  `(tactic| repeat (first | exact List.Mem.head _ | apply List.Mem.tail))

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section opaqueInits
namespace go_etcd_io.etcd.server.v3.auth
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `go_etcd_io.etcd.server.v3.auth`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([reportCurrentAuthRev.init,
        currentAuthRevision.init,
        knownOptions.init,
        DefaultTTL.init,
        «_».init,
        rootPerm.init,
        ErrInvalidAuthOpts.init,
        ErrInvalidAuthMethod.init,
        ErrMissingKey.init,
        ErrKeyMismatch.init,
        ErrVerifyOnly.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

/-- **The trust boundary: `go_etcd_io.etcd.server.v3.auth`'s untranslated `init` functions return.** Goose
names a package's `func init()`s `init.<k>`, as gc does, and translates them names-only
here, so the model does not unfold them (`@! init.<k>`: the semantics' `functions`, which
the package's `Assumptions` do not constrain for them). Go runs them at program start, and
etcd starts, so each returns without panicking. A fact about the Go code, as the axioms of
other names-only functions (`EtcdGrove.prometheus.MustRegister.wp_proof`). -/
axiom initFuncsOk :
    ∀ f ∈ ([init.«0»] : List GoString),
    {{ (True : IProp GF) }} (App (Val (@! f)) (Val #())) {{ RET #(); True }}

end go_etcd_io.etcd.server.v3.auth
end opaqueInits

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.go_etcd_io.etcd.server.v3.auth.Assumptions]
variable [EtcdGrove.ErrorStringLeaf]
variable [EtcdGrove.RpctypesEtcdErrorMethods]
variable [_root_.Perennial.context.ErrorStringIsError]
  [_root_.Perennial.context.DeadlineExceededIsError]

namespace go_etcd_io.etcd.server.v3.auth

set_option maxHeartbeats 8000000 in
theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.etcd.server.v3.auth get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrInvalidAuthMgmt _ as HErrInvalidAuthMgmt
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrInvalidAuthToken _ as HErrInvalidAuthToken
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrAuthOldRevision _ as HErrAuthOldRevision
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrAuthNotEnabled _ as HErrAuthNotEnabled
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrPermissionNotGranted _ as HErrPermissionNotGranted
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrRoleNotGranted _ as HErrRoleNotGranted
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrPermissionDenied _ as HErrPermissionDenied
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrNoPasswordUser _ as HErrNoPasswordUser
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrAuthFailed _ as HErrAuthFailed
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrPermissionNotGiven _ as HErrPermissionNotGiven
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrRoleEmpty _ as HErrRoleEmpty
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrRoleNotFound _ as HErrRoleNotFound
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrRoleAlreadyExist _ as HErrRoleAlreadyExist
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrUserNotFound _ as HErrUserNotFound
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrUserEmpty _ as HErrUserEmpty
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrUserAlreadyExist _ as HErrUserAlreadyExist
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrRootRoleNotExist _ as HErrRootRoleNotExist
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrRootUserNotExist _ as HErrRootUserNotExist
  wp_apply wp_GlobalAlloc (V := w64) simpleTokenTTLResolution _ as HsimpleTokenTTLResolution
  wp_apply wp_GlobalAlloc (V := w64) simpleTokenTTLDefault _ as HsimpleTokenTTLDefault
  wp_apply (_root_.Perennial.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd16⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.api.v3.etcdserverpb.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd15⟩
  wp_apply (_root_.Perennial.google_golang_org.grpc.metadata.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd14⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sync.atomic _root_.Perennial.sync.atomic.initialize'
      EtcdGrove.ExternalInit.sync_atomic _root_.Perennial.sync.atomic.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd13⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sort _root_.Perennial.sort.initialize'
      EtcdGrove.ExternalInit.sort _root_.Perennial.sort.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd12⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.bytes _root_.Perennial.bytes.initialize'
      EtcdGrove.ExternalInit.bytes _root_.Perennial.bytes.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd11⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.strings _root_.Perennial.strings.initialize'
      EtcdGrove.ExternalInit.strings _root_.Perennial.strings.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd10⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.strconv _root_.Perennial.strconv.initialize'
      EtcdGrove.ExternalInit.strconv _root_.Perennial.strconv.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd9⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.pkg.v3.adt.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd8⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.api.v3.authpb.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd7⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.fmt _root_.Perennial.fmt.initialize'
      EtcdGrove.ExternalInit.fmt _root_.Perennial.fmt.wp_initialize' _ Hinit.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd6⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sync _root_.Perennial.sync.initialize'
      EtcdGrove.ExternalInit.sync _root_.Perennial.sync.wp_initialize' _ Hinit.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply (_root_.Perennial.go_uber_org.zap.wp_initialize'_lb _ Hinit.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.time _root_.Perennial.time.initialize'
      EtcdGrove.ExternalInit.time _root_.Perennial.time.wp_initialize' _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.errors _root_.Perennial.errors.initialize'
      EtcdGrove.ExternalInit.errors _root_.Perennial.errors.wp_initialize' _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.context _root_.Perennial.context.initialize'
      EtcdGrove.ExternalInit.context _root_.Perennial.context.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  wp_apply (opaqueInitsOk reportCurrentAuthRev.init (by mem_tac))
  wp_apply (opaqueInitsOk currentAuthRevision.init (by mem_tac))
  wp_apply (opaqueInitsOk knownOptions.init (by mem_tac))
  wp_apply (opaqueInitsOk DefaultTTL.init (by mem_tac))
  -- translated initializer of simpleTokenTTLDefault))
  -- translated initializer of simpleTokenTTLResolution))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk rootPerm.init (by mem_tac))
  -- translated initializer of ErrRootUserNotExist))
  -- translated initializer of ErrRootRoleNotExist))
  -- translated initializer of ErrUserAlreadyExist))
  -- translated initializer of ErrUserEmpty))
  -- translated initializer of ErrUserNotFound))
  -- translated initializer of ErrRoleAlreadyExist))
  -- translated initializer of ErrRoleNotFound))
  -- translated initializer of ErrRoleEmpty))
  -- translated initializer of ErrPermissionNotGiven))
  -- translated initializer of ErrAuthFailed))
  -- translated initializer of ErrNoPasswordUser))
  -- translated initializer of ErrPermissionDenied))
  -- translated initializer of ErrRoleNotGranted))
  -- translated initializer of ErrPermissionNotGranted))
  -- translated initializer of ErrAuthNotEnabled))
  -- translated initializer of ErrAuthOldRevision))
  -- translated initializer of ErrInvalidAuthToken))
  wp_apply _root_.Perennial.context.wp_New_errorString as %xErrRootUserNotExist #MErrRootUserNotExist
  wp_apply _root_.Perennial.context.wp_New_errorString as %xErrRootRoleNotExist #MErrRootRoleNotExist
  wp_apply _root_.Perennial.context.wp_New_errorString as %xErrUserAlreadyExist #MErrUserAlreadyExist
  wp_apply _root_.Perennial.context.wp_New_errorString as %xErrUserEmpty #MErrUserEmpty
  wp_apply _root_.Perennial.context.wp_New_errorString as %xErrUserNotFound #MErrUserNotFound
  wp_apply _root_.Perennial.context.wp_New_errorString as %xErrRoleAlreadyExist #MErrRoleAlreadyExist
  wp_apply _root_.Perennial.context.wp_New_errorString as %xErrRoleNotFound #MErrRoleNotFound
  wp_apply _root_.Perennial.context.wp_New_errorString as %xErrRoleEmpty #MErrRoleEmpty
  wp_apply _root_.Perennial.context.wp_New_errorString as %xErrPermissionNotGiven #MErrPermissionNotGiven
  wp_apply _root_.Perennial.context.wp_New_errorString as %xErrAuthFailed #MErrAuthFailed
  wp_apply _root_.Perennial.context.wp_New_errorString as %xErrNoPasswordUser #MErrNoPasswordUser
  wp_apply _root_.Perennial.context.wp_New_errorString as %xErrPermissionDenied #MErrPermissionDenied
  wp_apply _root_.Perennial.context.wp_New_errorString as %xErrRoleNotGranted #MErrRoleNotGranted
  wp_apply _root_.Perennial.context.wp_New_errorString as %xErrPermissionNotGranted #MErrPermissionNotGranted
  wp_apply _root_.Perennial.context.wp_New_errorString as %xErrAuthNotEnabled #MErrAuthNotEnabled
  wp_apply _root_.Perennial.context.wp_New_errorString as %xErrAuthOldRevision #MErrAuthOldRevision
  wp_apply _root_.Perennial.context.wp_New_errorString as %xErrInvalidAuthToken #MErrInvalidAuthToken
  wp_apply (opaqueInitsOk ErrInvalidAuthOpts.init (by mem_tac))
  -- translated initializer of ErrInvalidAuthMgmt))
  wp_apply _root_.Perennial.context.wp_New_errorString as %xErrInvalidAuthMgmt #MErrInvalidAuthMgmt
  wp_apply (opaqueInitsOk ErrInvalidAuthMethod.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrMissingKey.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrKeyMismatch.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrVerifyOnly.init (by mem_tac))
  wp_apply (initFuncsOk init.«0» (by mem_tac))
  ipersist HErrRootUserNotExist
  ipersist HErrRootRoleNotExist
  ipersist HErrUserAlreadyExist
  ipersist HErrUserEmpty
  ipersist HErrUserNotFound
  ipersist HErrRoleAlreadyExist
  ipersist HErrRoleNotFound
  ipersist HErrRoleEmpty
  ipersist HErrPermissionNotGiven
  ipersist HErrAuthFailed
  ipersist HErrNoPasswordUser
  ipersist HErrPermissionDenied
  ipersist HErrRoleNotGranted
  ipersist HErrPermissionNotGranted
  ipersist HErrAuthNotEnabled
  ipersist HErrAuthOldRevision
  ipersist HErrInvalidAuthToken
  ipersist HErrInvalidAuthMgmt
  ihave #TErrRootUserNotExist := EtcdGrove.errorMsg_triple _ _ _ $$ MErrRootUserNotExist
  ihave #TErrRootRoleNotExist := EtcdGrove.errorMsg_triple _ _ _ $$ MErrRootRoleNotExist
  ihave #TErrUserAlreadyExist := EtcdGrove.errorMsg_triple _ _ _ $$ MErrUserAlreadyExist
  ihave #TErrUserEmpty := EtcdGrove.errorMsg_triple _ _ _ $$ MErrUserEmpty
  ihave #TErrUserNotFound := EtcdGrove.errorMsg_triple _ _ _ $$ MErrUserNotFound
  ihave #TErrRoleAlreadyExist := EtcdGrove.errorMsg_triple _ _ _ $$ MErrRoleAlreadyExist
  ihave #TErrRoleNotFound := EtcdGrove.errorMsg_triple _ _ _ $$ MErrRoleNotFound
  ihave #TErrRoleEmpty := EtcdGrove.errorMsg_triple _ _ _ $$ MErrRoleEmpty
  ihave #TErrPermissionNotGiven := EtcdGrove.errorMsg_triple _ _ _ $$ MErrPermissionNotGiven
  ihave #TErrAuthFailed := EtcdGrove.errorMsg_triple _ _ _ $$ MErrAuthFailed
  ihave #TErrNoPasswordUser := EtcdGrove.errorMsg_triple _ _ _ $$ MErrNoPasswordUser
  ihave #TErrPermissionDenied := EtcdGrove.errorMsg_triple _ _ _ $$ MErrPermissionDenied
  ihave #TErrRoleNotGranted := EtcdGrove.errorMsg_triple _ _ _ $$ MErrRoleNotGranted
  ihave #TErrPermissionNotGranted := EtcdGrove.errorMsg_triple _ _ _ $$ MErrPermissionNotGranted
  ihave #TErrAuthNotEnabled := EtcdGrove.errorMsg_triple _ _ _ $$ MErrAuthNotEnabled
  ihave #TErrAuthOldRevision := EtcdGrove.errorMsg_triple _ _ _ $$ MErrAuthOldRevision
  ihave #TErrInvalidAuthToken := EtcdGrove.errorMsg_triple _ _ _ $$ MErrInvalidAuthToken
  ihave #TErrInvalidAuthMgmt := EtcdGrove.errorMsg_triple _ _ _ $$ MErrInvalidAuthMgmt
  ihave Hri : (go_etcd_io.etcd.cache.v3.rpctypesInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hd16
  icases Hri with ⟨-, -, -, -, -, -, -, -, -, #HTG, #HTS, -⟩
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish
  imodintro
  unfold authInit authErrVar
  iframe #
  dsimp only
  iframe #
  repeat (first | (isplitl []; · (ipureintro; exact EtcdGrove.errorString_leaf _)) | (ipureintro; exact EtcdGrove.errorString_leaf _))

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.etcd.server.v3.auth get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end go_etcd_io.etcd.server.v3.auth

end init

end Perennial
