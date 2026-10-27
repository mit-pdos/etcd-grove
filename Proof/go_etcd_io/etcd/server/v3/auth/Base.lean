/-
Package initialization instances for etcd's auth store (`server/v3/auth`; with bodies since unit
P2, 2026-10-14: the request side of `authStore`) and the package its request side imports that no
lower proof module provides: grpc's `metadata` (types and names only: `MD`,
`FromIncomingContext`). Moved here from the apply package's `Base.lean`, which imports this file.
The others are the cache's (`cache/v3/Base.lean`: `zap`, `authpb`, `etcdserverpb`, `rpctypes`),
`adt`'s (`pkg/v3/adt/Base.lean`) and Perennial's (`sync`, `sync/atomic`, `strings`, `context`,
`errors`).

As in those, the package facts are assumptions about package initialization, not proved from
`initialize'`: `authInit` states what the proved methods read: the error variables they return
(`ErrUserEmpty`, `ErrUserNotFound`, `ErrPermissionDenied`, `ErrAuthOldRevision`,
`ErrInvalidAuthToken`, the admin side's eleven, S4, and S5's `ErrAuthFailed`, `ErrAuthNotEnabled`: `errors.New(...)`, each a fixed leaf pointer error whose `Error()`
returns, `authErrVar`, the shape of the apply package's `errVarLeaf`), and the two token keys of
`rpctypes` that `AuthInfoFromCtx` looks up (`TokenFieldNameGRPC`, `TokenFieldNameSwagger`:
read-only, `"token"` and `"authorization"`, the auth plan's E2c), stated here as the txn package states its foreign errors.
-/
module

public import Code.go_etcd_io.etcd.server.v3.auth
public import GeneratedProof.go_etcd_io.etcd.server.v3.auth
public import Code.google_golang_org.grpc.metadata
public import GeneratedProof.google_golang_org.grpc.metadata
public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Proof.go_etcd_io.etcd.pkg.v3.adt.Base
public import Perennial.Proof.sync
public import Perennial.Proof.sync.RWMutexGuard
public import Perennial.Proof.strings
public import Perennial.Proof.strconv.Base
public import Perennial.Proof.context
public import Perennial.Proof.errors
public import Proof.errors.NewVarCell

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

-- `google.golang.org/grpc/metadata` (types and names only): its initialization is in
-- `cache/v3/Base.lean` (unit W-W: grpc imports it, for its stream interfaces' `Header`/`Trailer`)

-- names only but for the cost bounds `NewAuthStore` reads (the auth plan's E2a, 2026-10-25)
namespace golang_org.x.crypto.bcrypt

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.golang_org.x.crypto.bcrypt :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.golang_org.x.crypto.bcrypt :=
  build_get_is_pkg_init_wf

end golang_org.x.crypto.bcrypt

namespace go_etcd_io.etcd.server.v3.auth

/-- The error variable `g` holds an `errors.New` error: a leaf pointer error without an `Is`
method whose `Error()` returns (the shape of the apply package's `errVarLeaf`, which the auth
package cannot import: the apply package imports it). -/
def authErrVar (g : GoString) : IProp GF :=
  iprop(∃ e : GoInterfaceOk, globalAddr g ↦□ GoInterface.ok e ∗
    ⌜_root_.Perennial.errors.IsPointerError e ∧ _root_.Perennial.errors.isLeafError e ∧
      methodSet e.ty !! go!"Is" ≠ some (go.Signature [go.error] false [go.bool])⌝ ∗
    {{ True }} (App (Val #(methods e.ty go!"Error" e.v)) (Val #()))
      {{ (msg : GoString), RET #msg; True }})

instance authErrVar_persistent (g : GoString) : Persistent (authErrVar (GF := GF) g) := by
  unfold authErrVar; infer_instance

/-- What the metrics reporter's lock `reportCurrentAuthRevMu` guards at `q`: the reporter
`reportCurrentAuthRev` (some closure; Prometheus's collector, which no verified code calls, runs it). -/
def reportP (q : Qp) : IProp GF :=
  iprop(∃ f : GoFunc, typedPointsto (globalAddr reportCurrentAuthRev) f (DFrac.own q))

instance reportP_fractional : Fractional (reportP (GF := GF)) where
  fractional q1 q2 := by
    unfold reportP
    constructor
    · iintro ⟨%f, Hf⟩
      icases (typedPointsto_frac_add _ _ q1 q2).1 $$ Hf with ⟨H1, H2⟩
      isplitl [H1]
      · iexists f; iexact H1
      · iexists f; iexact H2
    · iintro ⟨⟨%f1, H1⟩, ⟨%f2, H2⟩⟩
      icombine H1 H2 gives %Heq
      subst Heq
      iexists f1
      iapply (typedPointsto_frac_add _ _ q1 q2).2 $$ [$H1 $H2]

/-- **The auth package's `errors.New` variables with their messages** (`store.go`; the auth plan's
E3i, 2026-10-27): what tells them apart from other packages' error variables (`errVarCells`, the
message cells: the server's `applyEntryNormal` needs an auth rejection told apart from
`etcdserver/errors.ErrNoSpace`, the apply package's `applyErrVars`). The translated ones, in
`store.go`'s order. -/
def authErrMsgs : List (GoString × GoString) := [
  (ErrRootUserNotExist, go!"auth: root user does not exist"),
  (ErrRootRoleNotExist, go!"auth: root user does not have root role"),
  (ErrUserAlreadyExist, go!"auth: user already exists"),
  (ErrUserEmpty, go!"auth: user name is empty"),
  (ErrUserNotFound, go!"auth: user not found"),
  (ErrRoleAlreadyExist, go!"auth: role already exists"),
  (ErrRoleNotFound, go!"auth: role not found"),
  (ErrRoleEmpty, go!"auth: role name is empty"),
  (ErrPermissionNotGiven, go!"auth: permission not given"),
  (ErrAuthFailed, go!"auth: authentication failed, invalid user ID or password"),
  (ErrNoPasswordUser, go!"auth: authentication failed, password was given for no password user"),
  (ErrPermissionDenied, go!"auth: permission denied"),
  (ErrRoleNotGranted, go!"auth: role is not granted to the user"),
  (ErrPermissionNotGranted, go!"auth: permission is not granted to the role"),
  (ErrAuthNotEnabled, go!"auth: authentication is not enabled"),
  (ErrAuthOldRevision, go!"auth: revision in header is old"),
  (ErrInvalidAuthToken, go!"auth: invalid auth token"),
  (ErrInvalidAuthOpts, go!"auth: invalid auth options"),
  (ErrInvalidAuthMgmt, go!"auth: invalid auth management")]

/-- The messages of `authErrMsgs` (a literal list: what `decide` can compare with another
message). -/
def authErrTexts : List GoString := [
  go!"auth: root user does not exist",
  go!"auth: root user does not have root role",
  go!"auth: user already exists",
  go!"auth: user name is empty",
  go!"auth: user not found",
  go!"auth: role already exists",
  go!"auth: role not found",
  go!"auth: role name is empty",
  go!"auth: permission not given",
  go!"auth: authentication failed, invalid user ID or password",
  go!"auth: authentication failed, password was given for no password user",
  go!"auth: permission denied",
  go!"auth: role is not granted to the user",
  go!"auth: permission is not granted to the role",
  go!"auth: authentication is not enabled",
  go!"auth: revision in header is old",
  go!"auth: invalid auth token",
  go!"auth: invalid auth options",
  go!"auth: invalid auth management"]

theorem authErrMsgs_snd : authErrMsgs.map Prod.snd = authErrTexts := rfl

/-- A message none of the auth package's error variables has. -/
theorem authErrMsgs_ne_of (m : GoString) (h : m ∉ authErrTexts) :
    ∀ p ∈ authErrMsgs, p.2 ≠ m := by
  intro p hp heq
  apply h
  rw [← authErrMsgs_snd, ← heq]
  exact List.mem_map_of_mem hp

/-- The auth package's facts: its error variables the request side returns (`authErrVar`), and
`rpctypes`' token keys (fixed read-only strings). -/
abbrev authInit : IProp GF :=
  iprop(authErrVar ErrUserEmpty ∗ authErrVar ErrUserNotFound ∗ authErrVar ErrPermissionDenied ∗
    authErrVar ErrAuthOldRevision ∗ authErrVar ErrInvalidAuthToken ∗
    globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.TokenFieldNameGRPC ↦□ go!"token" ∗
    globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.TokenFieldNameSwagger ↦□ go!"authorization" ∗
    -- the admin side's (the auth plan's S4, 2026-10-24), appended
    authErrVar ErrRootUserNotExist ∗ authErrVar ErrRootRoleNotExist ∗
    authErrVar ErrUserAlreadyExist ∗ authErrVar ErrRoleAlreadyExist ∗ authErrVar ErrRoleNotFound ∗
    authErrVar ErrRoleEmpty ∗ authErrVar ErrPermissionNotGiven ∗ authErrVar ErrNoPasswordUser ∗
    authErrVar ErrRoleNotGranted ∗ authErrVar ErrPermissionNotGranted ∗
    authErrVar ErrInvalidAuthMgmt ∗
    -- the token binding's (the auth plan's S5, 2026-10-24), appended
    authErrVar ErrAuthFailed ∗ authErrVar ErrAuthNotEnabled ∗
    -- the TTL keeper's tick (the auth plan's S5e, 2026-10-25), appended: read-only (the package's
    -- code never writes it; etcd's tests do, outside the verified code), positive
    (∃ d : w64, globalAddr simpleTokenTTLResolution ↦□ d ∗ ⌜0 < sint.Z d⌝) ∗
    -- the metrics reporter's lock (the auth plan's E2a, 2026-10-25), appended: a guarded
    -- `RWMutex` over the reporter, which `setupMetricsReporter` takes to set it
    sync.isRWMutexGuard (globalAddr reportCurrentAuthRevMu) reportP ∗
    -- the token provider's constructor's error (the auth plan's E2g, 2026-10-25), appended
    authErrVar ErrInvalidAuthOpts ∗
    -- the error variables' message cells (the auth plan's E3i, 2026-10-27), appended
    EtcdGrove.errVarCells authErrMsgs)

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth :=
  define_is_pkg_init authInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.auth

end init

end Perennial
