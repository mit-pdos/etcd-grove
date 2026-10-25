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
fixed read-only strings), stated here as the txn package states its foreign errors.
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

/-- The auth package's facts: its error variables the request side returns (`authErrVar`), and
`rpctypes`' token keys (fixed read-only strings). -/
abbrev authInit : IProp GF :=
  iprop(authErrVar ErrUserEmpty ∗ authErrVar ErrUserNotFound ∗ authErrVar ErrPermissionDenied ∗
    authErrVar ErrAuthOldRevision ∗ authErrVar ErrInvalidAuthToken ∗
    (∃ s : GoString,
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.TokenFieldNameGRPC ↦□ s) ∗
    (∃ s : GoString,
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.TokenFieldNameSwagger ↦□ s) ∗
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
    sync.isRWMutexGuard (globalAddr reportCurrentAuthRevMu) reportP)

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth :=
  define_is_pkg_init authInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.auth

end init

end Perennial
