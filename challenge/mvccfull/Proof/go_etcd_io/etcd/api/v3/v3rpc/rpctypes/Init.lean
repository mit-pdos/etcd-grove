/-
Package initialization of `go_etcd_io.etcd.api.v3.v3rpc.rpctypes`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`rpctypesInit`, `cache/v3/Base.lean`): the errors `ErrFutureRev`, `ErrCompacted`
(`EtcdError`s, whose `Error()` returns), the map `errStringToError` (its values `status.Error`
errors grpc's `status` accepts), `EtcdError`'s method set (`EtcdGrove.RpctypesEtcdErrorMethods`, of
the method set goose emits), the `EtcdError`s `ErrUserEmpty`, `ErrInvalidAuthToken`,
`ErrAuthOldRevision`, `ErrNoLeader`, `ErrAuthNotEnabled` and the pointer error `ErrGRPCNotSupportedForLearner`, the token keys, the `ErrGRPC*` errors
`v3rpc`'s checks and interceptors return and its metadata keys, and (D19j) the `ErrGRPC*` errors its
watch server returns, whose `Error()` returns. Its variables'
initializers (`error.go`, `metadatafields.go`) are untranslated: the trust-boundary axioms
`<X>_init` state the ones the fact reads, `opaqueInitsOk` the others.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Proof.google_golang_org.grpc.codes.Init
public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory.Pkg
public import Code.go_etcd_io.raft.v3
public import Code.go_etcd_io.raft.v3.confchange
public import Code.go_etcd_io.raft.v3.raftpb
public import Code.go_etcd_io.raft.v3.tracker
public import Code.google_golang_org.protobuf.proto
public import Code.k8s_io.utils.third_party.forked.golang.btree
public import Perennial.Code.bytes
public import Perennial.Code.cmp
public import Perennial.Code.context
public import Perennial.Code.encoding.binary
public import Perennial.Code.errors
public import Perennial.Code.fmt
public import Perennial.Code.github_com.goose_lang.primitive
public import Perennial.Code.internal.oserror
public import Perennial.Code.internal.stringslite
public import Perennial.Code.io
public import Perennial.Code.iter
public import Perennial.Code.log
public import Perennial.Code.math
public import Perennial.Code.slices
public import Perennial.Code.sort
public import Perennial.Code.strconv
public import Perennial.Code.strings
public import Perennial.Code.sync
public import Perennial.Code.sync.atomic
public import Perennial.Code.time
public import Perennial.Code.«unsafe»
public import Perennial.Golang.Theory.TypeSet

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
namespace go_etcd_io.etcd.api.v3.v3rpc.rpctypes
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `go_etcd_io.etcd.api.v3.v3rpc.rpctypes`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([ErrGRPCLeaseNotFound.init,
        ErrGRPCLeaseExist.init,
        ErrGRPCLeaseTTLTooLarge.init,
        ErrGRPCMemberExist.init,
        ErrGRPCPeerURLExist.init,
        ErrGRPCMemberNotEnoughStarted.init,
        ErrGRPCMemberBadURLs.init,
        ErrGRPCMemberNotFound.init,
        ErrGRPCMemberNotLearner.init,
        ErrGRPCLearnerNotReady.init,
        ErrGRPCTooManyLearners.init,
        ErrGRPCClusterIDMismatch.init,
        ErrGRPCClusterIdMismatch.init,
        ErrGRPCRequestTooLarge.init,
        ErrGRPCRequestTooManyRequests.init,
        ErrGRPCRootUserNotExist.init,
        ErrGRPCRootRoleNotExist.init,
        ErrGRPCUserAlreadyExist.init,
        ErrGRPCUserNotFound.init,
        ErrGRPCRoleAlreadyExist.init,
        ErrGRPCRoleNotFound.init,
        ErrGRPCRoleEmpty.init,
        ErrGRPCAuthFailed.init,
        ErrGRPCPermissionNotGiven.init,
        ErrGRPCRoleNotGranted.init,
        ErrGRPCPermissionNotGranted.init,
        ErrGRPCAuthNotEnabled.init,
        ErrGRPCInvalidAuthMgmt.init,
        ErrGRPCNotLeader.init,
        ErrGRPCLeaderChanged.init,
        ErrGRPCStopped.init,
        ErrGRPCTimeout.init,
        ErrGRPCTimeoutDueToLeaderFail.init,
        ErrGRPCTimeoutDueToConnectionLost.init,
        ErrGRPCTimeoutWaitAppliedIndex.init,
        ErrGRPCUnhealthy.init,
        ErrGRPCCorrupt.init,
        ErrGRPCBadLeaderTransferee.init,
        ErrGRPCWrongDowngradeVersionFormat.init,
        ErrGRPCInvalidDowngradeTargetVersion.init,
        ErrGRPCClusterVersionUnavailable.init,
        ErrGRPCDowngradeInProcess.init,
        ErrGRPCNoInflightDowngrade.init,
        ErrGRPCCanceled.init,
        ErrGRPCDeadlineExceeded.init,
        ErrEmptyKey.init,
        ErrKeyNotFound.init,
        ErrValueProvided.init,
        ErrLeaseProvided.init,
        ErrTooManyOps.init,
        ErrDuplicateKey.init,
        ErrInvalidSortOption.init,
        ErrNoSpace.init,
        ErrLeaseNotFound.init,
        ErrLeaseExist.init,
        ErrLeaseTTLTooLarge.init,
        ErrMemberExist.init,
        ErrPeerURLExist.init,
        ErrMemberNotEnoughStarted.init,
        ErrMemberBadURLs.init,
        ErrMemberNotFound.init,
        ErrMemberNotLearner.init,
        ErrMemberLearnerNotReady.init,
        ErrTooManyLearners.init,
        ErrRequestTooLarge.init,
        ErrTooManyRequests.init,
        ErrRootUserNotExist.init,
        ErrRootRoleNotExist.init,
        ErrUserAlreadyExist.init,
        ErrUserNotFound.init,
        ErrRoleAlreadyExist.init,
        ErrRoleNotFound.init,
        ErrRoleEmpty.init,
        ErrAuthFailed.init,
        ErrPermissionDenied.init,
        ErrRoleNotGranted.init,
        ErrPermissionNotGranted.init,
        ErrInvalidAuthMgmt.init,
        ErrClusterIDMismatch.init,
        ErrClusterIdMismatch.init,
        ErrNotLeader.init,
        ErrLeaderChanged.init,
        ErrNotCapable.init,
        ErrStopped.init,
        ErrTimeout.init,
        ErrTimeoutDueToLeaderFail.init,
        ErrTimeoutDueToConnectionLost.init,
        ErrTimeoutWaitAppliedIndex.init,
        ErrUnhealthy.init,
        ErrCorrupt.init,
        ErrBadLeaderTransferee.init,
        ErrClusterVersionUnavailable.init,
        ErrWrongDowngradeVersionFormat.init,
        ErrInvalidDowngradeTargetVersion.init,
        ErrDowngradeInProcess.init,
        ErrNoInflightDowngrade.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

/-- `ErrFutureRev = Error(ErrGRPCFutureRev)` (`error.go`): an `EtcdError`, whose `Error()` returns its description, `ErrGRPCFutureRev`'s (k8s etcd3 7c), with no `Format` method (an `EtcdError`'s method set is `{Code, Error}`: `fmt` prints it through `Error()`; premise-fixes-4), an `EtcdError` value (k8s etcd3 7e-2, D1: stated, checked by `examples/k8s7e2attack`'s `TestRpctypesErrTypes` at the etcd pin). -/
axiom ErrFutureRev_init :
    {{ (True : IProp GF) }} (App (Val ErrFutureRev.init) (Val #()))
    {{ RET #(); ∃ e : GoInterfaceOk, globalAddr ErrFutureRev ↦ GoInterface.ok e ∗ go_etcd_io.etcd.cache.v3.errorStringSpec e ∗ ⌜go_etcd_io.etcd.cache.v3.errDesc (GoInterface.ok e) = go_etcd_io.etcd.cache.v3.futureRevDesc⌝ ∗ ⌜methodSet e.ty !! go!"Format" = none⌝ ∗ ⌜∃ x : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError, GoInterface.ok e = interface.mkOk go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty #x⌝ }}

/-- `ErrCompacted = Error(ErrGRPCCompacted)` (`error.go`): an `EtcdError`, whose `Error()` returns its description, `ErrGRPCCompacted`'s (k8s etcd3 7c), with no `Format` method (an `EtcdError`'s method set is `{Code, Error}`: `fmt` prints it through `Error()`; premise-fixes-4), an `EtcdError` value (k8s etcd3 7e-2, D1: stated, checked by `examples/k8s7e2attack`'s `TestRpctypesErrTypes` at the etcd pin). -/
axiom ErrCompacted_init :
    {{ (True : IProp GF) }} (App (Val ErrCompacted.init) (Val #()))
    {{ RET #(); ∃ e : GoInterfaceOk, globalAddr ErrCompacted ↦ GoInterface.ok e ∗ go_etcd_io.etcd.cache.v3.errorStringSpec e ∗ ⌜go_etcd_io.etcd.cache.v3.errDesc (GoInterface.ok e) = go_etcd_io.etcd.cache.v3.compactedDesc⌝ ∗ ⌜methodSet e.ty !! go!"Format" = none⌝ ∗ ⌜∃ x : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError, GoInterface.ok e = interface.mkOk go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty #x⌝ }}

/-- `ErrGRPCFutureRev = status.Error(codes.OutOfRange, "etcdserver: mvcc: required revision is a future revision")` (`error.go`): with that description (k8s etcd3 7c). -/
axiom ErrGRPCFutureRev_init :
    {{ (True : IProp GF) }} (App (Val ErrGRPCFutureRev.init) (Val #()))
    {{ RET #(); ∃ e : GoInterfaceOk, globalAddr ErrGRPCFutureRev ↦ GoInterface.ok e ∗ ⌜go_etcd_io.etcd.cache.v3.errDesc (GoInterface.ok e) = go_etcd_io.etcd.cache.v3.futureRevDesc⌝ }}

/-- `ErrGRPCCompacted = status.Error(codes.OutOfRange, "etcdserver: mvcc: required revision has been compacted")` (`error.go`): with that description (k8s etcd3 7c). -/
axiom ErrGRPCCompacted_init :
    {{ (True : IProp GF) }} (App (Val ErrGRPCCompacted.init) (Val #()))
    {{ RET #(); ∃ e : GoInterfaceOk, globalAddr ErrGRPCCompacted ↦ GoInterface.ok e ∗ ⌜go_etcd_io.etcd.cache.v3.errDesc (GoInterface.ok e) = go_etcd_io.etcd.cache.v3.compactedDesc⌝ }}

/-- `errStringToError = map[string]error{...}` (`error.go`): a map whose values are `ErrGRPC*` errors, `status.Error(...)`s: `*status.Error`s, leaf errors whose `Error()`, `GRPCStatus()` and `Is` return. -/
axiom errStringToError_init :
    {{ (True : IProp GF) }} (App (Val errStringToError.init) (Val #()))
    {{ RET #(); ∃ (mref : Loc) (m : GMap GoString GoInterface), globalAddr errStringToError ↦ mref ∗ mref ↦$□ m ∗ □ (∀ (k : GoString) (v : GoInterface), ⌜m !! k = some v⌝ → go_etcd_io.etcd.cache.v3.statusErrOk v) ∗ ⌜∀ (k : GoString) (v : GoInterface), m !! k = some v → go_etcd_io.etcd.cache.v3.errDesc v = k⌝ }}

/-- `ErrUserEmpty = Error(ErrGRPCUserEmpty)` (`error.go`): an `EtcdError`, with `ErrGRPCUserEmpty`'s description (D29). -/
axiom ErrUserEmpty_init :
    {{ (True : IProp GF) }} (App (Val ErrUserEmpty.init) (Val #()))
    {{ RET #(); ∃ x : EtcdError, globalAddr ErrUserEmpty ↦ interface.mkOk EtcdError.ty #x ∗ ⌜x.desc' = go!"etcdserver: user name is empty"⌝ }}

/-- `ErrInvalidAuthToken = Error(ErrGRPCInvalidAuthToken)` (`error.go`): an `EtcdError`, with `ErrGRPCInvalidAuthToken`'s description (D29). -/
axiom ErrInvalidAuthToken_init :
    {{ (True : IProp GF) }} (App (Val ErrInvalidAuthToken.init) (Val #()))
    {{ RET #(); ∃ x : EtcdError, globalAddr ErrInvalidAuthToken ↦ interface.mkOk EtcdError.ty #x ∗ ⌜x.desc' = go!"etcdserver: invalid auth token"⌝ }}

/-- `ErrAuthOldRevision = Error(ErrGRPCAuthOldRevision)` (`error.go`): an `EtcdError`, with `ErrGRPCAuthOldRevision`'s description (D29). -/
axiom ErrAuthOldRevision_init :
    {{ (True : IProp GF) }} (App (Val ErrAuthOldRevision.init) (Val #()))
    {{ RET #(); ∃ x : EtcdError, globalAddr ErrAuthOldRevision ↦ interface.mkOk EtcdError.ty #x ∗ ⌜x.desc' = go!"etcdserver: revision of auth store is old"⌝ }}

/-- `ErrGRPCNotSupportedForLearner = status.Error(codes.FailedPrecondition, "etcdserver: rpc not supported for learner")` (`error.go`): a `*status.Error`, a pointer error, with that description (D29), which grpc's `status.FromError` accepts (`statusErrOk`; k8s etcd3 7c, HS-6). -/
axiom ErrGRPCNotSupportedForLearner_init :
    {{ (True : IProp GF) }} (App (Val ErrGRPCNotSupportedForLearner.init) (Val #()))
    {{ RET #(); ∃ e : GoInterfaceOk, globalAddr ErrGRPCNotSupportedForLearner ↦ GoInterface.ok e ∗ ⌜errors.IsPointerError e⌝ ∗ ⌜go_etcd_io.etcd.cache.v3.errDesc (GoInterface.ok e) = go!"etcdserver: rpc not supported for learner"⌝ ∗ go_etcd_io.etcd.cache.v3.statusErrOk (GoInterface.ok e) }}

/-- `ErrNoLeader = Error(ErrGRPCNoLeader)` (`error.go`): an `EtcdError`. -/
axiom ErrNoLeader_init :
    {{ (True : IProp GF) }} (App (Val ErrNoLeader.init) (Val #()))
    {{ RET #(); ∃ x : EtcdError, globalAddr ErrNoLeader ↦ interface.mkOk EtcdError.ty #x }}

/-- `ErrAuthNotEnabled = Error(ErrGRPCAuthNotEnabled)` (`error.go`): an `EtcdError`. -/
axiom ErrAuthNotEnabled_init :
    {{ (True : IProp GF) }} (App (Val ErrAuthNotEnabled.init) (Val #()))
    {{ RET #(); ∃ x : EtcdError, globalAddr ErrAuthNotEnabled ↦ interface.mkOk EtcdError.ty #x }}

/-- `TokenFieldNameGRPC = "token"` (`metadatafields.go`): that string. -/
axiom TokenFieldNameGRPC_init :
    {{ (True : IProp GF) }} (App (Val TokenFieldNameGRPC.init) (Val #()))
    {{ RET #(); globalAddr TokenFieldNameGRPC ↦ go!"token" }}

/-- `TokenFieldNameSwagger = "authorization"` (`metadatafields.go`): that string. -/
axiom TokenFieldNameSwagger_init :
    {{ (True : IProp GF) }} (App (Val TokenFieldNameSwagger.init) (Val #()))
    {{ RET #(); globalAddr TokenFieldNameSwagger ↦ go!"authorization" }}

/-- `ErrGRPCEmptyKey = status.Error(codes.InvalidArgument, "etcdserver: key is not provided")` (`error.go`): a `*status.Error`, which grpc's `status.FromError` accepts (`statusErrOk`; k8s etcd3 7c, HS-6), with that description (k8s etcd3 7c). -/
axiom ErrGRPCEmptyKey_init :
    {{ (True : IProp GF) }} (App (Val ErrGRPCEmptyKey.init) (Val #()))
    {{ RET #(); ∃ e : GoInterfaceOk, globalAddr ErrGRPCEmptyKey ↦ GoInterface.ok e ∗ go_etcd_io.etcd.cache.v3.statusErrOk (GoInterface.ok e) ∗ ⌜go_etcd_io.etcd.cache.v3.errDesc (GoInterface.ok e) = go!"etcdserver: key is not provided"⌝ }}

/-- `ErrGRPCInvalidSortOption = status.Error(codes.InvalidArgument, "etcdserver: invalid sort option")` (`error.go`): a `*status.Error`, which grpc's `status.FromError` accepts (`statusErrOk`; k8s etcd3 7c, HS-6), with that description (k8s etcd3 7c). -/
axiom ErrGRPCInvalidSortOption_init :
    {{ (True : IProp GF) }} (App (Val ErrGRPCInvalidSortOption.init) (Val #()))
    {{ RET #(); ∃ e : GoInterfaceOk, globalAddr ErrGRPCInvalidSortOption ↦ GoInterface.ok e ∗ go_etcd_io.etcd.cache.v3.statusErrOk (GoInterface.ok e) ∗ ⌜go_etcd_io.etcd.cache.v3.errDesc (GoInterface.ok e) = go!"etcdserver: invalid sort option"⌝ }}

/-- `ErrGRPCValueProvided = status.Error(codes.InvalidArgument, "etcdserver: value is provided")` (`error.go`): a `*status.Error`, which grpc's `status.FromError` accepts (`statusErrOk`; k8s etcd3 7c, HS-6), with that description (k8s etcd3 7c). -/
axiom ErrGRPCValueProvided_init :
    {{ (True : IProp GF) }} (App (Val ErrGRPCValueProvided.init) (Val #()))
    {{ RET #(); ∃ e : GoInterfaceOk, globalAddr ErrGRPCValueProvided ↦ GoInterface.ok e ∗ go_etcd_io.etcd.cache.v3.statusErrOk (GoInterface.ok e) ∗ ⌜go_etcd_io.etcd.cache.v3.errDesc (GoInterface.ok e) = go!"etcdserver: value is provided"⌝ }}

/-- `ErrGRPCLeaseProvided = status.Error(codes.InvalidArgument, "etcdserver: lease is provided")` (`error.go`): a `*status.Error`, which grpc's `status.FromError` accepts (`statusErrOk`; k8s etcd3 7c, HS-6), with that description (k8s etcd3 7c). -/
axiom ErrGRPCLeaseProvided_init :
    {{ (True : IProp GF) }} (App (Val ErrGRPCLeaseProvided.init) (Val #()))
    {{ RET #(); ∃ e : GoInterfaceOk, globalAddr ErrGRPCLeaseProvided ↦ GoInterface.ok e ∗ go_etcd_io.etcd.cache.v3.statusErrOk (GoInterface.ok e) ∗ ⌜go_etcd_io.etcd.cache.v3.errDesc (GoInterface.ok e) = go!"etcdserver: lease is provided"⌝ }}

/-- `ErrGRPCTooManyOps = status.Error(codes.InvalidArgument, "etcdserver: too many operations in txn request")` (`error.go`): a `*status.Error`, which grpc's `status.FromError` accepts (`statusErrOk`; k8s etcd3 7c, HS-6), with that description (k8s etcd3 7c). -/
axiom ErrGRPCTooManyOps_init :
    {{ (True : IProp GF) }} (App (Val ErrGRPCTooManyOps.init) (Val #()))
    {{ RET #(); ∃ e : GoInterfaceOk, globalAddr ErrGRPCTooManyOps ↦ GoInterface.ok e ∗ go_etcd_io.etcd.cache.v3.statusErrOk (GoInterface.ok e) ∗ ⌜go_etcd_io.etcd.cache.v3.errDesc (GoInterface.ok e) = go!"etcdserver: too many operations in txn request"⌝ }}

/-- `ErrGRPCDuplicateKey = status.Error(codes.InvalidArgument, "etcdserver: duplicate key given in txn request")` (`error.go`): a `*status.Error`, which grpc's `status.FromError` accepts (`statusErrOk`; k8s etcd3 7c, HS-6), with that description (k8s etcd3 7c). -/
axiom ErrGRPCDuplicateKey_init :
    {{ (True : IProp GF) }} (App (Val ErrGRPCDuplicateKey.init) (Val #()))
    {{ RET #(); ∃ e : GoInterfaceOk, globalAddr ErrGRPCDuplicateKey ↦ GoInterface.ok e ∗ go_etcd_io.etcd.cache.v3.statusErrOk (GoInterface.ok e) ∗ ⌜go_etcd_io.etcd.cache.v3.errDesc (GoInterface.ok e) = go!"etcdserver: duplicate key given in txn request"⌝ }}

/-- `ErrGRPCKeyNotFound = status.Error(codes.InvalidArgument, "etcdserver: key not found")` (`error.go`): a `*status.Error`, which grpc's `status.FromError` accepts (`statusErrOk`; k8s etcd3 7c, HS-6), with that description (k8s etcd3 7c). -/
axiom ErrGRPCKeyNotFound_init :
    {{ (True : IProp GF) }} (App (Val ErrGRPCKeyNotFound.init) (Val #()))
    {{ RET #(); ∃ e : GoInterfaceOk, globalAddr ErrGRPCKeyNotFound ↦ GoInterface.ok e ∗ go_etcd_io.etcd.cache.v3.statusErrOk (GoInterface.ok e) ∗ ⌜go_etcd_io.etcd.cache.v3.errDesc (GoInterface.ok e) = go!"etcdserver: key not found"⌝ }}

/-- `ErrGRPCNoSpace = status.Error(codes.ResourceExhausted, "etcdserver: mvcc: database space exceeded")` (`error.go`): a `*status.Error`, which grpc's `status.FromError` accepts (`statusErrOk`; k8s etcd3 7c, HS-6), with that description (k8s etcd3 7c). -/
axiom ErrGRPCNoSpace_init :
    {{ (True : IProp GF) }} (App (Val ErrGRPCNoSpace.init) (Val #()))
    {{ RET #(); ∃ e : GoInterfaceOk, globalAddr ErrGRPCNoSpace ↦ GoInterface.ok e ∗ go_etcd_io.etcd.cache.v3.statusErrOk (GoInterface.ok e) ∗ ⌜go_etcd_io.etcd.cache.v3.errDesc (GoInterface.ok e) = go!"etcdserver: mvcc: database space exceeded"⌝ }}

/-- `ErrGRPCNotCapable = status.Error(codes.FailedPrecondition, "etcdserver: not capable")` (`error.go`): a `*status.Error`, which grpc's `status.FromError` accepts (`statusErrOk`; k8s etcd3 7c, HS-6), with that description (k8s etcd3 7c). -/
axiom ErrGRPCNotCapable_init :
    {{ (True : IProp GF) }} (App (Val ErrGRPCNotCapable.init) (Val #()))
    {{ RET #(); ∃ e : GoInterfaceOk, globalAddr ErrGRPCNotCapable ↦ GoInterface.ok e ∗ go_etcd_io.etcd.cache.v3.statusErrOk (GoInterface.ok e) ∗ ⌜go_etcd_io.etcd.cache.v3.errDesc (GoInterface.ok e) = go!"etcdserver: not capable"⌝ }}

/-- `ErrGRPCInvalidClientAPIVersion = status.Error(codes.InvalidArgument, "etcdserver: invalid client api version")` (`error.go`): a `*status.Error`, which grpc's `status.FromError` accepts (`statusErrOk`; k8s etcd3 7c, HS-6), with that description (k8s etcd3 7c). -/
axiom ErrGRPCInvalidClientAPIVersion_init :
    {{ (True : IProp GF) }} (App (Val ErrGRPCInvalidClientAPIVersion.init) (Val #()))
    {{ RET #(); ∃ e : GoInterfaceOk, globalAddr ErrGRPCInvalidClientAPIVersion ↦ GoInterface.ok e ∗ go_etcd_io.etcd.cache.v3.statusErrOk (GoInterface.ok e) ∗ ⌜go_etcd_io.etcd.cache.v3.errDesc (GoInterface.ok e) = go!"etcdserver: invalid client api version"⌝ }}

/-- `ErrGRPCNoLeader = status.Error(codes.Unavailable, "etcdserver: no leader")` (`error.go`): a `*status.Error`, which grpc's `status.FromError` accepts (`statusErrOk`; k8s etcd3 7c, HS-6), with that description (k8s etcd3 7c). -/
axiom ErrGRPCNoLeader_init :
    {{ (True : IProp GF) }} (App (Val ErrGRPCNoLeader.init) (Val #()))
    {{ RET #(); ∃ e : GoInterfaceOk, globalAddr ErrGRPCNoLeader ↦ GoInterface.ok e ∗ go_etcd_io.etcd.cache.v3.statusErrOk (GoInterface.ok e) ∗ ⌜go_etcd_io.etcd.cache.v3.errDesc (GoInterface.ok e) = go!"etcdserver: no leader"⌝ }}

/-- `MetadataClientAPIVersionKey = "client-api-version"` (`metadatafields.go`): a string. -/
axiom MetadataClientAPIVersionKey_init :
    {{ (True : IProp GF) }} (App (Val MetadataClientAPIVersionKey.init) (Val #()))
    {{ RET #(); ∃ k : GoString, globalAddr MetadataClientAPIVersionKey ↦ k }}

/-- `MetadataRequireLeaderKey = "hasleader"` (`metadatafields.go`): a string. -/
axiom MetadataRequireLeaderKey_init :
    {{ (True : IProp GF) }} (App (Val MetadataRequireLeaderKey.init) (Val #()))
    {{ RET #(); ∃ k : GoString, globalAddr MetadataRequireLeaderKey ↦ k }}

/-- `MetadataHasLeader = "true"` (`metadatafields.go`): a string. -/
axiom MetadataHasLeader_init :
    {{ (True : IProp GF) }} (App (Val MetadataHasLeader.init) (Val #()))
    {{ RET #(); ∃ k : GoString, globalAddr MetadataHasLeader ↦ k }}

/-- `ErrGRPCInvalidAuthToken = status.Error(codes.Unauthenticated, "etcdserver: invalid auth token")` (`error.go`): a `*status.Error`, whose `Error()` returns. -/
axiom ErrGRPCInvalidAuthToken_init :
    {{ (True : IProp GF) }} (App (Val ErrGRPCInvalidAuthToken.init) (Val #()))
    {{ RET #(); ∃ e : GoInterfaceOk, globalAddr ErrGRPCInvalidAuthToken ↦ GoInterface.ok e ∗ go_etcd_io.etcd.cache.v3.errorStringSpec e }}

/-- `ErrGRPCAuthOldRevision = status.Error(codes.InvalidArgument, "etcdserver: revision of auth store is old")` (`error.go`): a `*status.Error`, whose `Error()` returns. -/
axiom ErrGRPCAuthOldRevision_init :
    {{ (True : IProp GF) }} (App (Val ErrGRPCAuthOldRevision.init) (Val #()))
    {{ RET #(); ∃ e : GoInterfaceOk, globalAddr ErrGRPCAuthOldRevision ↦ GoInterface.ok e ∗ go_etcd_io.etcd.cache.v3.errorStringSpec e }}

/-- `ErrGRPCUserEmpty = status.Error(codes.InvalidArgument, "etcdserver: user name is empty")` (`error.go`): a `*status.Error`, whose `Error()` returns. -/
axiom ErrGRPCUserEmpty_init :
    {{ (True : IProp GF) }} (App (Val ErrGRPCUserEmpty.init) (Val #()))
    {{ RET #(); ∃ e : GoInterfaceOk, globalAddr ErrGRPCUserEmpty ↦ GoInterface.ok e ∗ go_etcd_io.etcd.cache.v3.errorStringSpec e }}

/-- `ErrGRPCPermissionDenied = status.Error(codes.PermissionDenied, "etcdserver: permission denied")` (`error.go`): a `*status.Error`, whose `Error()` returns. -/
axiom ErrGRPCPermissionDenied_init :
    {{ (True : IProp GF) }} (App (Val ErrGRPCPermissionDenied.init) (Val #()))
    {{ RET #(); ∃ e : GoInterfaceOk, globalAddr ErrGRPCPermissionDenied ↦ GoInterface.ok e ∗ go_etcd_io.etcd.cache.v3.errorStringSpec e }}

/-- `ErrGRPCWatchCanceled = status.Error(codes.Canceled, "etcdserver: watch canceled")` (`error.go`): a `*status.Error`, whose `Error()` returns, which grpc's `status.FromError` accepts (`statusErrOk`; premise-fixes-7: `watchServer.Watch` returns it). -/
axiom ErrGRPCWatchCanceled_init :
    {{ (True : IProp GF) }} (App (Val ErrGRPCWatchCanceled.init) (Val #()))
    {{ RET #(); ∃ e : GoInterfaceOk, globalAddr ErrGRPCWatchCanceled ↦ GoInterface.ok e ∗ go_etcd_io.etcd.cache.v3.errorStringSpec e ∗ go_etcd_io.etcd.cache.v3.statusErrOk (GoInterface.ok e) }}

end go_etcd_io.etcd.api.v3.v3rpc.rpctypes
end opaqueInits

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]

namespace go_etcd_io.etcd.api.v3.v3rpc.rpctypes

end go_etcd_io.etcd.api.v3.v3rpc.rpctypes

end init

end Perennial
