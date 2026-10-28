/-
Package initialization of `go_etcd_io.etcd.api.v3.v3rpc.rpctypes`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`rpctypesInit`, `cache/v3/Base.lean`): the errors `ErrFutureRev`, `ErrCompacted`
(`EtcdError`s, whose `Error()` returns), the map `errStringToError` (its values `status.Error`
errors grpc's `status` accepts), `EtcdError`'s method set (`EtcdGrove.RpctypesEtcdErrorMethods`, of
the method set goose emits), the `EtcdError`s `ErrUserEmpty`, `ErrInvalidAuthToken`,
`ErrAuthOldRevision`, `ErrNoLeader` and the pointer error `ErrGRPCNotSupportedForLearner`, the token keys, the `ErrGRPC*` errors
`v3rpc`'s checks and interceptors return and its metadata keys, and (D19j) the `ErrGRPC*` errors its
watch server returns, whose `Error()` returns. Its variables'
initializers (`error.go`, `metadatafields.go`) are untranslated: the trust-boundary axioms
`<X>_init` state the ones the fact reads, `opaqueInitsOk` the others.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Proof.google_golang_org.grpc.codes.Init
public import Proof.google_golang_org.grpc.status.Init
public import Perennial.Golang.Theory.TypeSet
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
    ∀ v ∈ ([ErrGRPCCompacted.init,
        ErrGRPCFutureRev.init,
        ErrGRPCLeaseNotFound.init,
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
        ErrAuthNotEnabled.init,
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

/-- `ErrFutureRev = Error(ErrGRPCFutureRev)` (`error.go`): an `EtcdError`, whose `Error()` returns its description. -/
axiom ErrFutureRev_init :
    {{ (True : IProp GF) }} (App (Val ErrFutureRev.init) (Val #()))
    {{ RET #(); ∃ e : GoInterfaceOk, globalAddr ErrFutureRev ↦ GoInterface.ok e ∗ go_etcd_io.etcd.cache.v3.errorStringSpec e }}

/-- `ErrCompacted = Error(ErrGRPCCompacted)` (`error.go`): an `EtcdError`, whose `Error()` returns its description. -/
axiom ErrCompacted_init :
    {{ (True : IProp GF) }} (App (Val ErrCompacted.init) (Val #()))
    {{ RET #(); ∃ e : GoInterfaceOk, globalAddr ErrCompacted ↦ GoInterface.ok e ∗ go_etcd_io.etcd.cache.v3.errorStringSpec e }}

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

/-- `ErrGRPCNotSupportedForLearner = status.Error(codes.FailedPrecondition, "etcdserver: rpc not supported for learner")` (`error.go`): a `*status.Error`, a pointer error, with that description (D29). -/
axiom ErrGRPCNotSupportedForLearner_init :
    {{ (True : IProp GF) }} (App (Val ErrGRPCNotSupportedForLearner.init) (Val #()))
    {{ RET #(); ∃ e : GoInterfaceOk, globalAddr ErrGRPCNotSupportedForLearner ↦ GoInterface.ok e ∗ ⌜errors.IsPointerError e⌝ ∗ ⌜go_etcd_io.etcd.cache.v3.errDesc (GoInterface.ok e) = go!"etcdserver: rpc not supported for learner"⌝ }}

/-- `ErrNoLeader = Error(ErrGRPCNoLeader)` (`error.go`): an `EtcdError`. -/
axiom ErrNoLeader_init :
    {{ (True : IProp GF) }} (App (Val ErrNoLeader.init) (Val #()))
    {{ RET #(); ∃ x : EtcdError, globalAddr ErrNoLeader ↦ interface.mkOk EtcdError.ty #x }}

/-- `TokenFieldNameGRPC = "token"` (`metadatafields.go`): that string. -/
axiom TokenFieldNameGRPC_init :
    {{ (True : IProp GF) }} (App (Val TokenFieldNameGRPC.init) (Val #()))
    {{ RET #(); globalAddr TokenFieldNameGRPC ↦ go!"token" }}

/-- `TokenFieldNameSwagger = "authorization"` (`metadatafields.go`): that string. -/
axiom TokenFieldNameSwagger_init :
    {{ (True : IProp GF) }} (App (Val TokenFieldNameSwagger.init) (Val #()))
    {{ RET #(); globalAddr TokenFieldNameSwagger ↦ go!"authorization" }}

/-- `ErrGRPCEmptyKey = status.Error(...)` (`error.go`): a non-nil error. -/
axiom ErrGRPCEmptyKey_init :
    {{ (True : IProp GF) }} (App (Val ErrGRPCEmptyKey.init) (Val #()))
    {{ RET #(); ∃ e : GoInterfaceOk, globalAddr ErrGRPCEmptyKey ↦ GoInterface.ok e }}

/-- `ErrGRPCInvalidSortOption = status.Error(...)` (`error.go`): a non-nil error. -/
axiom ErrGRPCInvalidSortOption_init :
    {{ (True : IProp GF) }} (App (Val ErrGRPCInvalidSortOption.init) (Val #()))
    {{ RET #(); ∃ e : GoInterfaceOk, globalAddr ErrGRPCInvalidSortOption ↦ GoInterface.ok e }}

/-- `ErrGRPCValueProvided = status.Error(...)` (`error.go`): a non-nil error. -/
axiom ErrGRPCValueProvided_init :
    {{ (True : IProp GF) }} (App (Val ErrGRPCValueProvided.init) (Val #()))
    {{ RET #(); ∃ e : GoInterfaceOk, globalAddr ErrGRPCValueProvided ↦ GoInterface.ok e }}

/-- `ErrGRPCLeaseProvided = status.Error(...)` (`error.go`): a non-nil error. -/
axiom ErrGRPCLeaseProvided_init :
    {{ (True : IProp GF) }} (App (Val ErrGRPCLeaseProvided.init) (Val #()))
    {{ RET #(); ∃ e : GoInterfaceOk, globalAddr ErrGRPCLeaseProvided ↦ GoInterface.ok e }}

/-- `ErrGRPCTooManyOps = status.Error(...)` (`error.go`): a non-nil error. -/
axiom ErrGRPCTooManyOps_init :
    {{ (True : IProp GF) }} (App (Val ErrGRPCTooManyOps.init) (Val #()))
    {{ RET #(); ∃ e : GoInterfaceOk, globalAddr ErrGRPCTooManyOps ↦ GoInterface.ok e }}

/-- `ErrGRPCDuplicateKey = status.Error(...)` (`error.go`): a non-nil error. -/
axiom ErrGRPCDuplicateKey_init :
    {{ (True : IProp GF) }} (App (Val ErrGRPCDuplicateKey.init) (Val #()))
    {{ RET #(); ∃ e : GoInterfaceOk, globalAddr ErrGRPCDuplicateKey ↦ GoInterface.ok e }}

/-- `ErrGRPCKeyNotFound = status.Error(...)` (`error.go`): a non-nil error. -/
axiom ErrGRPCKeyNotFound_init :
    {{ (True : IProp GF) }} (App (Val ErrGRPCKeyNotFound.init) (Val #()))
    {{ RET #(); ∃ e : GoInterfaceOk, globalAddr ErrGRPCKeyNotFound ↦ GoInterface.ok e }}

/-- `ErrGRPCNoSpace = status.Error(...)` (`error.go`): a non-nil error. -/
axiom ErrGRPCNoSpace_init :
    {{ (True : IProp GF) }} (App (Val ErrGRPCNoSpace.init) (Val #()))
    {{ RET #(); ∃ e : GoInterfaceOk, globalAddr ErrGRPCNoSpace ↦ GoInterface.ok e }}

/-- `ErrGRPCNotCapable = status.Error(...)` (`error.go`): a non-nil error. -/
axiom ErrGRPCNotCapable_init :
    {{ (True : IProp GF) }} (App (Val ErrGRPCNotCapable.init) (Val #()))
    {{ RET #(); ∃ e : GoInterfaceOk, globalAddr ErrGRPCNotCapable ↦ GoInterface.ok e }}

/-- `ErrGRPCInvalidClientAPIVersion = status.Error(...)` (`error.go`): a non-nil error. -/
axiom ErrGRPCInvalidClientAPIVersion_init :
    {{ (True : IProp GF) }} (App (Val ErrGRPCInvalidClientAPIVersion.init) (Val #()))
    {{ RET #(); ∃ e : GoInterfaceOk, globalAddr ErrGRPCInvalidClientAPIVersion ↦ GoInterface.ok e }}

/-- `ErrGRPCNoLeader = status.Error(...)` (`error.go`): a non-nil error. -/
axiom ErrGRPCNoLeader_init :
    {{ (True : IProp GF) }} (App (Val ErrGRPCNoLeader.init) (Val #()))
    {{ RET #(); ∃ e : GoInterfaceOk, globalAddr ErrGRPCNoLeader ↦ GoInterface.ok e }}

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

/-- `ErrGRPCWatchCanceled = status.Error(codes.Canceled, "etcdserver: watch canceled")` (`error.go`): a `*status.Error`, whose `Error()` returns. -/
axiom ErrGRPCWatchCanceled_init :
    {{ (True : IProp GF) }} (App (Val ErrGRPCWatchCanceled.init) (Val #()))
    {{ RET #(); ∃ e : GoInterfaceOk, globalAddr ErrGRPCWatchCanceled ↦ GoInterface.ok e ∗ go_etcd_io.etcd.cache.v3.errorStringSpec e }}

end go_etcd_io.etcd.api.v3.v3rpc.rpctypes
end opaqueInits

/-- **The method set of `rpctypes.EtcdError`** is `{Code, Error}` (`error.go`): no `As`,
`Unwrap`, `GRPCStatus` or `Is` method: a theorem of the method set goose emits
(`EtcdError.TypeAssumptions.method_set`), as `EtcdGrove.ErrorStringLeaf`. -/
class EtcdGrove.RpctypesEtcdErrorMethods [GooseExts] [GoGlobalContext] [GoSemanticsFunctions] : Prop where
  leaf : ∀ v : val, errors.isLeafError ⟨go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty, v⟩
  noGRPCStatus : methodSet go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty !! go!"GRPCStatus" = none
  noIs : methodSet go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty !! go!"Is" = none

instance EtcdGrove.rpctypesEtcdErrorMethods_inst [GooseExts] [GoGlobalContext] [GoLocalContext]
    [GoSemanticsFunctions] [_root_.Perennial.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions] :
    EtcdGrove.RpctypesEtcdErrorMethods := by
  have h := fun m => go.method_set_is (t := go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty) m
  have hAs := h go!"As"; have hU := h go!"Unwrap"; have hG := h go!"GRPCStatus"; have hIs := h go!"Is"
  simp only [go.methodSetLookup_cons, go.methodSetLookup_nil, gooseReduceIteDecide] at hAs hU hG hIs
  exact ⟨fun _ => by simp [errors.isLeafError, hAs, hU], hG, hIs⟩

/-- `rpctypes.EtcdError` implements `error` (its `Error` has a value receiver): a target
`errors.As` accepts. -/
theorem EtcdGrove.rpctypesEtcdError_asTarget [GooseExts] [GoGlobalContext] [GoLocalContext]
    [sem : go.Semantics] [_root_.Perennial.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions] :
    errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty :=
  Or.inr (by go_type_set)

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]

namespace go_etcd_io.etcd.api.v3.v3rpc.rpctypes

set_option maxHeartbeats 8000000 in
theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply (_root_.Perennial.google_golang_org.grpc.status.wp_initialize'_lb _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (_root_.Perennial.google_golang_org.grpc.codes.wp_initialize'_lb _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  wp_apply ErrGRPCEmptyKey_init as ⟨%eErrGRPCEmptyKey, HErrGRPCEmptyKey⟩
  wp_apply ErrGRPCKeyNotFound_init as ⟨%eErrGRPCKeyNotFound, HErrGRPCKeyNotFound⟩
  wp_apply ErrGRPCValueProvided_init as ⟨%eErrGRPCValueProvided, HErrGRPCValueProvided⟩
  wp_apply ErrGRPCLeaseProvided_init as ⟨%eErrGRPCLeaseProvided, HErrGRPCLeaseProvided⟩
  wp_apply ErrGRPCTooManyOps_init as ⟨%eErrGRPCTooManyOps, HErrGRPCTooManyOps⟩
  wp_apply ErrGRPCDuplicateKey_init as ⟨%eErrGRPCDuplicateKey, HErrGRPCDuplicateKey⟩
  wp_apply ErrGRPCInvalidClientAPIVersion_init as ⟨%eErrGRPCInvalidClientAPIVersion, HErrGRPCInvalidClientAPIVersion⟩
  wp_apply ErrGRPCInvalidSortOption_init as ⟨%eErrGRPCInvalidSortOption, HErrGRPCInvalidSortOption⟩
  wp_apply (opaqueInitsOk ErrGRPCCompacted.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrGRPCFutureRev.init (by mem_tac))
  wp_apply ErrGRPCNoSpace_init as ⟨%eErrGRPCNoSpace, HErrGRPCNoSpace⟩
  wp_apply (opaqueInitsOk ErrGRPCLeaseNotFound.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrGRPCLeaseExist.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrGRPCLeaseTTLTooLarge.init (by mem_tac))
  wp_apply ErrGRPCWatchCanceled_init as ⟨%eErrGRPCWatchCanceled, HErrGRPCWatchCanceled, #SErrGRPCWatchCanceled⟩
  wp_apply (opaqueInitsOk ErrGRPCMemberExist.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrGRPCPeerURLExist.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrGRPCMemberNotEnoughStarted.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrGRPCMemberBadURLs.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrGRPCMemberNotFound.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrGRPCMemberNotLearner.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrGRPCLearnerNotReady.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrGRPCTooManyLearners.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrGRPCClusterIDMismatch.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrGRPCClusterIdMismatch.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrGRPCRequestTooLarge.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrGRPCRequestTooManyRequests.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrGRPCRootUserNotExist.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrGRPCRootRoleNotExist.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrGRPCUserAlreadyExist.init (by mem_tac))
  wp_apply ErrGRPCUserEmpty_init as ⟨%eErrGRPCUserEmpty, HErrGRPCUserEmpty, #SErrGRPCUserEmpty⟩
  wp_apply (opaqueInitsOk ErrGRPCUserNotFound.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrGRPCRoleAlreadyExist.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrGRPCRoleNotFound.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrGRPCRoleEmpty.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrGRPCAuthFailed.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrGRPCPermissionNotGiven.init (by mem_tac))
  wp_apply ErrGRPCPermissionDenied_init as ⟨%eErrGRPCPermissionDenied, HErrGRPCPermissionDenied, #SErrGRPCPermissionDenied⟩
  wp_apply (opaqueInitsOk ErrGRPCRoleNotGranted.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrGRPCPermissionNotGranted.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrGRPCAuthNotEnabled.init (by mem_tac))
  wp_apply ErrGRPCInvalidAuthToken_init as ⟨%eErrGRPCInvalidAuthToken, HErrGRPCInvalidAuthToken, #SErrGRPCInvalidAuthToken⟩
  wp_apply (opaqueInitsOk ErrGRPCInvalidAuthMgmt.init (by mem_tac))
  wp_apply ErrGRPCAuthOldRevision_init as ⟨%eErrGRPCAuthOldRevision, HErrGRPCAuthOldRevision, #SErrGRPCAuthOldRevision⟩
  wp_apply ErrGRPCNoLeader_init as ⟨%eErrGRPCNoLeader, HErrGRPCNoLeader⟩
  wp_apply (opaqueInitsOk ErrGRPCNotLeader.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrGRPCLeaderChanged.init (by mem_tac))
  wp_apply ErrGRPCNotCapable_init as ⟨%eErrGRPCNotCapable, HErrGRPCNotCapable⟩
  wp_apply (opaqueInitsOk ErrGRPCStopped.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrGRPCTimeout.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrGRPCTimeoutDueToLeaderFail.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrGRPCTimeoutDueToConnectionLost.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrGRPCTimeoutWaitAppliedIndex.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrGRPCUnhealthy.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrGRPCCorrupt.init (by mem_tac))
  wp_apply ErrGRPCNotSupportedForLearner_init as ⟨%eErrGRPCNotSupportedForLearner, HErrGRPCNotSupportedForLearner, %PErrGRPCNotSupportedForLearner, %DErrGRPCNotSupportedForLearner⟩
  wp_apply (opaqueInitsOk ErrGRPCBadLeaderTransferee.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrGRPCWrongDowngradeVersionFormat.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrGRPCInvalidDowngradeTargetVersion.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrGRPCClusterVersionUnavailable.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrGRPCDowngradeInProcess.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrGRPCNoInflightDowngrade.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrGRPCCanceled.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrGRPCDeadlineExceeded.init (by mem_tac))
  wp_apply errStringToError_init as ⟨%mreferrStringToError, %merrStringToError, HerrStringToError, #MerrStringToError, #SerrStringToError, %DerrStringToError⟩
  wp_apply (opaqueInitsOk ErrEmptyKey.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrKeyNotFound.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrValueProvided.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrLeaseProvided.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrTooManyOps.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrDuplicateKey.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrInvalidSortOption.init (by mem_tac))
  wp_apply ErrCompacted_init as ⟨%eErrCompacted, HErrCompacted, #SErrCompacted⟩
  wp_apply ErrFutureRev_init as ⟨%eErrFutureRev, HErrFutureRev, #SErrFutureRev⟩
  wp_apply (opaqueInitsOk ErrNoSpace.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrLeaseNotFound.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrLeaseExist.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrLeaseTTLTooLarge.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrMemberExist.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrPeerURLExist.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrMemberNotEnoughStarted.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrMemberBadURLs.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrMemberNotFound.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrMemberNotLearner.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrMemberLearnerNotReady.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrTooManyLearners.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrRequestTooLarge.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrTooManyRequests.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrRootUserNotExist.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrRootRoleNotExist.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrUserAlreadyExist.init (by mem_tac))
  wp_apply ErrUserEmpty_init as ⟨%xErrUserEmpty, HErrUserEmpty, %DErrUserEmpty⟩
  wp_apply (opaqueInitsOk ErrUserNotFound.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrRoleAlreadyExist.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrRoleNotFound.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrRoleEmpty.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrAuthFailed.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrPermissionDenied.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrRoleNotGranted.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrPermissionNotGranted.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrAuthNotEnabled.init (by mem_tac))
  wp_apply ErrInvalidAuthToken_init as ⟨%xErrInvalidAuthToken, HErrInvalidAuthToken, %DErrInvalidAuthToken⟩
  wp_apply ErrAuthOldRevision_init as ⟨%xErrAuthOldRevision, HErrAuthOldRevision, %DErrAuthOldRevision⟩
  wp_apply (opaqueInitsOk ErrInvalidAuthMgmt.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrClusterIDMismatch.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrClusterIdMismatch.init (by mem_tac))
  wp_apply ErrNoLeader_init as ⟨%xErrNoLeader, HErrNoLeader⟩
  wp_apply (opaqueInitsOk ErrNotLeader.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrLeaderChanged.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrNotCapable.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrStopped.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrTimeout.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrTimeoutDueToLeaderFail.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrTimeoutDueToConnectionLost.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrTimeoutWaitAppliedIndex.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrUnhealthy.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrCorrupt.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrBadLeaderTransferee.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrClusterVersionUnavailable.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrWrongDowngradeVersionFormat.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrInvalidDowngradeTargetVersion.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrDowngradeInProcess.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrNoInflightDowngrade.init (by mem_tac))
  wp_apply MetadataRequireLeaderKey_init as ⟨%kMetadataRequireLeaderKey, HMetadataRequireLeaderKey⟩
  wp_apply MetadataHasLeader_init as ⟨%kMetadataHasLeader, HMetadataHasLeader⟩
  wp_apply MetadataClientAPIVersionKey_init as ⟨%kMetadataClientAPIVersionKey, HMetadataClientAPIVersionKey⟩
  wp_apply TokenFieldNameGRPC_init as HTokenFieldNameGRPC
  wp_apply TokenFieldNameSwagger_init as HTokenFieldNameSwagger
  ipersist HErrGRPCEmptyKey
  ipersist HErrGRPCInvalidSortOption
  ipersist HErrGRPCValueProvided
  ipersist HErrGRPCLeaseProvided
  ipersist HErrGRPCTooManyOps
  ipersist HErrGRPCDuplicateKey
  ipersist HErrGRPCKeyNotFound
  ipersist HErrGRPCNoSpace
  ipersist HErrGRPCNotCapable
  ipersist HErrGRPCInvalidClientAPIVersion
  ipersist HErrGRPCNoLeader
  ipersist HMetadataClientAPIVersionKey
  ipersist HMetadataRequireLeaderKey
  ipersist HMetadataHasLeader
  ipersist HErrGRPCInvalidAuthToken
  ipersist HErrGRPCAuthOldRevision
  ipersist HErrGRPCUserEmpty
  ipersist HErrGRPCPermissionDenied
  ipersist HErrGRPCWatchCanceled
  ipersist HTokenFieldNameGRPC
  ipersist HTokenFieldNameSwagger
  ipersist HErrFutureRev
  ipersist HErrCompacted
  ipersist HerrStringToError
  ipersist HErrUserEmpty
  ipersist HErrInvalidAuthToken
  ipersist HErrAuthOldRevision
  ipersist HErrGRPCNotSupportedForLearner
  ipersist HErrNoLeader
  ihave #HFRS : iprop(□ ∀ e : GoInterfaceOk, globalAddr ErrFutureRev ↦□ GoInterface.ok e -∗
      go_etcd_io.etcd.cache.v3.errorStringSpec e) $$ []
  · iintro !> %e He
    icombine HErrFutureRev He gives %Heq
    cases Heq
    iexact SErrFutureRev
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish
  imodintro
  unfold go_etcd_io.etcd.cache.v3.rpctypesInit
  iframe #
  ipureintro
  refine ⟨by assumption, ?_, by assumption, by assumption, by assumption, by assumption, by assumption⟩
  exact ⟨EtcdGrove.RpctypesEtcdErrorMethods.leaf, EtcdGrove.RpctypesEtcdErrorMethods.noGRPCStatus, EtcdGrove.RpctypesEtcdErrorMethods.noIs⟩

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end go_etcd_io.etcd.api.v3.v3rpc.rpctypes

end init

end Perennial
