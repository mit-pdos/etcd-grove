/-
Package initialization of `go_etcd_io.etcd.api.v3.v3rpc.rpctypes`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

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
public import Proof.google_golang_org.grpc.status.Init
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

/-- `ErrNoLeader = Error(ErrGRPCNoLeader)` (`error.go`): an `EtcdError`. -/
axiom ErrNoLeader_init :
    {{ (True : IProp GF) }} (App (Val ErrNoLeader.init) (Val #()))
    {{ RET #(); ∃ x : EtcdError, globalAddr ErrNoLeader ↦ interface.mkOk EtcdError.ty #x }}

/-- `ErrAuthNotEnabled = Error(ErrGRPCAuthNotEnabled)` (`error.go`): an `EtcdError`. -/
axiom ErrAuthNotEnabled_init :
    {{ (True : IProp GF) }} (App (Val ErrAuthNotEnabled.init) (Val #()))
    {{ RET #(); ∃ x : EtcdError, globalAddr ErrAuthNotEnabled ↦ interface.mkOk EtcdError.ty #x }}

end go_etcd_io.etcd.api.v3.v3rpc.rpctypes
end opaqueInits

/-- **The method set of `rpctypes.EtcdError`** is `{Code, Error}` (`error.go`): no `As`,
`Unwrap`, `GRPCStatus` or `Is` method: a theorem of the method set goose emits
(`EtcdError.TypeAssumptions.method_set`), as `EtcdGrove.ErrorStringLeaf`. -/
class EtcdGrove.RpctypesEtcdErrorMethods [GooseExts] [GoGlobalContext] [GoSemanticsFunctions] : Prop where
  leaf : ∀ v : val, errors.isLeafError ⟨go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty, v⟩
  noGRPCStatus : methodSet go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty !! go!"GRPCStatus" = none
  noIs : methodSet go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty !! go!"Is" = none
  /-- (premise-fixes-4) nor a `Format` method (`fmt` prints it with its `Error`). -/
  noFormat : methodSet go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty !! go!"Format" = none
  /-- (fmt soundness 2) and its `Error` is `Error() string` (what `fmt.argOk` asks). -/
  errorSig : methodSet go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty !! go!"Error" =
    some (go.signature.Signature [] false [go.string])

instance EtcdGrove.rpctypesEtcdErrorMethods_inst [GooseExts] [GoGlobalContext] [GoLocalContext]
    [GoSemanticsFunctions] [_root_.Perennial.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions] :
    EtcdGrove.RpctypesEtcdErrorMethods := by
  have h := fun m => go.method_set_is (t := go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty) m
  have hAs := h go!"As"; have hU := h go!"Unwrap"; have hG := h go!"GRPCStatus"; have hIs := h go!"Is"
  have hF := h go!"Format"; have hE := h go!"Error"
  simp only [go.methodSetLookup_cons, go.methodSetLookup_nil, gooseReduceIteDecide] at hAs hU hG hIs hF hE
  exact ⟨fun _ => by simp [errors.isLeafError, hAs, hU], hG, hIs, hF, hE⟩

/-- `rpctypes.EtcdError` implements `error` (its `Error` has a value receiver): a target
`errors.As` accepts. -/
theorem EtcdGrove.rpctypesEtcdError_asTarget [GooseExts] [GoGlobalContext] [GoLocalContext]
    [sem : go.Semantics] [_root_.Perennial.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions] :
    errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty :=
  Or.inr (by go_type_set)

end Perennial
