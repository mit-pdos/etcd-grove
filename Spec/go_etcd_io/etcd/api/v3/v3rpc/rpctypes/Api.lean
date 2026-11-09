/-
# rpctypes: etcd's gRPC errors (batch 2a)

`go.etcd.io/etcd/api/v3/v3rpc/rpctypes`: the status errors the server sends (`ErrGRPC*`), the
client-side errors (`Err*`, `EtcdError` values) the client turns them into (`Error`), and the
metadata keys. The realization of W0's error vocabulary: `errVal e` (`api/v3/State.lean`) and the
client's classification `callErr err k` (`client/v3/Api.lean`).

## Vocabulary (pure)

* `desc e`, `code e`: the description and gRPC code of etcd's error `e` (the `ErrGRPC*` variable's
  `status.Error(code, desc)`), transcribed from `error.go`.
* `mapped e`: `e`'s description is a key of `errStringToError`, so that `rpctypes.Error` turns a
  status with it into `errVal e`. **Six of `EtcdErr`'s constructors are not mapped**:
  `.timeoutWaitAppliedIndex`, `.canceled`, `.deadlineExceeded`, `.invalidClientAPIVersion`, `.watchCanceled`, `.permissionNotGiven`. A status with one of their descriptions stays
  what it is through `rpctypes.Error`, and so through the client's `ContextError`: the client
  returns the status error, not `errVal e`, and classifies it `.other` (an indefinite kind).
  For the indefinite ones this loses nothing; for `.invalidClientAPIVersion` (a refusal) and
  `.permissionNotGiven` (an answer of `RoleGrantPermission`) it means W0's `ansReply`, which
  promises `err = errVal e` for every answer `.err e`, is false of the client at those two errors
  (reported to W0: `req/go_etcd_io_etcd_api_v3.md`, "from 2a"). And `rpctypes.ErrTimeoutWaitAppliedIndex`
  holds the status error itself (`Error` of an unmapped status), not `errVal .timeoutWaitAppliedIndex`.
* `grpcVar e`: the name of the variable `ErrGRPC*` of `e`; `clientVar e`: the variable `Err*` of
  `e`, when there is one (`none` for `.notSupportedForLearner`, `.invalidClientAPIVersion`,
  `.watchCanceled`, `.permissionNotGiven`, `.canceled`, `.deadlineExceeded`).

## Laws (obligations of this package's realization, over grpc's boundary)

* `init.spec`: the variables after initialization.
* `errVal_fields.spec`: `errVal e` is `EtcdError{code e, desc e}`.
* `desc_inj.spec` (a pure fact of the table: `errVal_inj` follows), `desc_not_grpcMsg.spec` (the
  boundary's assumption that no error grpc makes itself carries one of etcd's descriptions: all of
  etcd's start with `etcdserver: `, none of grpc-go's does).
* `errVal_errMsg.spec`, `errVal_not_status.spec`: what `status.FromError` sees of `errVal e`.
* `ctxErr_errMsg.spec`: a context's error's message (Go's `context`: "context canceled",
  "context deadline exceeded").
* Round 1 (completeness F2): a definite error's code is pinned (`code e`, or `Unknown` for the two
  `EtcdError`s `togRPCError` sends); `desc_ascii`, `code_not_ctx`, `callErr_eof`.
* **`callErr`'s realization**: `callErr_view.spec` (what an error of each kind is, as
  `status.FromError` sees it), and its introductions `callErr_status.spec` (a status with a mapped
  description is `.etcd e`), `callErr_ownErr.spec` (grpc's own errors are `.other`),
  `callErr_unmapped.spec` (a status whose description is no mapped one is `.other`). W0's
  `callErr_errVal`, `callErr_ctxErr`, `callErr_agree` follow from these.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Api
public import Spec.google_golang_org.grpc.Api
public import Spec.PkgInit.go_etcd_io.etcd.api.v3.v3rpc.rpctypes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Rpctypes

open Iris Iris.BI EtcdModel ClientV3

/-- **The description of etcd's error `e`** (`ErrGRPC*`'s message). -/
def desc : EtcdErr → GoString
  | .emptyKey => go!"etcdserver: key is not provided"
  | .keyNotFound => go!"etcdserver: key not found"
  | .valueProvided => go!"etcdserver: value is provided"
  | .leaseProvided => go!"etcdserver: lease is provided"
  | .tooManyOps => go!"etcdserver: too many operations in txn request"
  | .duplicateKey => go!"etcdserver: duplicate key given in txn request"
  | .invalidSortOption => go!"etcdserver: invalid sort option"
  | .compacted => go!"etcdserver: mvcc: required revision has been compacted"
  | .futureRev => go!"etcdserver: mvcc: required revision is a future revision"
  | .noSpace => go!"etcdserver: mvcc: database space exceeded"
  | .leaseNotFound => go!"etcdserver: requested lease not found"
  | .leaseExist => go!"etcdserver: lease already exists"
  | .leaseTTLTooLarge => go!"etcdserver: too large lease TTL"
  | .memberExist => go!"etcdserver: member ID already exist"
  | .peerURLExist => go!"etcdserver: Peer URLs already exists"
  | .memberNotEnoughStarted => go!"etcdserver: re-configuration failed due to not enough started members"
  | .memberBadURLs => go!"etcdserver: given member URLs are invalid"
  | .memberNotFound => go!"etcdserver: member not found"
  | .memberNotLearner => go!"etcdserver: can only promote a learner member"
  | .memberLearnerNotReady => go!"etcdserver: can only promote a learner member which is in sync with leader"
  | .tooManyLearners => go!"etcdserver: too many learner members in cluster"
  | .requestTooLarge => go!"etcdserver: request is too large"
  | .tooManyRequests => go!"etcdserver: too many requests"
  | .rootUserNotExist => go!"etcdserver: root user does not exist"
  | .rootRoleNotExist => go!"etcdserver: root user does not have root role"
  | .userAlreadyExist => go!"etcdserver: user name already exists"
  | .userEmpty => go!"etcdserver: user name is empty"
  | .userNotFound => go!"etcdserver: user name not found"
  | .roleAlreadyExist => go!"etcdserver: role name already exists"
  | .roleNotFound => go!"etcdserver: role name not found"
  | .roleEmpty => go!"etcdserver: role name is empty"
  | .authFailed => go!"etcdserver: authentication failed, invalid user ID or password"
  | .permissionDenied => go!"etcdserver: permission denied"
  | .roleNotGranted => go!"etcdserver: role is not granted to the user"
  | .permissionNotGranted => go!"etcdserver: permission is not granted to the role"
  | .authNotEnabled => go!"etcdserver: authentication is not enabled"
  | .invalidAuthToken => go!"etcdserver: invalid auth token"
  | .authOldRevision => go!"etcdserver: revision of auth store is old"
  | .invalidAuthMgmt => go!"etcdserver: invalid auth management"
  | .clusterIdMismatch => go!"etcdserver: cluster ID mismatch"
  | .noLeader => go!"etcdserver: no leader"
  | .notLeader => go!"etcdserver: not leader"
  | .leaderChanged => go!"etcdserver: leader changed"
  | .notCapable => go!"etcdserver: not capable"
  | .stopped => go!"etcdserver: server stopped"
  | .timeout => go!"etcdserver: request timed out"
  | .timeoutDueToLeaderFail => go!"etcdserver: request timed out, possibly due to previous leader failure"
  | .timeoutDueToConnectionLost => go!"etcdserver: request timed out, possibly due to connection lost"
  | .timeoutWaitAppliedIndex => go!"etcdserver: request timed out, waiting for the applied index took too long"
  | .unhealthy => go!"etcdserver: unhealthy cluster"
  | .corrupt => go!"etcdserver: corrupt cluster"
  | .badLeaderTransferee => go!"etcdserver: bad leader transferee"
  | .clusterVersionUnavailable => go!"etcdserver: cluster version not found during downgrade"
  | .wrongDowngradeVersionFormat => go!"etcdserver: wrong downgrade target version format"
  | .invalidDowngradeTargetVersion => go!"etcdserver: invalid downgrade target version"
  | .downgradeInProcess => go!"etcdserver: cluster has a downgrade job in progress"
  | .noInflightDowngrade => go!"etcdserver: no inflight downgrade job"
  | .canceled => go!"etcdserver: request canceled"
  | .deadlineExceeded => go!"etcdserver: context deadline exceeded"
  | .notSupportedForLearner => go!"etcdserver: rpc not supported for learner"
  | .invalidClientAPIVersion => go!"etcdserver: invalid client api version"
  | .watchCanceled => go!"etcdserver: watch canceled"
  | .permissionNotGiven => go!"etcdserver: permission not given"

/-- **The gRPC code of etcd's error `e`**. -/
def code : EtcdErr → w32
  | .emptyKey => Grpc.cInvalidArgument
  | .keyNotFound => Grpc.cInvalidArgument
  | .valueProvided => Grpc.cInvalidArgument
  | .leaseProvided => Grpc.cInvalidArgument
  | .tooManyOps => Grpc.cInvalidArgument
  | .duplicateKey => Grpc.cInvalidArgument
  | .invalidSortOption => Grpc.cInvalidArgument
  | .compacted => Grpc.cOutOfRange
  | .futureRev => Grpc.cOutOfRange
  | .noSpace => Grpc.cResourceExhausted
  | .leaseNotFound => Grpc.cNotFound
  | .leaseExist => Grpc.cFailedPrecondition
  | .leaseTTLTooLarge => Grpc.cOutOfRange
  | .memberExist => Grpc.cFailedPrecondition
  | .peerURLExist => Grpc.cFailedPrecondition
  | .memberNotEnoughStarted => Grpc.cFailedPrecondition
  | .memberBadURLs => Grpc.cInvalidArgument
  | .memberNotFound => Grpc.cNotFound
  | .memberNotLearner => Grpc.cFailedPrecondition
  | .memberLearnerNotReady => Grpc.cFailedPrecondition
  | .tooManyLearners => Grpc.cFailedPrecondition
  | .requestTooLarge => Grpc.cInvalidArgument
  | .tooManyRequests => Grpc.cResourceExhausted
  | .rootUserNotExist => Grpc.cFailedPrecondition
  | .rootRoleNotExist => Grpc.cFailedPrecondition
  | .userAlreadyExist => Grpc.cFailedPrecondition
  | .userEmpty => Grpc.cInvalidArgument
  | .userNotFound => Grpc.cFailedPrecondition
  | .roleAlreadyExist => Grpc.cFailedPrecondition
  | .roleNotFound => Grpc.cFailedPrecondition
  | .roleEmpty => Grpc.cInvalidArgument
  | .authFailed => Grpc.cInvalidArgument
  | .permissionDenied => Grpc.cPermissionDenied
  | .roleNotGranted => Grpc.cFailedPrecondition
  | .permissionNotGranted => Grpc.cFailedPrecondition
  | .authNotEnabled => Grpc.cFailedPrecondition
  | .invalidAuthToken => Grpc.cUnauthenticated
  | .authOldRevision => Grpc.cInvalidArgument
  | .invalidAuthMgmt => Grpc.cInvalidArgument
  | .clusterIdMismatch => Grpc.cFailedPrecondition
  | .noLeader => Grpc.cUnavailable
  | .notLeader => Grpc.cFailedPrecondition
  | .leaderChanged => Grpc.cUnavailable
  | .notCapable => Grpc.cFailedPrecondition
  | .stopped => Grpc.cUnavailable
  | .timeout => Grpc.cUnavailable
  | .timeoutDueToLeaderFail => Grpc.cUnavailable
  | .timeoutDueToConnectionLost => Grpc.cUnavailable
  | .timeoutWaitAppliedIndex => Grpc.cUnavailable
  | .unhealthy => Grpc.cUnavailable
  | .corrupt => Grpc.cDataLoss
  | .badLeaderTransferee => Grpc.cFailedPrecondition
  | .clusterVersionUnavailable => Grpc.cFailedPrecondition
  | .wrongDowngradeVersionFormat => Grpc.cInvalidArgument
  | .invalidDowngradeTargetVersion => Grpc.cInvalidArgument
  | .downgradeInProcess => Grpc.cFailedPrecondition
  | .noInflightDowngrade => Grpc.cFailedPrecondition
  | .canceled => Grpc.cCanceled
  | .deadlineExceeded => Grpc.cDeadlineExceeded
  | .notSupportedForLearner => Grpc.cFailedPrecondition
  | .invalidClientAPIVersion => Grpc.cInvalidArgument
  | .watchCanceled => Grpc.cCanceled
  | .permissionNotGiven => Grpc.cInvalidArgument

/-- `e`'s description is a key of `errStringToError`. -/
def mapped : EtcdErr → Bool
  | .emptyKey | .keyNotFound | .valueProvided | .leaseProvided | .tooManyOps | .duplicateKey | .invalidSortOption | .compacted | .futureRev | .noSpace | .leaseNotFound | .leaseExist | .leaseTTLTooLarge | .memberExist | .peerURLExist | .memberNotEnoughStarted | .memberBadURLs | .memberNotFound | .memberNotLearner | .memberLearnerNotReady | .tooManyLearners | .requestTooLarge | .tooManyRequests | .rootUserNotExist | .rootRoleNotExist | .userAlreadyExist | .userEmpty | .userNotFound | .roleAlreadyExist | .roleNotFound | .roleEmpty | .authFailed | .permissionDenied | .roleNotGranted | .permissionNotGranted | .authNotEnabled | .invalidAuthToken | .authOldRevision | .invalidAuthMgmt | .clusterIdMismatch | .noLeader | .notLeader | .leaderChanged | .notCapable | .stopped | .timeout | .timeoutDueToLeaderFail | .timeoutDueToConnectionLost | .unhealthy | .corrupt | .badLeaderTransferee | .clusterVersionUnavailable | .wrongDowngradeVersionFormat | .invalidDowngradeTargetVersion | .downgradeInProcess | .noInflightDowngrade | .notSupportedForLearner => true
  | _ => false

section names
variable [GooseExts] [go_gctx : GoGlobalContext]

/-- The variable `ErrGRPC*` of `e`. -/
def grpcVar : EtcdErr → GoString
  | .emptyKey => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCEmptyKey
  | .keyNotFound => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCKeyNotFound
  | .valueProvided => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCValueProvided
  | .leaseProvided => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCLeaseProvided
  | .tooManyOps => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCTooManyOps
  | .duplicateKey => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCDuplicateKey
  | .invalidSortOption => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCInvalidSortOption
  | .compacted => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCCompacted
  | .futureRev => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCFutureRev
  | .noSpace => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCNoSpace
  | .leaseNotFound => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCLeaseNotFound
  | .leaseExist => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCLeaseExist
  | .leaseTTLTooLarge => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCLeaseTTLTooLarge
  | .memberExist => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCMemberExist
  | .peerURLExist => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCPeerURLExist
  | .memberNotEnoughStarted => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCMemberNotEnoughStarted
  | .memberBadURLs => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCMemberBadURLs
  | .memberNotFound => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCMemberNotFound
  | .memberNotLearner => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCMemberNotLearner
  | .memberLearnerNotReady => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCLearnerNotReady
  | .tooManyLearners => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCTooManyLearners
  | .requestTooLarge => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCRequestTooLarge
  | .tooManyRequests => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCRequestTooManyRequests
  | .rootUserNotExist => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCRootUserNotExist
  | .rootRoleNotExist => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCRootRoleNotExist
  | .userAlreadyExist => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCUserAlreadyExist
  | .userEmpty => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCUserEmpty
  | .userNotFound => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCUserNotFound
  | .roleAlreadyExist => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCRoleAlreadyExist
  | .roleNotFound => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCRoleNotFound
  | .roleEmpty => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCRoleEmpty
  | .authFailed => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCAuthFailed
  | .permissionDenied => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCPermissionDenied
  | .roleNotGranted => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCRoleNotGranted
  | .permissionNotGranted => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCPermissionNotGranted
  | .authNotEnabled => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCAuthNotEnabled
  | .invalidAuthToken => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCInvalidAuthToken
  | .authOldRevision => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCAuthOldRevision
  | .invalidAuthMgmt => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCInvalidAuthMgmt
  | .clusterIdMismatch => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCClusterIDMismatch
  | .noLeader => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCNoLeader
  | .notLeader => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCNotLeader
  | .leaderChanged => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCLeaderChanged
  | .notCapable => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCNotCapable
  | .stopped => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCStopped
  | .timeout => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCTimeout
  | .timeoutDueToLeaderFail => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCTimeoutDueToLeaderFail
  | .timeoutDueToConnectionLost => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCTimeoutDueToConnectionLost
  | .timeoutWaitAppliedIndex => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCTimeoutWaitAppliedIndex
  | .unhealthy => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCUnhealthy
  | .corrupt => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCCorrupt
  | .badLeaderTransferee => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCBadLeaderTransferee
  | .clusterVersionUnavailable => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCClusterVersionUnavailable
  | .wrongDowngradeVersionFormat => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCWrongDowngradeVersionFormat
  | .invalidDowngradeTargetVersion => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCInvalidDowngradeTargetVersion
  | .downgradeInProcess => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCDowngradeInProcess
  | .noInflightDowngrade => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCNoInflightDowngrade
  | .canceled => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCCanceled
  | .deadlineExceeded => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCDeadlineExceeded
  | .notSupportedForLearner => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCNotSupportedForLearner
  | .invalidClientAPIVersion => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCInvalidClientAPIVersion
  | .watchCanceled => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCWatchCanceled
  | .permissionNotGiven => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCPermissionNotGiven

/-- The client-side variable `Err*` of `e`, if any. -/
def clientVar : EtcdErr → Option GoString
  | .emptyKey => some go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrEmptyKey
  | .keyNotFound => some go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrKeyNotFound
  | .valueProvided => some go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrValueProvided
  | .leaseProvided => some go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrLeaseProvided
  | .tooManyOps => some go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrTooManyOps
  | .duplicateKey => some go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrDuplicateKey
  | .invalidSortOption => some go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrInvalidSortOption
  | .compacted => some go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrCompacted
  | .futureRev => some go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrFutureRev
  | .noSpace => some go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrNoSpace
  | .leaseNotFound => some go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrLeaseNotFound
  | .leaseExist => some go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrLeaseExist
  | .leaseTTLTooLarge => some go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrLeaseTTLTooLarge
  | .memberExist => some go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrMemberExist
  | .peerURLExist => some go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrPeerURLExist
  | .memberNotEnoughStarted => some go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrMemberNotEnoughStarted
  | .memberBadURLs => some go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrMemberBadURLs
  | .memberNotFound => some go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrMemberNotFound
  | .memberNotLearner => some go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrMemberNotLearner
  | .memberLearnerNotReady => some go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrMemberLearnerNotReady
  | .tooManyLearners => some go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrTooManyLearners
  | .requestTooLarge => some go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrRequestTooLarge
  | .tooManyRequests => some go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrTooManyRequests
  | .rootUserNotExist => some go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrRootUserNotExist
  | .rootRoleNotExist => some go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrRootRoleNotExist
  | .userAlreadyExist => some go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrUserAlreadyExist
  | .userEmpty => some go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrUserEmpty
  | .userNotFound => some go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrUserNotFound
  | .roleAlreadyExist => some go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrRoleAlreadyExist
  | .roleNotFound => some go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrRoleNotFound
  | .roleEmpty => some go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrRoleEmpty
  | .authFailed => some go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrAuthFailed
  | .permissionDenied => some go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrPermissionDenied
  | .roleNotGranted => some go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrRoleNotGranted
  | .permissionNotGranted => some go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrPermissionNotGranted
  | .authNotEnabled => some go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrAuthNotEnabled
  | .invalidAuthToken => some go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrInvalidAuthToken
  | .authOldRevision => some go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrAuthOldRevision
  | .invalidAuthMgmt => some go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrInvalidAuthMgmt
  | .clusterIdMismatch => some go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrClusterIDMismatch
  | .noLeader => some go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrNoLeader
  | .notLeader => some go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrNotLeader
  | .leaderChanged => some go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrLeaderChanged
  | .notCapable => some go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrNotCapable
  | .stopped => some go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrStopped
  | .timeout => some go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrTimeout
  | .timeoutDueToLeaderFail => some go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrTimeoutDueToLeaderFail
  | .timeoutDueToConnectionLost => some go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrTimeoutDueToConnectionLost
  | .timeoutWaitAppliedIndex => some go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrTimeoutWaitAppliedIndex
  | .unhealthy => some go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrUnhealthy
  | .corrupt => some go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrCorrupt
  | .badLeaderTransferee => some go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrBadLeaderTransferee
  | .clusterVersionUnavailable => some go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrClusterVersionUnavailable
  | .wrongDowngradeVersionFormat => some go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrWrongDowngradeVersionFormat
  | .invalidDowngradeTargetVersion => some go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrInvalidDowngradeTargetVersion
  | .downgradeInProcess => some go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrDowngradeInProcess
  | .noInflightDowngrade => some go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrNoInflightDowngrade
  | _ => none

end names

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- **The package's variables after initialization**: each `ErrGRPC*` holds a status error with its
code and description, each client-side `Err*` holds `errVal e` (mapped) or that status error (not
mapped), the metadata keys hold their strings; never written afterwards. -/
def init.spec : Prop :=
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes ⊢
    (□ ∀ e : EtcdErr, ∃ v : GoInterface, globalAddr (grpcVar e) ↦□ v ∗ Grpc.statusErr v (code e) (desc e) ∗
      (∀ n, ⌜clientVar e = some n⌝ -∗
        globalAddr n ↦□ (if mapped e then errVal e else v))) ∗
    globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.MetadataRequireLeaderKey ↦□ go!"hasleader" ∗
    globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.MetadataHasLeader ↦□ go!"true" ∗
    globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.MetadataClientAPIVersionKey ↦□ go!"client-api-version" ∗
    globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.TokenFieldNameGRPC ↦□ go!"token" ∗
    globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.TokenFieldNameSwagger ↦□ go!"authorization"

/-- `errVal e` is the `EtcdError` value of `e`'s code and description. -/
def errVal_fields.spec : Prop := ∀ e : EtcdErr,
  errVal e = interface.mkOk go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty
    #({ code' := code e, desc' := desc e } : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError)

end res

/-- The descriptions are distinct. -/
def desc_inj.spec : Prop := ∀ e e' : EtcdErr, desc e = desc e' → e = e'

/-- No error grpc makes itself carries one of etcd's descriptions (the boundary's assumption). -/
def desc_not_grpcMsg.spec : Prop := ∀ e : EtcdErr, ¬ Grpc.grpcMsg (desc e)

section res2
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

def errVal_errMsg.spec : Prop := ∀ e,
  ⊢ Grpc.errMsg (GF := GF) (errVal e) (desc e) ∗ Grpc.plainErr (errVal e) ∗ ⌜Grpc.cmpErr (errVal e)⌝

def errVal_not_status.spec : Prop := ∀ e c m, Grpc.statusErr (GF := GF) (errVal e) c m ⊢ False

/-- A context's error's message. -/
def ctxErr_errMsg.spec : Prop := ∀ err,
  context.isCtxErr (GF := GF) err ⊢ ∃ m, Grpc.errMsg err m ∗
    ⌜(m = go!"context canceled" ∨ m = go!"context deadline exceeded") ∧ Grpc.cmpErr err⌝ ∗
    Grpc.plainErr err ∗ (∀ c m', Grpc.statusErr err c m' -∗ False)

/-- **What an error of each kind is**: `.etcd e`: a status with `e`'s description that `Error` maps
(or `errVal e` itself); any other kind: a non-nil error whose description is no mapped one. -/
def callErr_view.spec : Prop := ∀ err k,
  callErr (GF := GF) err k ⊢
    match k with
    | .etcd e => ∃ c ok, Grpc.errView err c (desc e) ok ∗
        ⌜(c = code e ∨ c = Grpc.cUnknown) ∧ (mapped e = true ∨ err = errVal e)⌝
    | _ => ∃ c m ok, Grpc.errView err c m ok ∗ ⌜err ≠ GoInterface.nil ∧ ∀ e, mapped e = true → m ≠ desc e⌝

/-- A status with a mapped description, and `e`'s code (or `Unknown`: the two errors
`togRPCError` maps to `EtcdError`s, sent as `Unknown`), is that error. -/
def callErr_status.spec : Prop := ∀ err c e,
  Grpc.statusErr (GF := GF) err c (desc e) ∗ ⌜mapped e = true ∧ (c = code e ∨ c = Grpc.cUnknown)⌝ ⊢
    callErr err (.etcd e)

/-- etcd's descriptions are ASCII (so they arrive unchanged, `Grpc.fixUtf8_ascii`). -/
def desc_ascii.spec : Prop := ∀ (e : EtcdErr), ∀ b ∈ desc e, uint.nat b < 128

/-- No definite mapped etcd error has the code `Canceled` or `DeadlineExceeded` (the client's
`isContextError`, Kubernetes' `isCancelError`). -/
def code_not_ctx.spec : Prop := ∀ e : EtcdErr, mapped e = true → e.indefinite = false →
  code e ≠ Grpc.cCanceled ∧ code e ≠ Grpc.cDeadlineExceeded

/-- `io.EOF` (a stream's end, a `SendMsg` after the server ended) is `.other`. -/
def callErr_eof.spec : Prop := ∀ err,
  globalAddr io.EOF ↦□ err ⊢ callErr (GF := GF) err .other

/-- A status with no mapped description is `.other`. -/
def callErr_unmapped.spec : Prop := ∀ err c m,
  Grpc.statusErr (GF := GF) err c m ∗ ⌜∀ e, mapped e = true → m ≠ desc e⌝ ⊢ callErr err .other

/-- An error grpc made itself is `.other`. -/
def callErr_ownErr.spec : Prop := ∀ err, Grpc.ownErr (GF := GF) err ⊢ callErr err .other

end res2

end Rpctypes
end EtcdGrove
end Perennial
