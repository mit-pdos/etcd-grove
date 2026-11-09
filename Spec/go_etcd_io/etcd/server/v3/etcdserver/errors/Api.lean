/-
# The server's error values (batch 2c), vocabulary

The errors etcd's server returns to its callers (the gRPC handlers, the internal requesters):
`etcdserver/errors`' sentinels (`ErrTimeout`, `ErrStopped`, ...), `mvcc`'s, `lease`'s, `auth`'s,
`membership`'s, which 2a's `togRPCError` maps to rpctypes' (`toGRPCErrorMap`); the context's own
errors, which it passes through; and the unmapped ones (raft's `ErrStopped`,
`ErrProposalDropped`, `lease.ErrNotPrimary`, bcrypt's, protobuf's), which become a gRPC `Unknown`
with their message. Namespace `EtcdServer`.

## Vocabulary

**Sentinels are values read from globals** (verify round, A3-provability F4, cross-cutting): a
package's `var ErrX = errors.New(...)` holds a fresh `*errors.errorString`, which no Lean constant
fixed before the run can equal. So the server's errors are named by a persistent resource, not a
pure constant: the package's initialization gives each global's value `v` with `srvErr v e`
(`sentinelAt`), and a spec whose post returns that error says `srvErr err e` (a caller compares it
with the global's value through `srvErr_inj`).

* `srvErr err e` (persistent, opaque): `err` is the value of a server sentinel that
  `toGRPCErrorMap` maps to rpctypes' `e` (`ErrStopped`'s, `mvcc.ErrCompacted`'s, ...: one global
  per mapped `e`, two for `.memberNotFound`, `ErrIDRemoved` and `ErrIDNotFound`). Never `nil`, never
  a context's own error, one `e` per value (`srvErr_fun`), one value per `e` but `.memberNotFound`
  (`srvErr_inj`), a leaf (`srvErrLeaf`). Introduced by the owners' initialization laws
  (`errors_init` here for `etcdserver/errors`; 3c `lease`, 3d `auth`, 3e `mvcc`, 2e `membership`
  for theirs: requested, `verify/repair-server-core.md`).
* `srvErrLeaf err` (pure, opaque): `err` is an `errors.New` leaf (a `*errors.errorString`, no
  `Unwrap`, `Is` or `As` method): Perennial's `errors.wp_Is_leaf` applies, so `errors.Is(err, t)`
  is `err == t` for a sentinel `t`. A fact of the value's dynamic type: pure.
* `srvErrNotMapped err` (persistent, opaque): `errors.Is(err, v)` is false for every sentinel value
  `v` (`srvErr v e`): an unmapped error wraps no sentinel.
* raft's `ErrStopped` and `ErrProposalDropped` are raft's `Raft.errIs g err` (R1's globals): unmapped
  (`raftErr_unmapped`), with their shape (`raftErr_shape`). (`raftStoppedErr`, a Lean constant, is
  gone: it had the sentinels' defect.)
* `srvErrShape err` (transparent): what every error a server spec returns carries, for 2a's
  `togRPCError` (its precondition) and the callers' `errors.Is`: a context's error, or not one and
  either a sentinel (a leaf) or unmapped with a message (`Grpc.errMsg`) that settles nothing
  (`srvMsgIndef`) and no sentinel inside; comparable either way (`Grpc.cmpErr`; integration I4, 2a's
  `srvErrOk` requests).
* `srvIndef err`, `srvUnfired err` (transparent, persistent): the error classes of the request
  path's outcomes 3 and 2 (`ApiReq.lean`).

**Removed** (verify round, second pass): the pure `srvErrOf` and the constant `srvErrVal`,
unrealizable; every user now states its errors with `srvErr`.

## Intended realization

`srvErr err e`: `∃ g ∈ globals e, isPkgInit (pkg g) ∗ globalAddr g ↦□ err`, with the whole
program's initialization's distinctness facts (each `errors.New` allocates a fresh cell while the
earlier sentinels' cells are allocated, `↦□` kept: the values pairwise distinct, and distinct from
raft's and `context`'s).

## Laws

`srvErr_persistent`, `srvErrNotMapped_persistent`, `srvErr_ne_nil`, `srvErr_fun`, `srvErr_inj`,
`srvErr_leaf`, `srvErr_notCtx`, `srvErr_shape`, `raftErr_unmapped`, `raftErr_shape`, `authErr_srv`,
`leaseErr_srv`, `mvccErr_srv`, `srvErr_rangeCtx`, `bcryptErr_shape` (the owners' sentinels: lease-auth's
and mvcc's requests), `errors_init`.
-/
module

public import Spec.go_etcd_io.etcd.api.v3.Model
public import Spec.google_golang_org.grpc.Api
public import Spec.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Api
public import Spec.PkgInit.go_etcd_io.etcd.server.v3.etcdserver.errors
public import Spec.go_etcd_io.raft.v3.Api
public import Spec.go_etcd_io.etcd.server.v3.auth.Api
public import Spec.go_etcd_io.etcd.server.v3.lease.Api
public import Spec.golang_org.x.crypto.bcrypt.Api
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI EtcdModel

/-- **The `EtcdErr`s `toGRPCErrorMap` has a server error for** (`api/v3rpc/util.go`). -/
def srvErrMapped : EtcdErr → Bool
  | .memberNotFound | .memberExist | .peerURLExist | .memberNotLearner | .tooManyLearners
  | .memberNotEnoughStarted | .memberLearnerNotReady
  | .compacted | .futureRev | .requestTooLarge | .noSpace | .tooManyRequests
  | .noLeader | .notLeader | .leaderChanged | .canceled | .stopped | .timeout
  | .timeoutDueToLeaderFail | .timeoutDueToConnectionLost | .timeoutWaitAppliedIndex | .unhealthy
  | .keyNotFound | .corrupt | .badLeaderTransferee
  | .clusterVersionUnavailable | .wrongDowngradeVersionFormat | .invalidDowngradeTargetVersion
  | .downgradeInProcess | .noInflightDowngrade
  | .leaseNotFound | .leaseExist | .leaseTTLTooLarge
  | .rootUserNotExist | .rootRoleNotExist | .userAlreadyExist | .userEmpty | .userNotFound
  | .roleAlreadyExist | .roleNotFound | .roleEmpty | .authFailed | .permissionNotGiven
  | .permissionDenied | .roleNotGranted | .permissionNotGranted | .authNotEnabled
  | .invalidAuthToken | .invalidAuthMgmt | .authOldRevision => true
  | _ => false

section errs
variable [GooseExts] [go_gctx : GoGlobalContext]

/-- **`err` is an `errors.New` leaf error** (`errors.Is(err, t)` is `err == t` for a sentinel). -/
opaque srvErrLeaf (err : GoInterface) : Prop

end errs

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- **`err` is the value of the server sentinel that `togRPCError` maps to rpctypes' `e`.**
Persistent. -/
opaque srvErr [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (err : GoInterface) (e : EtcdErr) : IProp GF := iprop(True)

/-- **`err` wraps no sentinel** (`errors.Is(err, v)` is false for every `v` with `srvErr v e`).
Persistent. -/
opaque srvErrNotMapped [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (err : GoInterface) : IProp GF := iprop(True)

/-- **An error after which the request may still take effect** (outcome 3): not `nil`, and of an
indefinite kind if it is a sentinel. -/
def srvIndef (err : GoInterface) : IProp GF :=
  iprop(⌜err ≠ GoInterface.nil⌝ ∗ □ ∀ e, srvErr err e -∗ ⌜e.indefinite = true⌝)

/-- **An error of a request that never takes effect** (outcome 2): not `nil`, a refusal or an
indefinite kind if it is a sentinel. -/
def srvUnfired (err : GoInterface) : IProp GF :=
  iprop(⌜err ≠ GoInterface.nil⌝ ∗ □ ∀ e, srvErr err e -∗ ⌜e.refusal = true ∨ e.indefinite = true⌝)

def srvErr_persistent.spec : Prop := ∀ err e, Persistent (srvErr (GF := GF) err e)
def srvErrNotMapped_persistent.spec : Prop := ∀ err, Persistent (srvErrNotMapped (GF := GF) err)

def srvErr_ne_nil.spec : Prop := ∀ err e, srvErr (GF := GF) err e ⊢ ⌜err ≠ GoInterface.nil⌝

/-- A sentinel value maps to one `EtcdErr` (`toGRPCErrorMap` is a map; the values are distinct). -/
def srvErr_fun.spec : Prop := ∀ err e e', srvErr (GF := GF) err e ∗ srvErr err e' ⊢ ⌜e = e'⌝

/-- One value per `EtcdErr` (but `.memberNotFound`'s two). -/
def srvErr_inj.spec : Prop := ∀ err err' e, e ≠ .memberNotFound →
  srvErr (GF := GF) err e ∗ srvErr err' e ⊢ ⌜err = err'⌝

/-- The sentinels are leaves, of mapped kinds. -/
def srvErr_leaf.spec : Prop := ∀ err e,
  srvErr (GF := GF) err e ⊢ ⌜srvErrLeaf err ∧ srvErrMapped e = true⌝

/-- A context's error is never a server sentinel (`togRPCError` passes those through). -/
def srvErr_notCtx.spec : Prop := ∀ err e,
  context.isCtxErr (GF := GF) err ∗ srvErr err e ⊢ False

/-- **An unmapped error's message settles nothing**: if it is the description of an error rpctypes
maps (which a client decodes by its message), that error is an indefinite one (2a's `indefMsg`,
integration I3/I4). -/
def srvMsgIndef (m : GoString) : Prop :=
  ∀ e : EtcdErr, Rpctypes.mapped e = true → m = Rpctypes.desc e → e.indefinite = true

/-- **What a returned server error carries** (see the header): `togRPCError`'s precondition (2a's
`srvErrOk`, identified with this at integration I3): a context's error; or a comparable
(`Grpc.cmpErr`: `toGRPCErrorMap`'s lookup) non-context error, a sentinel (a leaf), or unmapped with
a message that settles nothing (`srvMsgIndef`). -/
def srvErrShape (err : GoInterface) : IProp GF :=
  iprop(context.isCtxErr err ∨
    ((context.isCtxErr err -∗ False) ∗ ⌜Grpc.cmpErr err⌝ ∗
      ((∃ e, srvErr err e ∗ ⌜srvErrLeaf err⌝) ∨
       (∃ m, Grpc.errMsg err m ∗ □ (∀ e, srvErr err e -∗ False) ∗ srvErrNotMapped err ∗
          ⌜srvMsgIndef m⌝))))

/-- A sentinel's shape. -/
def srvErr_shape.spec : Prop := ∀ err e, srvErr (GF := GF) err e ⊢ srvErrShape err

/-- **raft's `ErrStopped` and `ErrProposalDropped` are not server sentinels** (raft's own globals,
R1's `errIs`; `togRPCError` sends them as `Unknown` with their message). -/
def raftErr_unmapped.spec : Prop := ∀ (g : GoString) err e,
  (g = go_etcd_io.raft.v3.ErrStopped ∨ g = go_etcd_io.raft.v3.ErrProposalDropped) →
  Raft.errIs (GF := GF) g err ∗ srvErr err e ⊢ False

/-- **raft's `ErrStopped`'s and `ErrProposalDropped`'s shape** (unmapped; their messages, "raft:
stopped" and "raft proposal dropped", settle nothing). Verify round (A7-completeness F4.3): the
proposal error's law was missing, and `raftStoppedErr` was a constant no law tied to raft's
global. -/
def raftErr_shape.spec : Prop := ∀ (g : GoString) err,
  (g = go_etcd_io.raft.v3.ErrStopped ∨ g = go_etcd_io.raft.v3.ErrProposalDropped) →
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ Raft.errIs g err ⊢ srvErrShape err

/-- **auth's mapped sentinels are server sentinels** (lease-auth's request at the verify round: 3d
gives `Auth.errIs ae v` from its existential `init`; `errOf_srvErrVal` is gone). -/
def authErr_srv.spec : Prop := ∀ (ae : Auth.AuthErr) (e : EtcdErr) (v : GoInterface),
  ae.etcd = some e →
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ Auth.errIs ae v ⊢ srvErr v e

/-- **lease's mapped sentinels are server sentinels**; its `ErrNotPrimary` is unmapped, with its
shape (3c's `Lease.errIs`, from its existential `init`; lease-auth's request). -/
def leaseErr_srv.spec : Prop :=
  (∀ (g : GoString) (e : EtcdErr) (v : GoInterface),
    (g, e) ∈ [(go_etcd_io.etcd.server.v3.lease.ErrLeaseNotFound, EtcdErr.leaseNotFound),
              (go_etcd_io.etcd.server.v3.lease.ErrLeaseExists, EtcdErr.leaseExist),
              (go_etcd_io.etcd.server.v3.lease.ErrLeaseTTLTooLarge, EtcdErr.leaseTTLTooLarge)] →
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ Lease.errIs g v ⊢
      srvErr v e) ∧
  (∀ v : GoInterface,
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗
      Lease.errIs go_etcd_io.etcd.server.v3.lease.ErrNotPrimary v ⊢
      srvErrShape v ∗ □ (∀ e, srvErr v e -∗ False))

/-- **mvcc's mapped sentinels are server sentinels** (mvcc's second-pass request: its `init` gives
the globals' `*errorString` values with their messages, realized as `leaseErr_srv`). -/
def mvccErr_srv.spec : Prop := ∀ (g : GoString) (e : EtcdErr) (v : GoInterface),
  (g, e) ∈ [(go_etcd_io.etcd.server.v3.storage.mvcc.ErrCompacted, EtcdErr.compacted),
            (go_etcd_io.etcd.server.v3.storage.mvcc.ErrFutureRev, EtcdErr.futureRev)] →
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ globalAddr g ↦□ v ⊢
    srvErr v e

/-- **A range's context error is no server sentinel** (mvcc's `rangeCtxErr`: a wrapped context
error, whose message is not a sentinel's: from mvcc's `rangeCtxErr_fresh` with the sentinels'
`*errorString` messages that `srvErr`'s realization carries). Lets 3b's `ctxErr_not_errIs` cover
every owner's sentinels in one step. -/
def srvErr_rangeCtx.spec : Prop := ∀ (err : GoInterface) (e : EtcdErr),
  Mvcc.rangeCtxErr (GF := GF) err ∗ srvErr err e ⊢ False

/-- **bcrypt's `ErrPasswordTooLong` is unmapped** (`UserAdd`, `UserChangePassword` return it), with
its shape (its message from 3d's `Bcrypt.init`). -/
def bcryptErr_shape.spec : Prop := ∀ v : GoInterface,
  isPkgInit (PROP := IProp GF) pkg_id.golang_org.x.crypto.bcrypt ∗
    Bcrypt.errIs golang_org.x.crypto.bcrypt.ErrPasswordTooLong v ⊢
    srvErrShape v ∗ □ (∀ e, srvErr v e -∗ False)

end res

section init
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- **Global `g` holds the sentinel of `e`** (read-only): what an owner's initialization law gives
for each of its mapped error variables. -/
def sentinelAt (g : GoString) (e : EtcdErr) : IProp GF :=
  iprop(∃ v : GoInterface, globalAddr g ↦□ v ∗ srvErr v e)

/-- **`etcdserver/errors`' sentinels** (integration I4; the verify round's encoding: each global's
value, read-only, is the sentinel of its `EtcdErr`, `toGRPCErrorMap`'s keys). `ErrUnknownMethod`
and `ErrTimeoutLeaderTransfer` are unmapped (not stated: no server spec returns them to a caller
that maps them). -/
def errors_init.spec : Prop :=
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.errors ⊢
    sentinelAt go_etcd_io.etcd.server.v3.etcdserver.errors.ErrStopped .stopped ∗
    sentinelAt go_etcd_io.etcd.server.v3.etcdserver.errors.ErrCanceled .canceled ∗
    sentinelAt go_etcd_io.etcd.server.v3.etcdserver.errors.ErrTimeout .timeout ∗
    sentinelAt go_etcd_io.etcd.server.v3.etcdserver.errors.ErrTimeoutDueToLeaderFail .timeoutDueToLeaderFail ∗
    sentinelAt go_etcd_io.etcd.server.v3.etcdserver.errors.ErrTimeoutDueToConnectionLost .timeoutDueToConnectionLost ∗
    sentinelAt go_etcd_io.etcd.server.v3.etcdserver.errors.ErrTimeoutWaitAppliedIndex .timeoutWaitAppliedIndex ∗
    sentinelAt go_etcd_io.etcd.server.v3.etcdserver.errors.ErrLeaderChanged .leaderChanged ∗
    sentinelAt go_etcd_io.etcd.server.v3.etcdserver.errors.ErrNotEnoughStartedMembers .memberNotEnoughStarted ∗
    sentinelAt go_etcd_io.etcd.server.v3.etcdserver.errors.ErrLearnerNotReady .memberLearnerNotReady ∗
    sentinelAt go_etcd_io.etcd.server.v3.etcdserver.errors.ErrNoLeader .noLeader ∗
    sentinelAt go_etcd_io.etcd.server.v3.etcdserver.errors.ErrNotLeader .notLeader ∗
    sentinelAt go_etcd_io.etcd.server.v3.etcdserver.errors.ErrRequestTooLarge .requestTooLarge ∗
    sentinelAt go_etcd_io.etcd.server.v3.etcdserver.errors.ErrNoSpace .noSpace ∗
    sentinelAt go_etcd_io.etcd.server.v3.etcdserver.errors.ErrTooManyRequests .tooManyRequests ∗
    sentinelAt go_etcd_io.etcd.server.v3.etcdserver.errors.ErrUnhealthy .unhealthy ∗
    sentinelAt go_etcd_io.etcd.server.v3.etcdserver.errors.ErrCorrupt .corrupt ∗
    sentinelAt go_etcd_io.etcd.server.v3.etcdserver.errors.ErrBadLeaderTransferee .badLeaderTransferee ∗
    sentinelAt go_etcd_io.etcd.server.v3.etcdserver.errors.ErrClusterVersionUnavailable .clusterVersionUnavailable ∗
    sentinelAt go_etcd_io.etcd.server.v3.etcdserver.errors.ErrWrongDowngradeVersionFormat .wrongDowngradeVersionFormat ∗
    sentinelAt go_etcd_io.etcd.server.v3.etcdserver.errors.ErrKeyNotFound .keyNotFound

end init

end EtcdServer
end EtcdGrove
end Perennial
