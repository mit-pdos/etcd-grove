/-
# The server's error values (batch 2c), vocabulary

The errors etcd's server returns to its callers (the gRPC handlers, the internal requesters):
`etcdserver/errors`' sentinels (`ErrTimeout`, `ErrStopped`, ...), `mvcc`'s, `lease`'s, `auth`'s,
`membership`'s, which 2a's `togRPCError` maps to rpctypes' (`toGRPCErrorMap`); the context's own
errors, which it passes through; and the unmapped ones (raft's `ErrStopped`,
`ErrProposalDropped`, `lease.ErrNotPrimary`, bcrypt's, protobuf's), which become a gRPC `Unknown`
with their message. Namespace `EtcdServer`.

## Vocabulary

* `srvErrOf err e` (pure, opaque): `err` is a server error value that `toGRPCErrorMap` maps to
  rpctypes' `e`. Never a context's own error (`srvErrOf_notCtx`).
* `srvErrVal e` (pure, opaque): **the** server sentinel of `e` (one per mapped `e`, `srvErrMapped`;
  `.memberNotFound` has two, `ErrIDRemoved` and `ErrIDNotFound`, of which `srvErrVal` is one).
  That each package variable holds its `srvErrVal` is a law of the package's initialization (its
  owner's: 3c `lease`, 3d `auth`, 3e `mvcc`, 2e `membership`, and `etcdserver/errors`: requested,
  `req/`).
* `srvErrLeaf err` (pure, opaque): `err` is an `errors.New` leaf (a `*errors.errorString`, no
  `Unwrap`, `Is` or `As` method): Perennial's `errors.wp_Is_leaf` applies, so `errors.Is(err, t)`
  is `err == t` for a sentinel `t`.
* `srvErrNotMapped err` (pure, opaque): `errors.Is(err, srvErrVal e)` is false for every mapped `e`
  (an unmapped error wraps no sentinel).
* `raftStoppedErr` (opaque): raft's `ErrStopped` (unmapped; R1's package variable, requested).
* `srvErrShape err` (transparent): what every error a server spec returns carries, for 2a's
  `togRPCError` (its precondition) and the callers' `errors.Is`: a context's error, or not one and
  either mapped (and a leaf) or unmapped with a message (`Grpc.errMsg`) and no sentinel inside.
* `srvIndef err`, `srvUnfired err` (pure, transparent): the error classes of the request path's
  outcomes 3 and 2 (`ApiReq.lean`).

## Laws

`srvErrOf_ne_nil`, `srvErrOf_fun`, `srvErrOf_val`, `srvErrOf_inj`, `srvErrVal_leaf`,
`srvErrOf_notCtx`, `raftStoppedErr_unmapped`, `raftStoppedErr_shape`.
-/
module

public import Spec.go_etcd_io.etcd.api.v3.Model
public import Spec.google_golang_org.grpc.Api

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

/-- **`err` is a server error value that `togRPCError` maps to rpctypes' `e`.** -/
opaque srvErrOf (err : GoInterface) (e : EtcdErr) : Prop

/-- **The server sentinel of `e`.** -/
opaque srvErrVal (e : EtcdErr) : GoInterface

/-- **`err` is an `errors.New` leaf error** (`errors.Is(err, t)` is `err == t` for a sentinel). -/
opaque srvErrLeaf (err : GoInterface) : Prop

/-- **`err` wraps no mapped sentinel** (`errors.Is(err, srvErrVal e)` is false for every `e`). -/
opaque srvErrNotMapped (err : GoInterface) : Prop

/-- raft's `ErrStopped`. -/
opaque raftStoppedErr : GoInterface

/-- **An error after which the request may still take effect** (outcome 3): not `nil`, and of an
indefinite kind if `togRPCError` maps it. -/
def srvIndef (err : GoInterface) : Prop :=
  err ≠ GoInterface.nil ∧ ∀ e, srvErrOf err e → e.indefinite = true

/-- **An error of a request that never takes effect** (outcome 2): not `nil`, a refusal or an
indefinite kind if mapped. -/
def srvUnfired (err : GoInterface) : Prop :=
  err ≠ GoInterface.nil ∧ ∀ e, srvErrOf err e → e.refusal = true ∨ e.indefinite = true

def srvErrOf_ne_nil.spec : Prop := ∀ err e, srvErrOf err e → err ≠ GoInterface.nil

/-- An error value maps to one `EtcdErr` (`toGRPCErrorMap` is a map). -/
def srvErrOf_fun.spec : Prop := ∀ err e e', srvErrOf err e → srvErrOf err e' → e = e'

/-- The sentinel of a mapped `e` maps to it. -/
def srvErrOf_val.spec : Prop := ∀ e, srvErrMapped e = true → srvErrOf (srvErrVal e) e

/-- One value per `EtcdErr` (but `.memberNotFound`'s two). -/
def srvErrOf_inj.spec : Prop := ∀ err e, e ≠ .memberNotFound → srvErrOf err e → err = srvErrVal e

/-- The mapped values are leaves. -/
def srvErrVal_leaf.spec : Prop := ∀ err e, srvErrOf err e → srvErrLeaf err

/-- raft's `ErrStopped` is unmapped and wraps nothing. -/
def raftStoppedErr_unmapped.spec : Prop :=
  (∀ e, ¬ srvErrOf raftStoppedErr e) ∧ srvErrNotMapped raftStoppedErr

end errs

section shape
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- **What a returned server error carries** (see the header): `togRPCError`'s precondition. -/
def srvErrShape (err : GoInterface) : IProp GF :=
  iprop(context.isCtxErr err ∨
    ((context.isCtxErr err -∗ False) ∗
      ((⌜(∃ e, srvErrOf err e) ∧ srvErrLeaf err⌝) ∨
       (∃ m, Grpc.errMsg err m ∗ ⌜(∀ e, ¬ srvErrOf err e) ∧ srvErrNotMapped err⌝))))

/-- A context's error is never a mapped server error (`togRPCError` passes those through). -/
def srvErrOf_notCtx.spec : Prop := ∀ err,
  context.isCtxErr (GF := GF) err ⊢ ⌜∀ e, ¬ srvErrOf err e⌝

/-- raft's `ErrStopped`'s shape (its message). -/
def raftStoppedErr_shape.spec : Prop := ⊢ srvErrShape (GF := GF) raftStoppedErr

/-- A mapped sentinel's shape. -/
def srvErrVal_shape.spec : Prop := ∀ e, srvErrMapped e = true → ⊢ srvErrShape (GF := GF) (srvErrVal e)

end shape

end EtcdServer
end EtcdGrove
end Perennial
