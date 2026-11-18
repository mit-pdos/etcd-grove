/-
`clientv3.WatchResponse.Err()` (`client/v3/watch.go`, translated for the cache). Lean-first (no
Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvOp
public import Proof.go_etcd_io.etcd.client.v3.ClientErr

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `wr.Err()`: `nil` exactly when the response has no close error, no compact revision and
is not canceled (otherwise some error: `rpctypes.Error(closeErr)`, `rpctypes.ErrCompacted`, or
for a cancellation `rpctypes.Error` of a `FailedPrecondition` status with the cancel reason, or
`rpctypes.ErrFutureRev` without one), whose `Error()` returns some string if the close
error's does (`errStrOk`). A read, on any fraction. The close error is one grpc's `status`
accepts (`statusErrOk`, unit P3a, 2026-10-14: `rpctypes.Error` calls its `Error()` and
`GRPCStatus()`; the spec had no premise, which made it false for a close error whose methods
panic). (k8s 7f-5a-P, E2, ledger 2026-11-15) The error is one grpc's `status` accepts (`statusErrOk`;
`nil` included) and a client error (`clientErr`) whenever the close error is one (or is `nil`), given
that `EtcdError` is an `errors.As` target (`clientErr`'s type-only first conjunct): `rpctypes.Error`
keeps `clientErr`, `ErrCompacted`/`ErrFutureRev` are `EtcdError` values, and a cancel reason's
`status.Error` is a `*status.Error` leaf. (k8s 7f-5a-P step 5) An `*errors.errorString` result is the
close error's own cell (`errCellOk`: `rpctypes.Error` keeps it; the other results are of other
types). (k8s 7f-5, ledger 2026-11-16) An `*errors.errorString` result is a pointer if the close error is
(`errPtrOk`). -/
abbrev WatchResponse.Err.spec : Prop :=
  ∀ (wr : Loc) (resp : go_etcd_io.etcd.client.v3.WatchResponse) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ wr ↦{dq} resp ∗
      statusErrOk resp.closeErr' }}
    (App (Val (wr @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.WatchResponse.ty @!! go!"Err")) (Val #()))
  {{ (err : GoError), RET #err; wr ↦{dq} resp ∗
      ⌜err = interface.nil ↔
        (resp.closeErr' = interface.nil ∧ resp.CompactRevision' = W64 0 ∧
          resp.Canceled' = false)⌝ ∗
      □ (errStrOk resp.closeErr' -∗ errStrOk err) ∗
      statusErrOk err ∗
      ⌜errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
        (resp.closeErr' ≠ interface.nil → clientErr resp.closeErr') → clientErr err⌝ ∗
      □ (errCellOk resp.closeErr' -∗ errCellOk err) ∗
      -- (k8s 7f-5, 2026-11-16) a pointer if an `*errors.errorString`, if the close error is
      ⌜errPtrOk resp.closeErr' → errPtrOk err⌝ }}

end spec

end EtcdGrove
end Perennial
