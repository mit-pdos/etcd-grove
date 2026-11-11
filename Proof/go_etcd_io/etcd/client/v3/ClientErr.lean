/-
`clientErr`: what an error etcd's client returns is, as Go's `errors.As` needs it (moved from
`cache/v3/InvEtcdTxnOwn.lean` in unit C1, 2026-10-14, so that `rpctypes.Error`'s spec, which
imports less, can state that it keeps it). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Perennial.Proof.errors
public import Code.go_etcd_io.etcd.api.v3.v3rpc.rpctypes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.etcd.api.v3

section clientErr
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- **The dynamic types of the errors etcd's client returns** (k8s 7e-1, 2026-11-10, approved by
etcd-grove-81): a gRPC status error (`*status.Error`, grpc's `internal/status`: `toRPCErr`,
`status.Error`, `status.FromContextError`), an `rpctypes.EtcdError` (`rpctypes.Error`), an
`*errors.errorString` (`io.EOF`, `context.Canceled`) and `context.deadlineExceededError`
(`context.DeadlineExceeded`). Checked, for the errors `kubernetes.Client` returns (after
`ContextError` and `rpctypes.Error` have converted the attempt's error), by `examples/k8s/etcd3`'s
`TestClientErrorTypes` (gates 9c: partitions, deadlines, a closed client); the attempt-level types
`grpcInvokerOk` states rest on the attack programs of `examples/k8s7e1attack` (`InvGrpc.lean`). True of
grpc-go v1.84 under etcd's configuration only: a per-RPC credentials error carrying a status (or
wrapping one with `%w`), and a service-config retry policy's `"max retries exhausted"` error, are of
other types; `perRPCCredsOk` requires credentials that return no error, and `grpcResolverAt` a
service config without a retry policy (`notes/k8s-etcd3-plan.md`, "Soundness finding in the trust
base"). -/
def clientErrTys : List go.GoType :=
  [go.GoType.PointerType google_golang_org.grpc.internal.status.Error.ty,
   v3rpc.rpctypes.EtcdError.ty,
   go.GoType.PointerType _root_.Perennial.errors.errorString.ty,
   _root_.Perennial.context.deadlineExceededError.ty]

/-- **An error etcd's client returns** (a gRPC status error, an `rpctypes.EtcdError`, a context
error): a leaf of an error tree, without `Unwrap` or `As` methods (`errors.isLeafError`), whose
dynamic type is one of `clientErrTys` (since k8s 7e-1), whose
value, if its dynamic type is `rpctypes.EtcdError`, is an `EtcdError` (Go's typing, which the model
lacks: `errors.AsTypeTyped`); and `rpctypes.EtcdError` implements `error` (its method set has
`Error() string`, `func (e EtcdError) Error() string`: `errors.AsTarget`, a method-set fact, which
the model also lacks, since method sets are uninterpreted). What `errors.As(err, &serverErr)`
needs (`leasingKV.acquire`, `errors.wp_As`: Go's `As` panics for a target whose element type is
neither an interface nor implements `error`). -/
def clientErr (err : GoInterface) : Prop :=
  errors.AsTarget v3rpc.rpctypes.EtcdError.ty ∧
  ∀ ii, err = GoInterface.ok ii → errors.isLeafError ii ∧
    errors.AsTypeTyped v3rpc.rpctypes.EtcdError v3rpc.rpctypes.EtcdError.ty ii ∧
    ii.ty ∈ clientErrTys

end clientErr

end EtcdGrove
end Perennial
