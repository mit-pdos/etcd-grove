/-
`metrics.RecordEtcdRequest(verb, gr, err, startTime)` (names-only): a no-op for the store's
results, for an error grpc's `status` accepts (`statusErrOk`: `nil`, or a leaf whose `Error()`,
`GRPCStatus()` and `Is` return). The trust boundary: an axiom,
`Proof/k8s_io/apiserver/pkg/storage/etcd3/metrics/RecordEtcdRequest.lean`. Lean-first (no Rocq
counterpart).

(Premise fixes 3, 2026-11-10, decided by etcd-grove-81: the precondition `statusErrOk err`; it
returned for every `err`.) For a non-nil `err`, Go's `RecordEtcdRequest` (`metrics.go:217-223` at
the apiserver pin `9c4ec15b8038`) computes `errorReason(err)` (`metrics.go:225-243`) whether the
metrics are registered or not, which calls `errors.Is`, `errors.As` and grpc's `status.FromError`
on it: `FromError` calls the error's `GRPCStatus()`, which for a typed-nil `*status.Error`
dereferences nil and panics (`examples/premisefix/recordetcdrequest`). The store's errors have it:
the client's (`Client.Get`'s, `OptimisticPut`'s, `OptimisticDelete`'s error branch) and
`txnError`'s (`ErrTransactionConflict`, an `errors.New` leaf).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- See the file header. -/
abbrev metrics.RecordEtcdRequest.spec : Prop :=
  ∀ (verb : GoString) (gr : k8s_io.apimachinery.pkg.runtime.schema.GroupResource)
    (err : GoInterface) (start : time.Time),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3.metrics ∗
      go_etcd_io.etcd.cache.v3.statusErrOk err }}
    (App (App (App (App (Val (@! k8s_io.apiserver.pkg.storage.etcd3.metrics.RecordEtcdRequest))
      (Val #verb)) (Val #gr)) (Val #err)) (Val #start))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
