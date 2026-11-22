/-
`t.Record(err, startTime)` (the store's latency metrics, names-only): a no-op for its results,
for a tracker `NewEtcdMetricsTracker` built (`latencyTrackerOk`) and an error grpc's `status`
accepts (`statusErrOk`, as `RecordEtcdRequest`'s). The trust boundary: an axiom,
`Proof/k8s_io/apiserver/pkg/storage/etcd3/metrics/OperationLatencyTracker__Record.lean`. Lean-first
(no Rocq counterpart).

(prove-metrics, 2026-11-21: false until then, `notes/specs-only/ledger.md`.) It took any non-nil
`t` and any `err`. Go's `Record` (`metrics.go:380-386` at the apiserver pin `9c4ec15b8038`) calls
`t.latency.Observe`, a nil-interface call on a zero `OperationLatencyTracker`, and for a non-nil
`err` computes `errorReason(err)` whether the metrics are registered or not, which panics on a
typed-nil `*status.Error` (`status.FromError` calls its `GRPCStatus`): both panics in
`examples/premisefix/latencytracker`. The store's `Get` passes its tracker (`isStore`) and
`Client.Get`'s error (`statusErrOk_split`).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.metrics.Tracker

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
abbrev metrics.OperationLatencyTracker.Record.spec : Prop :=
  ∀ (t : Loc) (err : GoInterface) (start : time.Time),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3.metrics ∗
      ⌜metrics.latencyTrackerOk t⌝ ∗ go_etcd_io.etcd.cache.v3.statusErrOk err }}
    (App (App (Val (t @!! go.GoType.PointerType
      k8s_io.apiserver.pkg.storage.etcd3.metrics.OperationLatencyTracker.ty @!! go!"Record"))
      (Val #err)) (Val #start))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
