/-
`metrics.NewEtcdMetricsTracker(groupResource)` (the store's metrics, names-only), of a
group-resource whose labels are valid UTF-8: a new tracker whose `Get` field, read-only, holds a
latency tracker it built (`latencyTrackerOk`, what `OperationLatencyTracker.Record` takes);
`isStore`'s `c.mt`, `c.lt`.

(prove-metrics, 2026-11-21: false until then, `notes/specs-only/ledger.md`.) It took any
group-resource; once the metrics are registered (`metrics.Register`, which the apiserver runs),
`NewOperationLatencyTracker`'s `WithLabelValues` panics on a group or resource that is not valid
UTF-8 (`examples/premisefix/latencytracker`), as the recorders do
(`nonissues/k8s-apiserver-metrics-negative-or-non-utf8-panic.md`). The store has them
(`New`'s premises). The trust boundary: an axiom, `Proof/k8s_io/apiserver/pkg/storage/etcd3/metrics/NewEtcdMetricsTracker.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.metrics.Tracker
public import Proof.unicode.utf8.Valid

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
abbrev metrics.NewEtcdMetricsTracker.spec : Prop :=
  ∀ (gr : k8s_io.apimachinery.pkg.runtime.schema.GroupResource),
  utf8Valid gr.Group' → utf8Valid gr.Resource' →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3.metrics }}
    (App (Val (@! k8s_io.apiserver.pkg.storage.etcd3.metrics.NewEtcdMetricsTracker)) (Val #gr))
  {{ (mt lt : Loc), RET #mt;
      structFieldRef k8s_io.apiserver.pkg.storage.etcd3.metrics.EtcdMetricsTracker go!"Get" mt ↦□
        lt ∗ ⌜metrics.latencyTrackerOk lt⌝ }}

end spec

end EtcdGrove
end Perennial
