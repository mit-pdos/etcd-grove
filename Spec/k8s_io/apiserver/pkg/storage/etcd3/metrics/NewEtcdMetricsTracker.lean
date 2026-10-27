/-
`metrics.NewEtcdMetricsTracker(groupResource)` (the store's metrics, names-only): a new tracker
whose `Get` field, read-only, holds a latency tracker (non-nil); `isStore`'s `c.mt`, `c.lt`. The trust boundary: an axiom, `Proof/k8s_io/apiserver/pkg/storage/etcd3/metrics/NewEtcdMetricsTracker.lean`. Lean-first (no Rocq
counterpart).
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
abbrev metrics.NewEtcdMetricsTracker.spec : Prop :=
  ∀ (gr : k8s_io.apimachinery.pkg.runtime.schema.GroupResource),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3.metrics }}
    (App (Val (@! k8s_io.apiserver.pkg.storage.etcd3.metrics.NewEtcdMetricsTracker)) (Val #gr))
  {{ (mt lt : Loc), RET #mt;
      structFieldRef k8s_io.apiserver.pkg.storage.etcd3.metrics.EtcdMetricsTracker go!"Get" mt ↦□
        lt ∗ ⌜lt ≠ null⌝ }}

end spec

end EtcdGrove
end Perennial
