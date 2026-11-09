/-
`metrics.RecordEtcdRequest(verb, gr, err, startTime)` (names-only): a no-op for the store's
results, its labels valid UTF-8 (stage 7e-2, R1, a trust-base repair: once the apiserver
registers the metrics, a label that is not valid UTF-8 panics in `WithLabelValues`;
`nonissues/k8s-apiserver-metrics-negative-or-non-utf8-panic.md`). The trust boundary: an axiom, `Proof/k8s_io/apiserver/pkg/storage/etcd3/metrics/RecordEtcdRequest.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base
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
abbrev metrics.RecordEtcdRequest.spec : Prop :=
  ∀ (verb : GoString) (gr : k8s_io.apimachinery.pkg.runtime.schema.GroupResource)
    (err : GoInterface) (start : time.Time),
  utf8Valid verb → utf8Valid gr.Group' → utf8Valid gr.Resource' →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3.metrics }}
    (App (App (App (App (Val (@! k8s_io.apiserver.pkg.storage.etcd3.metrics.RecordEtcdRequest))
      (Val #verb)) (Val #gr)) (Val #err)) (Val #start))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
