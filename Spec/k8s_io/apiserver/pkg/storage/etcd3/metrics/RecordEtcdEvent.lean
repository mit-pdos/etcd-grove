/-
`metrics.RecordEtcdEvent(gr)` (names-only; k8s 7f-5a, T5-f, reviewed and approved with D7,
`notes/k8s-7f5a-draft.md` §5): a no-op for the program's results, given the group-resource's labels
valid UTF-8 (as `RecordEtcdRequest`'s: once the apiserver registers the metrics, a label that is not
valid UTF-8 panics in `WithLabelValues`; the store has them, `storeListOk`). Go evidence:
`examples/premisefix/watcherctx/draft7f5a_test.go`, `TestRecordEtcdEventBookmarkLabels`. The etcd3
watcher's `startWatching` takes it as a callee spec. The trust boundary: an axiom,
`Proof/k8s_io/apiserver/pkg/storage/etcd3/metrics/RecordEtcdEvent.lean` (7f-5a-P step 7). Lean-first (no Rocq counterpart).
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
abbrev metrics.RecordEtcdEvent.spec : Prop :=
  ∀ (gr : k8s_io.apimachinery.pkg.runtime.schema.GroupResource),
  utf8Valid gr.Group' → utf8Valid gr.Resource' →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3.metrics }}
    (App (Val (@! k8s_io.apiserver.pkg.storage.etcd3.metrics.RecordEtcdEvent)) (Val #gr))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
