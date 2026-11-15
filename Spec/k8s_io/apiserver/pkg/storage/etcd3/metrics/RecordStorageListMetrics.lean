/-
`metrics.RecordStorageListMetrics(gr, index, numFetched, numEvald, numReturned)` (names-only): a
no-op, for non-negative counts and valid UTF-8 labels (the group, the resource and the index).

Faithful (revised after the attack, `notes/k8s-7e-2-attack.md` T16): prometheus counters, no result;
once registered (the apiserver registers them, `server/routes/metrics.go:53-60`) a negative count
panics (`counter cannot decrease in value`, `storage/metrics/metrics.go:79-84`) and so does a label
that is not valid UTF-8 (`WithLabelValues`; `nonissues/k8s-apiserver-metrics-negative-or-non-utf8-panic.md`);
unregistered (the driver), every call is a no-op. The trust boundary (stage 7e-2,
`notes/k8s-7e-2-draft.md` §5.5): an axiom, `Proof/k8s_io/apiserver/pkg/storage/etcd3/metrics/RecordStorageListMetrics.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base
public import Proof.unicode.utf8.Valid

@[expose] public section

set_option linter.unusedSectionVars false

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
abbrev metrics.RecordStorageListMetrics.spec : Prop :=
  ∀ (gr : k8s_io.apimachinery.pkg.runtime.schema.GroupResource) (idx : GoString) (a b c' : w64),
  0 ≤ sint.Z a → 0 ≤ sint.Z b → 0 ≤ sint.Z c' →
  utf8Valid gr.Group' → utf8Valid gr.Resource' → utf8Valid idx →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3.metrics }}
    (App (App (App (App (App (Val (@! k8s_io.apiserver.pkg.storage.etcd3.metrics.RecordStorageListMetrics))
      (Val #gr)) (Val #idx)) (Val #a)) (Val #b)) (Val #c'))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
