/-
`metrics.RecordListLatency(gr, streamed, startTime)` (names-only): a no-op, for valid UTF-8 labels
(the group and the resource; the streamed label is a literal).

Faithful (revised after the attack, `notes/k8s-7e-2-attack.md` T17): a prometheus histogram,
`Observe` takes any float; once registered a label that is not valid UTF-8 panics
(`nonissues/k8s-apiserver-metrics-negative-or-non-utf8-panic.md`); unregistered, a no-op. The trust
boundary (stage 7e-2, `notes/k8s-7e-2-draft.md` §5.5): an axiom,
`Proof/k8s_io/apiserver/pkg/storage/etcd3/metrics/RecordListLatency.lean`. Lean-first (no Rocq counterpart).
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
abbrev metrics.RecordListLatency.spec : Prop :=
  ∀ (gr : k8s_io.apimachinery.pkg.runtime.schema.GroupResource) (streamed : Bool) (start : time.Time),
  utf8Valid gr.Group' → utf8Valid gr.Resource' →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3.metrics }}
    (App (App (App (Val (@! k8s_io.apiserver.pkg.storage.etcd3.metrics.RecordListLatency))
      (Val #gr)) (Val #streamed)) (Val #start))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
