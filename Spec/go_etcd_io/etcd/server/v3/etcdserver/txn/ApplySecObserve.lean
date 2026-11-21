/-
`txn.ApplySecObserve` (`metrics.go`): it records an apply's latency (the apply package calls it): no
effect here. Lean-first; the trust boundary until prove-etcdserver (2026-11-20), now proved
(`Proof/.../txn/ApplySecObserve.lean`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-- `ApplySecObserve(version, op, success, latency)` of a valid UTF-8 `version` and `op` returns: it
observes the latency in seconds on `applySec`'s histogram for the labels `version`, `op` and
`strconv.FormatBool(success)` (`metrics.go`). Prometheus panics on a label value that is not valid
UTF-8 (`WithLabelValues`, `prometheus.labelValuesOk`): the premise, since prove-etcdserver
(2026-11-20; until then the axiom took any strings, false: `notes/axiom-review/applysecobserve-utf8.md`).
The apply thread's `dispatch` passes `"v3"` and the request's operation name, a literal. -/
abbrev txn.ApplySecObserve.spec : Prop :=
  ∀ (ver op : GoString) (success : Bool) (latency : time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗
      ⌜utf8Valid ver ∧ utf8Valid op⌝ }}
    (App (App (App (App (Val (@! txn.ApplySecObserve)) (Val #ver)) (Val #op)) (Val #success))
      (Val #latency))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
