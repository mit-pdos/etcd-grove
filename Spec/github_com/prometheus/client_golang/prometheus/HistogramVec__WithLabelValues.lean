/-
`prometheus.HistogramVec.WithLabelValues`: the trust boundary (`prometheus` is names-only). Lean-first (no Rocq counterpart); the request path
(`notes/decisions.md`, "The request path").
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply
public import Proof.github_com.prometheus.client_golang.prometheus.Labels

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI 

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- A prometheus `Observer` (a histogram's): `Observe(f)` returns (persistent). -/
def prometheus.observerSpec (o : GoInterfaceOk) : IProp GF :=
  iprop(□ (∀ f : val, {{ True }} (App (Val #(methods o.ty go!"Observe" o.v)) (Val f))
    {{ RET #(); True }}))

instance prometheus.observerSpec_persistent (o : GoInterfaceOk) :
    Persistent (prometheus.observerSpec (GF := GF) o) := by
  unfold prometheus.observerSpec; infer_instance

/-- `hv.WithLabelValues(lvs...)` returns the vector's observer for the labels (the request path's
`requestDurationSec` has two and is passed two), whose `Observe` returns (`observerSpec`).
Go panics (the vector's `GetMetricWith...` error) on a wrong label count or a value that is not
valid UTF-8: the premise `labelValuesOk`, against the vector's label names (`vecLabels`, from its
initializer's fact; D19l (iii), 2026-10-18); the values are read at any fraction and kept. -/
abbrev prometheus.HistogramVec.WithLabelValues.spec : Prop :=
  ∀ (hv : Loc) (lvs : GoSlice) (ls vs : List GoString) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.prometheus.client_golang.prometheus ∗
      ⌜prometheus.vecLabels hv ls ∧ prometheus.labelValuesOk ls vs⌝ ∗ lvs ↦*{dq} vs }}
    (App (Val (hv @!! go.GoType.PointerType github_com.prometheus.client_golang.prometheus.HistogramVec.ty @!! go!"WithLabelValues"))
      (Val #lvs))
  {{ (o : GoInterface), RET #o; ∃ oi : GoInterfaceOk, ⌜o = GoInterface.ok oi⌝ ∗
      prometheus.observerSpec oi ∗ lvs ↦*{dq} vs }}

end spec

end EtcdGrove
end Perennial
