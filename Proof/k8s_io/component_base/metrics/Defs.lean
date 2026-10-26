/-
**component-base's metric vectors, as the watch cache's specs see them** (KEP-6404,
`notes/kep-6404-plan.md`; 2026-10-26). Lean-first (no Rocq counterpart).

`k8s.io/component-base/metrics` (names-only) wraps prometheus' vectors: `HistogramVec.WithContext`
returns a `*HistogramVecWithContext`, whose `WithLabelValues(lvs...)` returns an observer
(`*exemplarHistogramVec`) after the wrapped `HistogramVec.WithLabelValues`, which returns a no-op
observer for a vector not registered (`IsCreated`), replaces values not in the metric's allow
list, and otherwise calls prometheus' `WithLabelValues`: a panic unless there are as many values
as the vector has labels, each valid UTF-8 (`prometheus.labelValuesOk`, `Labels.lean` of
prometheus).

* `vecLabels v ls` (opaque, pure): `v` is a `*HistogramVec` built by
  `NewHistogramVec(opts, ls)`; only the vectors' initializers' trust-boundary axioms state it.
* `histCtxOk vc ls`: `WithLabelValues` of `vc`, with values `labelValuesOk` for `ls`, returns an
  observer whose `Observe` returns.
-/
module

public import GeneratedProof.k8s_io.component_base.metrics
public import Perennial.Proof.ProofPrelude
public import Proof.github_com.prometheus.client_golang.prometheus.Labels

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kmetrics

open Iris Iris.BI k8s_io.component_base.metrics

/-- The vector `v` has the labels `ls` (see the file header). Opaque: only the vectors'
initializers' trust-boundary axioms state it. -/
opaque vecLabels (v : Loc) (ls : List GoString) : Prop

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A vector with a context, of labels `ls`** (persistent; see the file header). -/
def histCtxOk (vc : Loc) (ls : List GoString) : IProp GF :=
  iprop(□ ∀ (sl : GoSlice) (vs : List GoString) (dq : DFrac),
    {{ ⌜prometheus.labelValuesOk ls vs⌝ ∗ sl ↦*{dq} vs }}
      (App (Val (vc @!! go.GoType.PointerType HistogramVecWithContext.ty @!! go!"WithLabelValues"))
        (Val #sl))
    {{ (o : Loc), RET #o; sl ↦*{dq} vs ∗
        □ ∀ x : w64, {{ True }}
          (App (Val (o @!! go.GoType.PointerType exemplarHistogramVec.ty @!! go!"Observe")) (Val #x))
          {{ RET #(); True }} }})

instance histCtxOk_persistent (vc : Loc) (ls : List GoString) :
    Persistent (histCtxOk (GF := GF) vc ls) := by
  unfold histCtxOk; infer_instance

end defs

end kmetrics
end EtcdGrove
end Perennial
