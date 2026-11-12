/-
**component-helpers' `scheduling/corev1` taint helpers: their predicates** (phase 5 of
`notes/k8s-daemonset-plan.md`). Lean-first (no Rocq counterpart).

* `taintFilterOk f P`: the Go closure `f` (a `taintsFilterFunc`) is a pure filter `P` on the taint
  it is passed by address (`getFilteredTaints`' `inclusionFilter`).
-/
module

public import Proof.k8s_io.kubernetes.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A taint filter** (persistent): `f` is not `nil`, and called on the address of a taint it
returns `P` of the taint and keeps it. -/
def taintFilterOk (f : GoFunc) (P : k8s_io.api.core.v1.Taint → Bool) : IProp GF :=
  iprop(⌜f ≠ func.nil⌝ ∗ ∀ (p : Loc) (tv : k8s_io.api.core.v1.Taint),
    {{ p ↦ tv }} (App (Val #f) (Val #p)) {{ RET #(P tv); p ↦ tv }})

instance taintFilterOk_persistent (f : GoFunc) (P : k8s_io.api.core.v1.Taint → Bool) :
    Persistent (taintFilterOk (GF := GF) f P) := by
  unfold taintFilterOk; infer_instance

end defs

end dsctl
end EtcdGrove
end Perennial
