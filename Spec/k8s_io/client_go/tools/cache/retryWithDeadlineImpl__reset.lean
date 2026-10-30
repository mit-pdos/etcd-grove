/-
`(*retryWithDeadlineImpl).reset()` (`retry_with_deadline.go:50`): zeroes the two error times.
Lean-first; phase 4 of `notes/k8s-daemonset-plan.md`, fifth round.
-/
module

public import Proof.k8s_io.client_go.tools.cache.RefWatchDefs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI k8s_io.client_go.tools.cache

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- The retry state with its two error times zeroed. -/
def retryReset (v : retryWithDeadlineImpl) : retryWithDeadlineImpl :=
  { v with firstErrorTime' := zero_val time.Time, lastErrorTime' := zero_val time.Time }

/-- **`rt.reset()`**: the two error times zeroed. -/
abbrev retryWithDeadlineImpl.reset.spec : Prop :=
  ∀ (l : Loc) (v : retryWithDeadlineImpl),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ l ↦ v }}
    (App (Val (l @!! go.GoType.PointerType retryWithDeadlineImpl.ty @!! go!"reset")) (Val #()))
  {{ RET #(); l ↦ retryReset v }}

end spec

end cache
end EtcdGrove
end Perennial
