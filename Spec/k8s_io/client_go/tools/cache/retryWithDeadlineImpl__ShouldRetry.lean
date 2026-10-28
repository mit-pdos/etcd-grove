/-
`(*retryWithDeadlineImpl).ShouldRetry()` (`retry_with_deadline.go:69`): whether the first error is
within the retry deadline (resetting the state otherwise). Lean-first; phase 4 of
`notes/k8s-daemonset-plan.md`, fifth round. Some boolean; the state stays the watch's.
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

/-- **`rt.ShouldRetry()`**: some boolean. -/
abbrev retryWithDeadlineImpl.ShouldRetry.spec : Prop :=
  ∀ (l : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗
      retryOwn (interface.mkOk (go.GoType.PointerType retryWithDeadlineImpl.ty) #l) }}
    (App (Val (l @!! go.GoType.PointerType retryWithDeadlineImpl.ty @!! go!"ShouldRetry")) (Val #()))
  {{ (b : Bool), RET #b; retryOwn (interface.mkOk (go.GoType.PointerType retryWithDeadlineImpl.ty) #l) }}

end spec

end cache
end EtcdGrove
end Perennial
