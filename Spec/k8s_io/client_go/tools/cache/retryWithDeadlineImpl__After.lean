/-
`(*retryWithDeadlineImpl).After(err)` (`retry_with_deadline.go:55`): records a retryable error's
time. **A named hypothesis, a gap**: its `r.firstErrorTime.IsZero()` calls `(*time.Time).IsZero`,
which Perennial's `time` translation at the pin lacks (no `IsZero` method), so the call does not
step; `?` in `etc/link-lean-first-k8scache.txt` (`notes/perennial-changes.md`). Phase 4 of
`notes/k8s-daemonset-plan.md`, fifth round. Stated as what the code does to the watch's retry state:
it stays a retry state of the same clock and predicate (`retryOwn`; only the two times change).
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

/-- **`rt.After(err)`**: the retry state stays one. -/
abbrev retryWithDeadlineImpl.After.spec : Prop :=
  ∀ (l : Loc) (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗
      retryOwn (interface.mkOk (go.GoType.PointerType retryWithDeadlineImpl.ty) #l) }}
    (App (Val (l @!! go.GoType.PointerType retryWithDeadlineImpl.ty @!! go!"After")) (Val #err))
  {{ RET #(); retryOwn (interface.mkOk (go.GoType.PointerType retryWithDeadlineImpl.ty) #l) }}

end spec

end cache
end EtcdGrove
end Perennial
