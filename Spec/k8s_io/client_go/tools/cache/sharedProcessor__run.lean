/-
`(*sharedProcessor).run(ctx)` (`shared_informer.go`): under the write lock, each listener's
`watchSynced`, `run` and `pop` started, `listenersStarted` set (waking `distribute`); then, once
`ctx` is done, every listener's `addCh` closed, the map cleared, and the goroutines joined.
Returns. **A first cut** (Stage 3; the lock's resource holds the not-yet-started listeners'
`lstnGoPre`). Lean-first; the DaemonSet run's track A.
-/
module

public import Spec.k8s_io.client_go.tools.cache.sharedProcessor__addListener

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI apimodel cache informer k8s_io.client_go.tools.cache

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]
variable [ctx_sem : _root_.Perennial.context.Assumptions]

/-- **`p.run(ctx)`**: see the file header. -/
abbrev sharedProcessor.run.spec : Prop :=
  ∀ [ReceiptBoundLe GF (2 ^ 61)] (p : Loc) (γp : ProcNames) (ctx : GoInterfaceOk)
    (cs : context.ContextDesc (IProp GF)) (ch : GoChan) (γch : ChanNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ isProc p ∗ sync.isRWMutexGuard (structFieldRef sharedProcessor go!"listenersLock" p) (procP p γp) ∗
      context.isContext ctx cs ∗ stableCtx ctx ch γch }}
    (App (Val (p @!! go.GoType.PointerType sharedProcessor.ty @!! go!"run"))
      (Val #(GoInterface.ok ctx)))
  {{ RET #(); True }}

end spec

end cache
end EtcdGrove
end Perennial
