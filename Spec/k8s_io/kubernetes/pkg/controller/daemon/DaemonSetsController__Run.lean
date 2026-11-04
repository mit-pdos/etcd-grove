/-
`(*DaemonSetsController).Run(ctx, workers)` (`daemon_controller.go:359`). Lean-first; track C
of the DaemonSet run.

**What the code does**: defers `HandleCrashWithContext(ctx)`; starts the broadcaster's logging and
its recording to the clientset's events sink, defers `Shutdown`; waits for the four stores' first
sync (`WaitForNamedCacheSyncWithContext`: on `false`, returns through the deferred shutdown of the
queues and `wg.Wait()`); for each of `workers`, `wg.Go` of `UntilWithContext(ctx, runWorker, 1s)`
and of `UntilWithContext(ctx, runNodeUpdateWorker, 1s)`; `wg.Go` of `Until(failedPodsBackoff.GC,
1m, ctx.Done())`; `<-ctx.Done()`; the deferred `ShutDown` of both queues, `wg.Wait()`.

**The spec.** With the controller and the two invariants (`dscEnv`), what only `Run` reads
(`dscRun`), and a context with one `Done` channel (`stableCtx`, track A), `Run` returns once the
context is done and gives its thread token back (`go dsc.Run(ctx, 2)`'s goroutine ends with it).
Each goroutine `wg.Go` starts gets its own token from the fork (`wp_fork_tok`); the wait group's
counter is bounded by the live goroutines (`notes/bounds-plan.md`): no bound on `workers`.
-/
module

public import Proof.k8s_io.kubernetes.pkg.controller.daemon.LifeDefs

@[expose] public section

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI apimodel informer informers cache workqueue k8s_io.kubernetes.pkg.controller.daemon

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.controller.daemon.Assumptions]
variable [ctx_sem : _root_.Perennial.context.Assumptions]
variable [cache_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- **`dsc.Run(ctx, workers)`**: see the file header. -/
abbrev DaemonSetsController.Run.spec : Prop :=
  ∀  (dsc : Loc) (c : DscComp)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config)
    (γa : ApiNames) (F : DscFams GF) (γ : S1Names)
    (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)) (ch : GoChan) (γch : ChanNames)
    (workers : w64),
  {{ dscEnv dsc c cfg γa F γ ∗ dscRun dsc c ∗ context.isContext ctx cs ∗ stableCtx ctx ch γch ∗ threadTok }}
    (App (App (Val (dsc @!! go.GoType.PointerType DaemonSetsController.ty @!! go!"Run")) (Val #(GoInterface.ok ctx))) (Val #workers))
  {{ RET #(); threadTok }}

end spec

end dsctl
end EtcdGrove
end Perennial
