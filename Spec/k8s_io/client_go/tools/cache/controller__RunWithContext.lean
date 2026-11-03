/-
`(*controller).RunWithContext(ctx)` (`controller.go`): a goroutine closing the queue once `ctx` is
done; the reflector (`NewReflectorWithOptions` over the config's list-watch, object type and
queue) run on a `wait.Group` goroutine; `processLoop` every second until `ctx` is done
(`wait.UntilWithContext`); the group joined. Its precondition: `processLoop`'s, the reflector's
environment (the informer invariant, the list-watch, good keys) and the invariant's half of the
reflector's last version (none yet) with a past state. Returns. Lean-first; the DaemonSet run's
track A.
-/
module

public import Spec.k8s_io.client_go.tools.cache.controller__processLoop
public import Spec.k8s_io.client_go.tools.cache.NewReflectorWithOptions

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

/-- **`c.RunWithContext(ctx)`**: see the file header. -/
abbrev controller.RunWithContext.spec : Prop :=
  ∀ (c : Loc) (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)) (dch : GoChan)
    (γd : ChanNames) (f : Loc) (lw : GoInterfaceOk) (q : Loc) (γa : ApiNames)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config) (res : Res)
    (γf : FifoNames) (γt : TsNames) (γi : InfNames) (pf pbf : GoFunc)
    (Ψ : List FD → Bool → IProp GF) (Ψ' : List FD → GoInterface → IProp GF) (I : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ ⌜rvuTyOk ∧ bmTyOk⌝ ∗
      context.isContext ctx cs ∗ stableCtx ctx dch γd ∗
      (c.[controller, go!"config"]).[Config, go!"Queue"] ↦□
        interface.mkOk (go.GoType.PointerType RealFIFO.ty) #f ∗
      (c.[controller, go!"config"]).[Config, go!"ListerWatcher"] ↦□ (GoInterface.ok lw : ListerWatcher) ∗
      (c.[controller, go!"config"]).[Config, go!"ObjectType"] ↦□
        (interface.mkOk (go.GoType.PointerType (resObjTy res)) #q :
          k8s_io.apimachinery.pkg.runtime.Object) ∗
      (c.[controller, go!"config"]).[Config, go!"FullResyncPeriod"] ↦□ (W64 0 : time.Duration) ∗
      (c.[controller, go!"config"]).[Config, go!"Process"] ↦□ pf ∗
      (c.[controller, go!"config"]).[Config, go!"ProcessBatch"] ↦□ pbf ∗
      infInv γa res γf γt γi ∗ isFIFO f γf (infObj γi res) ∗ lwOk lw γa cfg res ∗ keysOk γa ∗
      reflLast γi none ∗ (∃ σ0 : apimodel.St, pastSt γa σ0) ∗
      □ processOk (infObj γi res) pf (fun d b => Ψ [d] b) (fun d e => Ψ' [d] e) ∗
      □ processBatchOk (infObj γi res) pbf Ψ Ψ' ∗ gateOk ∗ errIsOk ∗ I ∗
      □ (I -∗ popAU γf (fun d b => Ψ [d] b) (popDone I) ∗ doneAU γf (fun d e => Ψ' [d] e) (popDone I)) ∗
      □ (I -∗ popBatchAU γf Ψ (popBatchDone I) ∗ doneBatchAU γf Ψ' (popBatchDone I)) }}
    (App (Val (c @!! go.GoType.PointerType controller.ty @!! go!"RunWithContext"))
      (Val #(GoInterface.ok ctx)))
  {{ RET #(); True }}

end spec

end cache
end EtcdGrove
end Perennial
