/-
`(*sharedIndexInformer).RunWithContext(ctx)` (`shared_informer.go`): once (a second run
returns), under `startedLock`, the FIFO (`newQueueFIFO`, over the invariant's preallocated FIFO
names `I.γf`) and the controller (the sharded list-watch, `handleDeltas`/`handleBatchDeltas` as
its processing), `started` set (with the whole callers' half of the not-started token,
`infNotStarted I.γi 1`, used up: the start lock's half flips, `nsLock_start`); then the mutation
detector, the processor and the synced-closer
on goroutines of a `wait.Group`, and the controller's loop until `ctx` is done. Returns (partial
correctness). Lean-first; the DaemonSet run's track A.
-/
module

public import Proof.k8s_io.client_go.tools.cache.SIIAt

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

/-- **`s.RunWithContext(ctx)`**: see the file header. -/
abbrev sharedIndexInformer.RunWithContext.spec : Prop :=
  ∀ (s : Loc) (γa : ApiNames) (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config) (r : Res) (I : InfH) (FamN : GoString → Fn GF) (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)) (ch : GoChan)
    (γch : ChanNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ siiAt s γa cfg r I FamN ∗ infNotStarted I.γi 1 ∗ context.isContext ctx cs ∗ stableCtx ctx ch γch }}
    (App (Val (s @!! go.GoType.PointerType sharedIndexInformer.ty @!! go!"RunWithContext")) (Val #(GoInterface.ok ctx)))
  {{ RET #(); True }}

end spec

end cache
end EtcdGrove
end Perennial
