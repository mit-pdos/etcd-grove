/-
`(*sharedInformerFactory).StartWithContext(ctx)`: under the lock, unless shutting down, each
informer not yet started runs `informer.RunWithContext(ctx)` on a goroutine of the factory's
wait group (`infRunOk`, which the factory's lock holds for each informer). Lean-first; the
DaemonSet run's track A.
-/
module

public import Proof.k8s_io.client_go.informers.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace informers

open Iris Iris.BI apimodel cache informer informers

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.informers.Assumptions]
variable [cache_sem : k8s_io.client_go.tools.cache.Assumptions]
variable [ctx_sem : _root_.Perennial.context.Assumptions]

/-- **`f.StartWithContext(ctx)`**: see the file header. -/
abbrev sharedInformerFactory.StartWithContext.spec : Prop :=
  ∀ (f : Loc) (γF : FacNames) (γa : ApiNames) (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config) (Fams : Res → Nat → Fn GF) (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)) (ch : GoChan)
    (γch : ChanNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.informers ∗ isFactory f γF γa cfg Fams ∗ context.isContext ctx cs ∗ stableCtx ctx ch γch }}
    (App (Val (f @!! go.GoType.PointerType k8s_io.client_go.informers.sharedInformerFactory.ty @!! go!"StartWithContext"))
      (Val #(GoInterface.ok ctx)))
  {{ RET #(); True }}

end spec

end informers
end EtcdGrove
end Perennial
