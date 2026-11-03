/-
`cache.NewTypedSharedIndexInformer[T](informer)`: `&typedSharedIndexInformer[T]{informer}`, whose
methods forward to `informer`'s (gap C2's promoted methods, named hypotheses): the same informer,
runnable if `informer` is. Lean-first; the DaemonSet run's track A.
-/
module

public import Proof.k8s_io.client_go.tools.cache.InformerApi

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

/-- **`NewTypedSharedIndexInformer[T](x)`**: a wrapper of the informer `x`. -/
abbrev NewTypedSharedIndexInformer.spec : Prop :=
  ∀ (T : go.GoType) (x : GoInterface) (γa : ApiNames) (r : Res) (I : InfH) (Fam : Nat → Fn GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ isInformer x γa r I Fam }}
    (App (Val #(functions NewTypedSharedIndexInformer [T])) (Val #x))
  {{ (w : Loc), RET #(interface.mkOk (go.GoType.PointerType (typedSharedIndexInformer.ty T)) #w);
      isInformer (interface.mkOk (go.GoType.PointerType (typedSharedIndexInformer.ty T)) #w) γa r I Fam ∗
      □ (infRunOk x -∗
        infRunOk (interface.mkOk (go.GoType.PointerType (typedSharedIndexInformer.ty T)) #w)) }}

end spec

end cache
end EtcdGrove
end Perennial
