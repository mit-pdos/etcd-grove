/-
`typedSharedIndexInformer[T].HasSynced`, promoted from the embedded `SharedIndexInformer`: **a
named hypothesis, gap C2** (`notes/k8s-daemonset-goose.md`): `Code/k8s_io/client_go/tools/cache.toml`
excludes the generic struct's promoted methods (the pinned Goose's pointer-receiver unfolding
once named the generic struct without its type argument). The hypothesis is that they unfold
to the forward through the embedded field, as the pinned Goose emits for `workqueue`'s
`rateLimitingType` since the C2 fix (`Code/k8s_io/client_go/util/workqueue.lean`,
`rateLimitingType.TypeAssumptions.Add_unfold`/`ptr_Add_unfold`, the same shape). Dropping the
exclusions from the `.toml` and re-translating (the coordinator's) turns it into the generated
instances. Lean-first; the DaemonSet run's track A.
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


/-- **`typedSharedIndexInformer[T].HasSynced` forwards to the embedded informer** (gap C2). -/
abbrev typedSharedIndexInformer.HasSynced_body.spec : Prop :=
  ∀ T : go.GoType,
  MethodUnfold (typedSharedIndexInformer.ty T) go!"HasSynced" (LamV "$r"
    (App (Val (GoInstruction (MethodResolve SharedIndexInformer.ty go!"HasSynced")))
      (App (Val (GoInstruction (StructFieldGet (typedSharedIndexInformer.ty T) go!"SharedIndexInformer")))
        (Var "$r")))) ∧
  MethodUnfold (go.GoType.PointerType (typedSharedIndexInformer.ty T)) go!"HasSynced" (LamV "$r"
    (App (Val (GoInstruction (MethodResolve SharedIndexInformer.ty go!"HasSynced")))
      (App (Val (GoInstruction (GoLoad SharedIndexInformer.ty)))
        (App (Val (GoInstruction (StructFieldRef (typedSharedIndexInformer.ty T)
          go!"SharedIndexInformer"))) (Var "$r")))))

end spec

end cache
end EtcdGrove
end Perennial
