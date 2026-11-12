/-
`(*ListPager).ListWithAlloc(ctx, options)` (`pager.go:88`): `p.list(ctx, options, true)`. Lean-first;
phase 4 of `notes/k8s-daemonset-plan.md`, fifth round. Stated as `list`.
-/
module

public import Proof.k8s_io.client_go.tools.pager.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace pager

open Iris Iris.BI apimodel cache k8s_io.client_go.tools.pager

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.pager.Assumptions]

/-- **`p.ListWithAlloc(context.Background(), options)`**: the page function's result. -/
abbrev ListPager.ListWithAlloc.spec : Prop :=
  ∀ (p : Loc) (pg : ListPager) (opts : k8s_io.apimachinery.pkg.apis.«meta».v1.ListOptions)
    (res : Res) (S : Loc → List Obj → GoString → IProp GF),
  opts.TimeoutSeconds' = null → opts.SendInitialEvents' = null →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.pager ∗ p ↦ pg ∗
      pfnOk pg.PageFn' res S }}
    (App (App (Val (p @!! go.GoType.PointerType ListPager.ty @!! go!"ListWithAlloc"))
      (Val #(interface.ok context.backgroundCtxVal))) (Val #opts))
  {{ (obj : GoInterface) (pag : Bool) (err : GoInterface), RET (PairV (PairV #obj #pag) #err);
      p ↦ pg ∗ pageRes res S obj err }}

end spec

end pager
end EtcdGrove
end Perennial
