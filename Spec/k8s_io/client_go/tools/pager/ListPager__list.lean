/-
`(*ListPager).list(ctx, options, allocNew)` (`pager.go:92`): list in pages of `PageSize` (the
options' `Limit` if set), following continue tokens, falling back to a full list if a continue
token expires. Lean-first; phase 4 of `notes/k8s-daemonset-plan.md`, fifth round.

Stated for the reflector's call: the context `context.Background()` (its `Done()` is `nil`, so the
loop's `select` takes its default), options with no timeout or `sendInitialEvents` pointer, a page
function returning lists of the model (`pfnOk`: `typedListAt`, no continue token). So one page: the
first page's result is the pager's, an error (whether or not expired: the continue token is empty)
or the list.
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

/-- **`p.list(context.Background(), options, alloc)`**: the page function's result. -/
abbrev ListPager.list.spec : Prop :=
  ∀ (p : Loc) (pg : ListPager) (opts : k8s_io.apimachinery.pkg.apis.«meta».v1.ListOptions)
    (alloc : Bool) (res : Res) (S : Loc → List Obj → GoString → IProp GF),
  opts.TimeoutSeconds' = null → opts.SendInitialEvents' = null →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.pager ∗ p ↦ pg ∗
      pfnOk pg.PageFn' res S }}
    (App (App (App (Val (p @!! go.GoType.PointerType ListPager.ty @!! go!"list"))
      (Val #(interface.ok context.backgroundCtxVal))) (Val #opts)) (Val #alloc))
  {{ (obj : GoInterface) (pag : Bool) (err : GoInterface), RET (PairV (PairV #obj #pag) #err);
      p ↦ pg ∗ pageRes res S obj err }}

end spec

end pager
end EtcdGrove
end Perennial
