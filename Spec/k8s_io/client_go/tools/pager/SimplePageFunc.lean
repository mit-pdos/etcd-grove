/-
`pager.SimplePageFunc(fn)` (`pager.go:36`): the page function `func(ctx, opts) { return fn(opts) }`.
Lean-first; phase 4 of `notes/k8s-daemonset-plan.md`, fifth round.
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

/-- **`pager.SimplePageFunc(fn)`**: a page function returning what `fn` returns. -/
abbrev SimplePageFunc.spec : Prop :=
  ∀ (fn : GoFunc) (res : Res) (S : Loc → List Obj → GoString → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.pager ∗ fnOk fn res S }}
    (App (Val (@! k8s_io.client_go.tools.pager.SimplePageFunc)) (Val #fn))
  {{ (pfn : GoFunc), RET #pfn; pfnOk pfn res S }}

end spec

end pager
end EtcdGrove
end Perennial
