/-
`pager.New(fn)` (`pager.go:61`): a pager over the page function `fn`, with the default page size
(500), full list on an expired continue (`FullListIfExpired`), and buffer size (10). Lean-first;
phase 4 of `notes/k8s-daemonset-plan.md`, fifth round.
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.pager.Assumptions]

/-- **`pager.New(fn)`**: a fresh pager over `fn`. -/
abbrev New.spec : Prop :=
  ∀ (fn : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.pager }}
    (App (Val (@! k8s_io.client_go.tools.pager.New)) (Val #fn))
  {{ (p : Loc), RET #p; p ↦ ListPager.mk (W64 500) fn true (W32 10) }}

end spec

end pager
end EtcdGrove
end Perennial
