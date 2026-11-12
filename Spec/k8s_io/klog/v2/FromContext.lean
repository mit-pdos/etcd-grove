/-
`klog.FromContext(ctx)` (`k8s.io/klog/v2`, names-only): the context's logger, or klog's global one.
**A named hypothesis** (phase 4 of `notes/k8s-daemonset-plan.md`, fifth round): outside client-go,
no axiom this round; `?` in `etc/link-lean-first-k8scache.txt`. The reflector's functions call it
for their logs.
-/
module

public import Proof.k8s_io.klog.v2.Init

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.klog.v2.Assumptions]

/-- `klog.FromContext(ctx)` of a non-`nil` context (`nil` panics in `ctx.Value`): some logger. -/
abbrev klog.FromContext.spec : Prop :=
  ∀ (ctx : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.klog.v2 ∗ ⌜ctx ≠ interface.nil⌝ }}
    (App (Val (@! k8s_io.klog.v2.FromContext)) (Val #ctx))
  {{ (l : github_com.go_logr.logr.Logger), RET #l; True }}

end spec

end EtcdGrove
end Perennial
