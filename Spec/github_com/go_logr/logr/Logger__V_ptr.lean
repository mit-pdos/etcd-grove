/-
`(*logr.Logger).V(level)` (`github.com/go-logr/logr`, names-only): `V` called through a pointer to
a logger variable (Goose calls a value method of an addressable variable through the pointer's
method set).
**A named hypothesis** (phase 4 of `notes/k8s-daemonset-plan.md`, fifth round): outside client-go,
no axiom this round; `?` in `etc/link-lean-first-k8scache.txt`.
-/
module

public import Proof.github_com.go_logr.logr.Init

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
variable [package_sem : github_com.go_logr.logr.Assumptions]

/-- `(&l).V(level)`: some logger; the variable unchanged. -/
abbrev logr.Logger.V_ptr.spec : Prop :=
  ∀ (p : Loc) (l : github_com.go_logr.logr.Logger) (dq : DFrac) (level : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.go_logr.logr ∗ p ↦{dq} l }}
    (App (Val (p @!! go.GoType.PointerType github_com.go_logr.logr.Logger.ty @!! go!"V"))
      (Val #level))
  {{ (l' : github_com.go_logr.logr.Logger), RET #l'; p ↦{dq} l }}

end spec

end EtcdGrove
end Perennial
