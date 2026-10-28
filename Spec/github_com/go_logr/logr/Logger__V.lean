/-
`(logr.Logger).V(level)` (`github.com/go-logr/logr`, names-only): the logger at a verbosity.
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.go_logr.logr.Assumptions]

/-- `l.V(level)`: some logger. -/
abbrev logr.Logger.V.spec : Prop :=
  ∀ (l : github_com.go_logr.logr.Logger) (level : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.go_logr.logr }}
    (App (Val (l @!! github_com.go_logr.logr.Logger.ty @!! go!"V")) (Val #level))
  {{ (l' : github_com.go_logr.logr.Logger), RET #l'; True }}

end spec

end EtcdGrove
end Perennial
