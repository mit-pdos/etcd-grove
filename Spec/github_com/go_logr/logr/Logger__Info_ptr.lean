/-
`(*logr.Logger).Info(msg, keysAndValues...)` (`github.com/go-logr/logr`, names-only): `Info` called
through a pointer to a logger variable.
**A named hypothesis** (phase 4 of `notes/k8s-daemonset-plan.md`, fifth round): outside client-go,
no axiom this round; `?` in `etc/link-lean-first-k8scache.txt`. As klog's `Verbose.Infof` boundary,
it returns and leaves the arguments' slice; the formatting of the arguments' values (their `String`
or `Error` methods) is not modeled.
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

/-- `(&l).Info(msg, kvs...)`: returns, the arguments' slice and the variable back. -/
abbrev logr.Logger.Info_ptr.spec : Prop :=
  ∀ (p : Loc) (l : github_com.go_logr.logr.Logger) (dp : DFrac) (msg : GoString) (kvs : GoSlice)
    (dq : DFrac) (xs : List GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.go_logr.logr ∗ p ↦{dp} l ∗ kvs ↦*{dq} xs }}
    (App (App (Val (p @!! go.GoType.PointerType github_com.go_logr.logr.Logger.ty @!! go!"Info"))
      (Val #msg)) (Val #kvs))
  {{ RET #(); p ↦{dp} l ∗ kvs ↦*{dq} xs }}

end spec

end EtcdGrove
end Perennial
