/-
`(*logr.Logger).Error(err, msg, keysAndValues...)` (`github.com/go-logr/logr`, names-only): `Error`
called through a pointer to a logger variable. **A named hypothesis, boundary pending approval**
(phase 5 of `notes/k8s-daemonset-plan.md`: the pod control logs an error with it): `?` in
`etc/link-lean-first-k8sdaemon.txt`. As `Info`'s boundary, it returns and leaves the arguments'
slice; the formatting of the arguments' values is not modeled.
-/
module

public import Proof.github_com.go_logr.logr.Init

@[expose] public section

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

/-- `(&l).Error(err, msg, kvs...)`: returns, the arguments' slice and the variable back. -/
abbrev logr.Logger.Error_ptr.spec : Prop :=
  ∀ (p : Loc) (l : github_com.go_logr.logr.Logger) (dp : DFrac) (err : GoInterface)
    (msg : GoString) (kvs : GoSlice) (dq : DFrac) (xs : List GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.go_logr.logr ∗ p ↦{dp} l ∗ kvs ↦*{dq} xs }}
    (App (App (App (Val (p @!! go.GoType.PointerType github_com.go_logr.logr.Logger.ty @!! go!"Error"))
      (Val #err)) (Val #msg)) (Val #kvs))
  {{ RET #(); p ↦{dp} l ∗ kvs ↦*{dq} xs }}

end spec

end EtcdGrove
end Perennial
