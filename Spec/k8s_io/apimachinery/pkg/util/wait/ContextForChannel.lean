/-
`wait.ContextForChannel(parentCh)` (`k8s.io/apimachinery/pkg/util/wait`, `wait.go:120`; translated,
2026-11-04, K4 of `notes/k8s-compactor-plan.md`: the context Kubernetes' compactor loop runs
under). It returns `channelContext{stopCh: parentCh}` as a `context.Context`: the value, whose
methods `channelContext__Done.lean` and `channelContext__Err.lean` specify. Lean-first.
-/
module

public import Proof.k8s_io.apimachinery.pkg.util.wait.Init

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

/-- `ContextForChannel(sc)` is the context `channelContext{stopCh: sc}`. -/
abbrev wait.ContextForChannel.spec : Prop :=
  ∀ (sc : GoChan),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.wait }}
    (App (Val (@! k8s_io.apimachinery.pkg.util.wait.ContextForChannel)) (Val #sc))
  {{ RET #(interface.mkOk k8s_io.apimachinery.pkg.util.wait.channelContext.ty
      #(k8s_io.apimachinery.pkg.util.wait.channelContext.mk sc) : GoInterface); True }}

end spec

end EtcdGrove
end Perennial
