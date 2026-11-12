/-
`channelContext.Value(key)` (`k8s.io/apimachinery/pkg/util/wait`, `wait.go:142`; translated,
premise-fixes-7, 2026-11-11): it returns `nil`. Lean-first.
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

/-- `channelContext{stopCh: sc}.Value(key)` returns `nil`, at every key. -/
abbrev wait.channelContext.Value.spec : Prop :=
  ∀ (sc : GoChan) (key : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.wait }}
    (App (Val (k8s_io.apimachinery.pkg.util.wait.channelContext.mk sc @!!
      k8s_io.apimachinery.pkg.util.wait.channelContext.ty @!! go!"Value")) (Val #key))
  {{ RET #GoInterface.nil; True }}

end spec

end EtcdGrove
end Perennial
