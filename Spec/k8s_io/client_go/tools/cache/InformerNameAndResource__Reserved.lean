/-
`InformerNameAndResource.Reserved()` (`identity.go:187`): whether the informer name is reserved
(`false` for the zero identity, whose `reserved` is `nil`). Lean-first.
-/
module

public import Proof.k8s_io.client_go.tools.cache.TSDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI k8s_io.client_go.tools.cache

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- `n.Reserved()` for an identity without a reservation (`reserved` `nil`, as the zero one's):
`false`. (A reserved identity's case, an `atomic.Bool` load, is not specified.) -/
abbrev InformerNameAndResource.Reserved.spec : Prop :=
  ∀ (n : InformerNameAndResource),
  {{ (⌜n.reserved' = null⌝ : IProp GF) }}
    (App (Val (n @!! InformerNameAndResource.ty @!! go!"Reserved")) (Val #()))
  {{ RET #false; True }}

end spec

end cache
end EtcdGrove
end Perennial
