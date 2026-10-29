/-
`ObjectName.String()` (`object-names.go:41`): the store key of a namespace and name. Lean-first.
-/
module

public import Proof.k8s_io.client_go.tools.cache.Keys

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

/-- `on.String()`: `nameKey on.Namespace on.Name` (`ns/name`, or `name`). -/
abbrev ObjectName.String.spec : Prop :=
  ∀ (on : ObjectName),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache }}
    (App (Val (on @!! ObjectName.ty @!! go!"String")) (Val #()))
  {{ RET #(nameKey on.Namespace' on.Name'); True }}

end spec

end cache
end EtcdGrove
end Perennial
