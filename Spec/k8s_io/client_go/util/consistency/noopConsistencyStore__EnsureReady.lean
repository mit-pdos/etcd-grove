/-
`(*noopConsistencyStore).EnsureReady` (`consistency.go:241`): always `nil`. Lean-first.
-/
module

public import Proof.k8s_io.client_go.util.consistency.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace consistency

open Iris Iris.BI k8s_io.client_go.util.consistency

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.util.consistency.Assumptions]

/-- `p.EnsureReady(o)` of the no-op store: `nil`. -/
abbrev noopConsistencyStore.EnsureReady.spec : Prop :=
  ∀ (p : Loc) (o : Owner),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.consistency }}
    (App (Val (p @!! go.GoType.PointerType noopConsistencyStore.ty @!! go!"EnsureReady")) (Val #o))
  {{ RET #(interface.nil : GoInterface); True }}

end spec

end consistency
end EtcdGrove
end Perennial
