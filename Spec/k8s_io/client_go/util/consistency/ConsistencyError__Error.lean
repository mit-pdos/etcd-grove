/-
`(*ConsistencyError).Error()` (`consistency.go:57`): the error's message. Lean-first.
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

/-- `e.Error()`: some string; the error is unchanged. -/
abbrev ConsistencyError.Error.spec : Prop :=
  ∀ (l : Loc) (dq : DFrac) (e : ConsistencyError),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.consistency ∗ l ↦{dq} e }}
    (App (Val (l @!! go.GoType.PointerType ConsistencyError.ty @!! go!"Error")) (Val #()))
  {{ (s : GoString), RET #s; l ↦{dq} e }}

end spec

end consistency
end EtcdGrove
end Perennial
