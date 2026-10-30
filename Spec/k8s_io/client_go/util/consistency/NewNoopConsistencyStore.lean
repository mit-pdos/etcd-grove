/-
`NewNoopConsistencyStore()` (`consistency.go:250`): a store that records nothing. Lean-first.
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

/-- `NewNoopConsistencyStore()`: a `*noopConsistencyStore` as a `ConsistencyStore`. -/
abbrev NewNoopConsistencyStore.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.consistency }}
    (App (Val (@! NewNoopConsistencyStore)) (Val #()))
  {{ (p : Loc), RET #(interface.mkOk (go.GoType.PointerType noopConsistencyStore.ty) #p :
      ConsistencyStore); True }}

end spec

end consistency
end EtcdGrove
end Perennial
