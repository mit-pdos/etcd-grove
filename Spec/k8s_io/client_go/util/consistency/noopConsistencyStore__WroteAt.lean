/-
`(*noopConsistencyStore).WroteAt` (`consistency.go:236`): records nothing. Lean-first.
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

/-- `p.WroteAt(o, uid, gr, rv)` of the no-op store: nothing. -/
abbrev noopConsistencyStore.WroteAt.spec : Prop :=
  ∀ (p : Loc) (o : Owner) (uid : GoString) (gr : GR) (rv : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.consistency }}
    (App (App (App (App (Val (p @!! go.GoType.PointerType noopConsistencyStore.ty @!! go!"WroteAt"))
      (Val #o)) (Val #uid)) (Val #gr)) (Val #rv))
  {{ RET #(); True }}

end spec

end consistency
end EtcdGrove
end Perennial
