/-
`(*noopConsistencyStore).Clear` (`consistency.go:239`): nothing. Lean-first.
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.util.consistency.Assumptions]

/-- `p.Clear(o, uid)` of the no-op store: nothing. -/
abbrev noopConsistencyStore.Clear.spec : Prop :=
  ∀ (p : Loc) (o : Owner) (uid : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.consistency }}
    (App (App (Val (p @!! go.GoType.PointerType noopConsistencyStore.ty @!! go!"Clear"))
      (Val #o)) (Val #uid))
  {{ RET #(); True }}

end spec

end consistency
end EtcdGrove
end Perennial
