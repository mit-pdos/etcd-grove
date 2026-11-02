module
public import Proof.go_etcd_io.bbolt.internal.common.Init

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt.internal.common

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

/-- `s.Less(i, j)`: page `i`'s id is below page `j`'s. -/
abbrev Pages.Less.spec : Prop :=
  ∀ (s : GoSlice) (ps : List Loc) (dq : DFrac) (i j : w64) (pi pj : Loc) (vi vj : Page)
    (qi qj : DFrac),
  0 ≤ sint.Z i → 0 ≤ sint.Z j → ps[sint.nat i]? = some pi → ps[sint.nat j]? = some pj →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ s ↦*{dq} ps ∗ pi ↦{qi} vi ∗ pj ↦{qj} vj }}
    (App (App (Val (s @!! Pages.ty @!! go!"Less")) (Val #i)) (Val #j))
  {{ RET #(decide (uint.Z vi.id' < uint.Z vj.id')); s ↦*{dq} ps ∗ pi ↦{qi} vi ∗ pj ↦{qj} vj }}

end spec

end bbolt
end EtcdGrove
end Perennial
