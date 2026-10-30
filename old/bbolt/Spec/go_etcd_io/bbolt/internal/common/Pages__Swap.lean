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

/-- `s.Swap(i, j)`: elements `i` and `j` of `s` are exchanged. -/
abbrev Pages.Swap.spec : Prop :=
  ∀ (s : GoSlice) (ps : List Loc) (i j : w64) (x y : Loc),
  0 ≤ sint.Z i → 0 ≤ sint.Z j → ps[sint.nat i]? = some x → ps[sint.nat j]? = some y →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ s ↦* ps }}
    (App (App (Val (s @!! Pages.ty @!! go!"Swap")) (Val #i)) (Val #j))
  {{ RET #(); s ↦* ((ps.set (sint.nat i) y).set (sint.nat j) x) }}

end spec

end bbolt
end EtcdGrove
end Perennial
