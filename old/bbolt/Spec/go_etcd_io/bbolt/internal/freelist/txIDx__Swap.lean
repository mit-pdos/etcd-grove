module
public import Proof.go_etcd_io.bbolt.internal.freelist.Model

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt.internal.freelist

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

/-- `t.Swap(i, j)`: elements `i` and `j` of `t` are exchanged. -/
abbrev txIDx.Swap.spec : Prop :=
  ∀ (t : GoSlice) (xs : List w64) (i j : w64) (x y : w64),
  0 ≤ sint.Z i → 0 ≤ sint.Z j → xs[sint.nat i]? = some x → xs[sint.nat j]? = some y →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ t ↦* xs }}
    (App (App (Val (t @!! txIDx.ty @!! go!"Swap")) (Val #i)) (Val #j))
  {{ RET #(); t ↦* ((xs.set (sint.nat i) y).set (sint.nat j) x) }}

end spec

end bbolt
end EtcdGrove
end Perennial
