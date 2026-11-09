/-
`leasesByExpiry.Swap(i, j)` (`lease.go:135`), an internal helper's spec (mirrors the code).
**Users**: `sort.Sort` in `Leases`, `Promote`. In-bounds indices. **Changes** (from `specs-ref`):
unchanged. **Margin**: none.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.Internal

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Lease

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- **Swap elements `i` and `j`.** -/
def leasesByExpiry.Swap.spec : Prop :=
  ∀ (sl : GoSlice) (ps : List Loc) (i j : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ sl ↦* ps ∗
      ⌜0 ≤ sint.Z i ∧ sint.Z i < ps.length ∧ 0 ≤ sint.Z j ∧ sint.Z j < ps.length⌝ }}
    (App (App (Val (sl @!! go_etcd_io.etcd.server.v3.lease.leasesByExpiry.ty @!! go!"Swap"))
      (Val #i)) (Val #j))
  {{ RET #(); sl ↦* ((ps.set (sint.nat i) (ps[sint.nat j]!)).set (sint.nat j) (ps[sint.nat i]!)) }}

end spec
end Lease
end EtcdGrove
end Perennial
