/-
`leasesByExpiry.Less(i, j)` (`lease.go:134`), an internal helper's spec (mirrors the code).
**Users**: `sort.Sort` in `Leases`, `Promote`. **Proof sketch**: the two objects' `Remaining()`
(`leaseExpiry`), compared. In-bounds indices (Go panics otherwise; `sort.Sort` passes them).
**Changes** (from `specs-ref`): over `leaseExpiry`. **Margin**: the answer (time).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.lease.Internal

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

/-- **Whether object `i` expires before object `j`** (some boolean: time). -/
def leasesByExpiry.Less.spec : Prop :=
  ∀ (sl : GoSlice) (ps : List Loc) (dq : DFrac) (i j : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ sl ↦*{dq} ps ∗
      ([∗list] p ∈ ps, leaseExpiry p) ∗
      ⌜0 ≤ sint.Z i ∧ sint.Z i < ps.length ∧ 0 ≤ sint.Z j ∧ sint.Z j < ps.length⌝ }}
    (App (App (Val (sl @!! go_etcd_io.etcd.server.v3.lease.leasesByExpiry.ty @!! go!"Less"))
      (Val #i)) (Val #j))
  {{ (b : Bool), RET #b; sl ↦*{dq} ps }}

end spec
end Lease
end EtcdGrove
end Perennial
