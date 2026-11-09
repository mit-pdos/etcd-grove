/-
`leasesByExpiry.Len()` (`lease.go:133`), an internal helper's spec (mirrors the code). **Users**:
`sort.Sort` in `Leases`, `Promote`. **Changes** (from `specs-ref`): unchanged. **Margin**: none.
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

/-- **The slice's length.** -/
def leasesByExpiry.Len.spec : Prop :=
  ∀ (sl : GoSlice) (ps : List Loc) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ sl ↦*{dq} ps }}
    (App (Val (sl @!! go_etcd_io.etcd.server.v3.lease.leasesByExpiry.ty @!! go!"Len")) (Val #()))
  {{ RET #(W64 ps.length); sl ↦*{dq} ps }}

end spec
end Lease
end EtcdGrove
end Perennial
