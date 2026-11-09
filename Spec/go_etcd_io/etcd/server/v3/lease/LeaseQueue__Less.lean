/-
`LeaseQueue.Less(i, j)` (`lease_queue.go:35`), an internal helper's spec (mirrors the code).
**Users**: `container/heap`. **Proof sketch**: the cells' times compared (`time.Time.Before`).
In-bounds indices. **Changes** (from `specs-ref`): unchanged. **Margin**: the answer (time).
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

/-- **Whether cell `i`'s time is before cell `j`'s** (some boolean: time). -/
def LeaseQueue.Less.spec : Prop :=
  ∀ (s : GoSlice) (xs : List (Loc × w64)) (dq : DFrac) (i j : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ queueAt s xs dq ∗
      ⌜0 ≤ sint.Z i ∧ sint.Z i < xs.length ∧ 0 ≤ sint.Z j ∧ sint.Z j < xs.length⌝ }}
    (App (App (Val (s @!! go_etcd_io.etcd.server.v3.lease.LeaseQueue.ty @!! go!"Less")) (Val #i))
      (Val #j))
  {{ (b : Bool), RET #b; queueAt s xs dq }}

end spec
end Lease
end EtcdGrove
end Perennial
