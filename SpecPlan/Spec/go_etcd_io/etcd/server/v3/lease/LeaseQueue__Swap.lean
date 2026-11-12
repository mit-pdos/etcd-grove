/-
`LeaseQueue.Swap(i, j)` (`lease_queue.go:39`), an internal helper's spec (mirrors the code).
**Users**: `container/heap`. **Proof sketch**: swap the slice's elements, store each cell's new
index. In-bounds indices. **Changes** (from `specs-ref`): unchanged. **Margin**: none.
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

/-- **Swap cells `i` and `j`**, their indices updated. -/
def LeaseQueue.Swap.spec : Prop :=
  ∀ (s : GoSlice) (xs : List (Loc × w64)) (i j : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ queueAt s xs (DFrac.own 1) ∗
      ⌜0 ≤ sint.Z i ∧ sint.Z i < xs.length ∧ 0 ≤ sint.Z j ∧ sint.Z j < xs.length⌝ }}
    (App (App (Val (s @!! go_etcd_io.etcd.server.v3.lease.LeaseQueue.ty @!! go!"Swap")) (Val #i))
      (Val #j))
  {{ RET #(); queueAt s ((xs.set (sint.nat i) (xs[sint.nat j]!)).set (sint.nat j) (xs[sint.nat i]!))
      (DFrac.own 1) }}

end spec
end Lease
end EtcdGrove
end Perennial
