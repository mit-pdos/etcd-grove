/-
`LeaseQueue.Len()` (`lease_queue.go:33`), an internal helper's spec (mirrors the code). **Users**:
`container/heap` on the notifier's queue and the checkpoint heap. **Changes** (from `specs-ref`):
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

/-- **The queue's length.** -/
def LeaseQueue.Len.spec : Prop :=
  ∀ (s : GoSlice) (xs : List (Loc × w64)) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ queueAt s xs dq }}
    (App (Val (s @!! go_etcd_io.etcd.server.v3.lease.LeaseQueue.ty @!! go!"Len")) (Val #()))
  {{ RET #(W64 xs.length); queueAt s xs dq }}

end spec
end Lease
end EtcdGrove
end Perennial
