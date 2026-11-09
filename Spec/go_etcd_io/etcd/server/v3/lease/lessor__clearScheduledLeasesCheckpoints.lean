/-
`(*lessor).clearScheduledLeasesCheckpoints()` (`lessor.go:689`), an internal helper's spec (mirrors
the code). **Users**: `Demote`, under `le.mu`. **Proof sketch**: a fresh empty heap stored.
**Changes**: new (no old spec; `Demote`'s proof calls it). **Margin**: none.
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

/-- **Drop the scheduled checkpoints** (under the lock). -/
def lessor.clearScheduledLeasesCheckpoints.spec : Prop :=
  ∀ (le : Loc) (c : Cfg) (ls : LessorState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗
      lessorFields le c (DFrac.own 1) ls }}
    (App (Val (le @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.lessor.ty @!!
      go!"clearScheduledLeasesCheckpoints")) (Val #()))
  {{ RET #(); lessorFields le c (DFrac.own 1) ls }}

end spec
end Lease
end EtcdGrove
end Perennial
