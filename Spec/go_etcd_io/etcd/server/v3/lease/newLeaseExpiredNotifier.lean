/-
`newLeaseExpiredNotifier()` (`lease_queue.go:68`), an internal helper's spec (mirrors the code).
**Users**: `newLessor`, `clearLeaseExpiredNotifier` (`Demote`). **Proof sketch**: a fresh map and an
empty queue. **Changes**: new (no old spec; `Demote`'s proof calls it). **Margin**: none.
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

/-- **An empty notifier.** -/
def newLeaseExpiredNotifier.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease }}
    (App (Val (@! go_etcd_io.etcd.server.v3.lease.newLeaseExpiredNotifier)) (Val #()))
  {{ (np : Loc), RET #np; notifierAt np (DFrac.own 1) }}

end spec
end Lease
end EtcdGrove
end Perennial
