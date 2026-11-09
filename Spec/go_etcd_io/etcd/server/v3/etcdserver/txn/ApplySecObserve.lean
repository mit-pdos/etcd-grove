/-
## `ApplySecObserve(version, op, success, latency)` (`metrics.go`, names-only)

**Users.** The uber-applier's `dispatch` (`apply/uber_applier.go:98`). Snippet: none.

**Proof sketch.** Trust boundary (prometheus' histogram, a float division): it records a latency.
**Changes.** Unchanged. **Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Txn

open Iris Iris.BI EtcdModel EtcdWire

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-- `ApplySecObserve(...)` returns. -/
def ApplySecObserve.spec : Prop :=
  ∀ (ver op : GoString) (success : Bool) (latency : time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.ApplySecObserve)) (Val #ver)) (Val #op)) (Val #success)) (Val #latency))
  {{ RET #(); True }}

end spec
end Txn
end EtcdGrove
end Perennial
