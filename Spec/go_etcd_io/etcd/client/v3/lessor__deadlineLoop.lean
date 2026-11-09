/-
`(*clientv3.lessor).deadlineLoop` (`client/v3/lease.go`).

Users: `KeepAlive` (a goroutine, started once).

Proof sketch: a timer loop (`time.NewTimer`, `Reset`, `Stop`: Perennial's time); each tick, under `l.mu`,
closes (`keepAlive.close`) and deletes the entries whose deadline is before `time.Now()`.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/lessor__deadlineLoop.lean`: restated over `lessorHandle`.

Margin: none.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.ApiLease

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ClientV3

open Iris Iris.BI EtcdModel EtcdWire
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `l.deadlineLoop()`: the deadline loop: closes the entries whose deadline passed, until `donec` closes. -/
def lessor.deadlineLoop.spec : Prop :=
  ∀ (l c : Loc) (γ : Cluster) (who : Principal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ lessorHandle l c γ who ∗ clientReady c }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!! go!"deadlineLoop")) (Val #()))
  {{ (v : val), RET v; True }}

end spec

end ClientV3
end EtcdGrove
end Perennial
