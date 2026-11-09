/-
## `(*EtcdServer).adjustTicks()` (`server.go:464-525`)

**Users.** `Start` (attached goroutine).

**Proof sketch.** `Members()` of the cluster (`Membership`), the transport's `ActivePeers` (2f), the
raft node's `advanceTicks` (2d): ticks only (no model effect), all reachable from `isServer`.

**Changes** (from `specs-ref`: it took no premise on `s`, the sweep's survey): over `isServer`.

**Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiBoot

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **Fast-forwards the election ticks** of a fresh start. -/
def EtcdServer.adjustTicks.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"adjustTicks")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdServer
end EtcdGrove
end Perennial
