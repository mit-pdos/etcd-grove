/-
`(*EtcdServer).PauseSending()` (`server.go:2211`): `s.r.pauseSending()`, which asserts the transport is `rafthttp.Pausable` and calls `Pause()`.

**Users**: the integration framework's `Member.Pause` (`tests/framework/integration/cluster.go:1166`). Snippet `etcdserverboot/boot.go` `ReqPartition`.

**Proof sketch**: `srvMember`'s realization holds `s.r.transport`, the member's `*rafthttp.Transport` (2f's `isTransport`), so the type assertion succeeds; `Transport.Pause.spec` (the caller's `threadTok`).

**Changes**: verify round (A8-completeness F5; rafthttp's request): new. `raftNode.pauseSending` is not translated (inlined here).

**Margin**: none (pausing drops messages: raft tolerates loss).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiBoot

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

/-- **`PauseSending()`**: the transport stops sending. -/
def EtcdServer.PauseSending.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (id : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ srvMember s γ id ∗ threadTok }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!!
      go!"PauseSending")) (Val #()))
  {{ RET #(); threadTok }}

end spec

end EtcdServer
end EtcdGrove
end Perennial
