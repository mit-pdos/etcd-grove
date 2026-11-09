/-
`(*EtcdServer).LeaderChangedNotify()` (`server.go:1738-1740`): `s.leaderChanged.Receive()`.

**Users**: v3rpc's watch and lease streams (`monitorLeader`), the lessor's keep-alive loop:
they end on a leader change.

**Proof sketch**: the read-only field `s.leaderChanged` (`srvStarted`: 2c's `notifierAt`);
`Notifier.Receive.spec` (its read lock: the caller's `threadTok`), whose channel is closed only by a
`Notify` (`recvAny`).

**Changes**: verify round (A7-provability F4, F6): new here (the old tree's
`EtcdServer__LeaderChangedNotify.lean`; S1 of A8-completeness), with the caller's thread token.

**Margin**: the post forgets which leader change the channel announces.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiApply

set_option autoImplicit false
set_option linter.iris.dupNamespace false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

/-- **`LeaderChangedNotify()`**: a channel closed at the next leader change. -/
def EtcdServer.LeaderChangedNotify.spec : Prop :=
  ∀ (s : Loc) (γ : Names) (id : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvNode s γ id ∗ srvStarted s γ id ∗ threadTok }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!!
      go!"LeaderChangedNotify")) (Val #()))
  {{ (ch : Loc), RET #ch; Read.recvAny ch ∗ threadTok }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
