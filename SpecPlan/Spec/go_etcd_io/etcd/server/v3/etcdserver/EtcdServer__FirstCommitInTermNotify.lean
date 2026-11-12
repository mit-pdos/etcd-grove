/-
`(*EtcdServer).FirstCommitInTermNotify()` (`server.go:1746-1748`): `s.firstCommitInTerm.Receive()`.

**Users**: the read loop (`readEnv`'s `FirstCommitInTermNotify` row: a read round retries its
`ReadIndex` when it fires).

**Proof sketch**: the read-only field `s.firstCommitInTerm` (`srvStarted`: 2c's `notifierAt`);
`Notifier.Receive.spec` (its read lock: the caller's `threadTok`), whose channel is closed only by a
`Notify` (`recvAny`).

**Changes**: verify round (A7-provability F4, F6): new here (the old tree's
`EtcdServer__FirstCommitInTermNotify.lean`), with the caller's thread token.

**Margin**: the post forgets which commit the channel announces.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiApply

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

/-- **`FirstCommitInTermNotify()`**: a channel closed at the next first commit in a term. -/
def EtcdServer.FirstCommitInTermNotify.spec : Prop :=
  ∀ (s : Loc) (γ : Names) (id : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvNode s γ id ∗ srvStarted s γ id ∗ threadTok }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!!
      go!"FirstCommitInTermNotify")) (Val #()))
  {{ (ch : Loc), RET #ch; Read.recvAny ch ∗ threadTok }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
