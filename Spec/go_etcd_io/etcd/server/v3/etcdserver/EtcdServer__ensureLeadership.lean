/-
`(*EtcdServer).ensureLeadership()` (`server.go:912-939`): `true` if the member ticked recently
(`isActive`); otherwise a linearizable read under `s.ctx` with the request timeout, then whether the
raft status names this member leader and the cluster has more than one voter.

**Users**: `revokeExpiredLeases` (`server.go:861`), `LeaseRenew` (`v3_server.go`), the lessor's
checkpointer closure (`server.go:395-403`: 3c's `ckptOk`).

**Proof sketch**: `Logger.spec` (the thread's token; `srvMember` by `srvNode_member`);
`isActive` (`raftNode.getLatestTickTs`, `time.Now`: any answer); `context.WithTimeout(s.ctx, ...)`
(`RequestTimeout.spec`); `LinearizableReadNotify.spec` at the current `committedLb` (any answer
used only as a boolean); `raftStatus()` (R1's `node.Status`: a status the caller owns); the
cluster's `VotingMemberIDs` (2e's membership, its read lock: the thread's token). Every answer is
safe for the callers: a revocation, a renewal or a checkpoint proposed by a non-leader is decided by
raft and the model (`envUpd`'s steps are idempotent).

**Changes**: verify round (A7-provability F7, completeness F3): new here (the old tree's
`EtcdServer__ensureLeadership.lean`).

**Margin**: the boolean is not tied to raft's leadership.
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

/-- **`ensureLeadership()`**: a boolean (any). -/
def EtcdServer.ensureLeadership.spec : Prop :=
  ∀ (s : Loc) (γ : Names) (id : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvNode s γ id ∗ srvStarted s γ id ∗ threadTok }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!!
      go!"ensureLeadership")) (Val #()))
  {{ (b : Bool), RET #b; threadTok }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
