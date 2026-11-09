/-
`(*EtcdServer).MoveLeader(ctx, lead, transferee)` (`server.go:1268-1300`): refuse a transferee that
is not a voting member (`ErrBadLeaderTransferee`); else ask raft to transfer the leadership and poll
`Lead()` every tick until it is the transferee or the context ends (`ErrTimeoutLeaderTransfer`).

**Users**: v3rpc's `maintenanceServer.MoveLeader` (`ms.lt.MoveLeader`, then `togRPCError`), `Stop`
through `TryTransferLeadershipOnShutdown`.

**Proof sketch** (names only in the translation: trusted): the membership view's `Member` (2e's,
its read lock: the caller's `threadTok`); `Logger`; `s.r.TransferLeadership` (R1's
`node.TransferLeadership`: a message to the raft loop, no effect on the model: raft's leadership
is not observable); `Lead()` (any); the context's `Done` and `time.After`. Both errors are
`etcdserver/errors`' sentinels (`ErrBadLeaderTransferee` mapped; `ErrTimeoutLeaderTransfer`
unmapped, with its message), so their shape is `srvErrShape`.

**Changes**: verify round (A8-completeness F5): new.

**Margin**: no model change, and the post does not say who leads.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiReq

set_option autoImplicit false
set_option linter.iris.dupNamespace false

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

/-- **`MoveLeader(ctx, lead, transferee)`**: `nil`, or an error with its shape; the model is
unchanged. -/
def EtcdServer.MoveLeader.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (ctx : GoInterface) (lead transferee : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ∗
      Context.ctxOk ctx ∗ threadTok }}
    (App (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!!
      go!"MoveLeader")) (Val #ctx)) (Val #lead)) (Val #transferee))
  {{ (err : GoInterface), RET #err; threadTok ∗ (⌜err = GoInterface.nil⌝ ∨ srvErrShape err) }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
