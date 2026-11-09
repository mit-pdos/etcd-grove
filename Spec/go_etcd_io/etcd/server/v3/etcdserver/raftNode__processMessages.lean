/-
`(*raftNode).processMessages(ms)` (`raft.go:370-414`): from last to first, drop messages to removed
members and all but the last `MsgAppResp`, divert `MsgSnap`s to `msgSnapC` (dropped if full), note
late heartbeats; return the rest.

**Users**: the loop (`raft.go:250, 303`). Snippet `raftnode.go` (`ReqWriteBeforeSend`).

**Proof sketch**: `isIDRemoved` (2e's membership query: any answer); a dropped message's resources
are dropped; a `MsgSnap` goes on `msgSnapC` with `msgPts` and `msgSent` (its credit is trivial, R1's
`msgCredit_intro`), the channel's payload (`isRaftNode`); `td.Observe` (2e's contention detector);
the kept ones' `sendable` resources go to the result (`append`). Dropping a `MsgAppResp` older than a
later one is safe: R1's acknowledgements are monotone (the later carries the higher index).

**Changes** from `specs-ref`'s spec (`rnMsgOk E m`): over `sendable`. **Margin**: which messages
are kept is not stated.
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

def raftNode.processMessages.spec : Prop :=
  ∀ (r : Loc) (γ : Names) (id : w64) (n : Loc) (ms : GoSlice) (msgs : List Raft.Msg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isRaftNode r γ id n ∗ sendable γ ms msgs }}
    (App (Val (r @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.raftNode.ty @!!
      go!"processMessages")) (Val #ms))
  {{ (out : GoSlice), RET #out; ∃ msgs', sendable γ out msgs' }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
