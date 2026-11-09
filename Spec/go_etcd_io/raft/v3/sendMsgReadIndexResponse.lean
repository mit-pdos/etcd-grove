/-
## `sendMsgReadIndexResponse(r, m)` (internal)

**Users.** `stepLeader`'s `MsgReadIndex` arm (`raft.go:1380`), `releasePendingReadIndexMessages`
(`:2143`). **Proof sketch.** The read's update was deposited at its first step (realization item 3).
The node the only voter: answered at once at the commit index (`responseToReadIndexReq`; the commit
index covers every entry committed before the read: an entry of the leader's term is committed,
`committedEntryInCurrentTerm`). Else `ReadOnlySafe` (`ConfigOk`): registered at the commit index (R3's
`addRequest`), the node's own acknowledgement (`recvAck`), `bcastHeartbeat`; confirmed later by a
quorum's heartbeat responses (`stepLeader`'s `MsgHeartbeatResp` arm). **Changes** (from
`specs-ref`'s `sendMsgReadIndexResponse.lean`): over the opened struct; round 1: the read's update
deposited at the first step and fired at the ghost commits (as the old proof), not at confirmation.
**Margin.** The view and log are unchanged.
-/
module

public import Spec.go_etcd_io.raft.v3.ApiCore

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Raft

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- (internal) A leader with an entry of its term committed answers or registers a read. -/
def sendMsgReadIndexResponse.spec : Prop :=
  ∀ (r : Loc) (γ : Cluster) (id : w64) (o : CoreOpen) (ml : Loc) (m : Msg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftOpen r γ id o ∗ coreInv r γ id o ∗ msgPts ml (DFrac.own 1) m ∗
      (stepIn γ id m ∨ (msgSent γ m ∗ ⌜m.type = MsgReadIndex ∧ m.to = id⌝)) ∗
      ⌜m.type = MsgReadIndex ∧ o.view.role = StateLeader ∧
        o.log.termOf o.log.committed = some o.view.hs.term⌝ }}
    (App (App (Val (@! go_etcd_io.raft.v3.sendMsgReadIndexResponse)) (Val #r)) (Val #ml))
  {{ RET #(); ∃ o', raftOpen r γ id o' ∗ coreInv r γ id o' ∗ ⌜o'.view = o.view⌝ }}

end spec
end Raft
end EtcdGrove
end Perennial
