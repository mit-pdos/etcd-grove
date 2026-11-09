/-
## `raft.send(m)` (internal)

**Users.** Every sender: `maybeSendAppend`, `maybeSendSnapshot`, `sendHeartbeat`, `appendEntry`,
`campaign`, `raft.Step` (vote responses, stale-term replies), `stepFollower` (forwarding),
`stepLeader` (read responses), `handle*`, `sendTimeoutNow`. **Proof sketch.** Mirrors the code:
`From` set to the node's id if unset; a vote message keeps its term (non-zero: `sendShape`), any
other gets the node's term unless a proposal or a read request (forwarded unstamped); an append or
vote response goes to `msgsAfterAppend` (its `msgSent` minted at the batch's enter, at the durable
state), any other to `msgs` (not self-addressed: `sendShape`). The message's protocol fact
(`msgJust`) is the caller's; the invariant records it with the queued message. **Changes** (from
`specs-ref`'s `raft__send.lean`): over the opened struct and `msgJust` (was the message's record
over `NState`). **Margin.** None on the view.
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

/-- (internal) Queues `m` with its protocol fact. -/
def raft.send.spec : Prop :=
  ∀ (r : Loc) (γ : Cluster) (id : w64) (o : CoreOpen) (ml : Loc) (m : Msg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftOpen r γ id o ∗ coreInv r γ id o ∗ msgPts ml (DFrac.own 1) m ∗ msgJust r γ id m ∗ ⌜sendShape id m⌝ }}
    (App (Val (r @!! go.GoType.PointerType go_etcd_io.raft.v3.raft.ty @!! go!"send")) (Val #ml))
  {{ RET #(); raftOpen r γ id o ∗ coreInv r γ id o }}

end spec
end Raft
end EtcdGrove
end Perennial
