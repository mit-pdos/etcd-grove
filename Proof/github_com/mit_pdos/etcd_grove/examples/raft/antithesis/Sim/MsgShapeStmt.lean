/-
Lean-first (no Rocq counterpart).

# A `Ready`'s messages' shape and the logs' normality: the statement (#33 S4, drain)

What `Cluster.drain` takes of a `Ready` beyond `ReadyOutP` (statement only; proved by a `Sim`
induction in `Sim/MsgShape.lean`, as `Outbox.lean`'s `outOk_reach`): every message the `Ready` hands
to another node is from the node itself, of a type the harness's network carries or a (forwarded)
proposal, a heartbeat or its response with no context, its entries normal; and the
log at the `Ready` is normal. The drain reads them as `NetFacts` (`HarnessInv.lean`: `NetMsgOk`, the
types `antStepTypes`, a heartbeat response's empty context, `AllNormal` of the entries), `msgOf`'s
and `entriesOf`'s premises (normal entries; a `Ready`'s entries and committed entries are slices of
the log, `ReadyOutP`), and the next view's normal log. And the destinations (`ReadyMsgsToVoters`,
which `ReadyOutP` then states): every message to another node is to one of the three (a response to
the handled message's sender, a node by `NetOk`; a leader's appends and heartbeats to the
configuration's peers, `AppSendOk`'s and `TickEnd`'s `c.ids`; a campaign's requests to the voters; a
forwarded proposal to the leader hint, a node by `NodeOk`'s `LeadOk`). The premise on the `Ready` is
`ReadyOutP`'s messages clause only (its messages the outbox's to other nodes), which `ReadyOut` gives
without the destinations.

Normality is not part of the binding's relation (an entry's type is not in the checker's state), so
it is a premise: the view's log is normal and so are the entries of the message the drain handles
(the network's, `NetFacts`), and a handled heartbeat has no context (`NetFacts`; a heartbeat response
echoes it); the node's log after an input or `Advance` is then normal (a proposal's
entry, `propMsg`; a new leader's empty entry; a received append's entries).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Stmts

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

section stmt
variable [GooseExts]

/-- Normal entries (`EntryNormal = 0`; `HarnessDefs.lean`'s `AllNormal`, restated here so that `Sim`
imports only the protocol model). -/
def EntsNormal (es : List EntryM) : Prop := ∀ e ∈ es, e.Type' = W32 0

/-- The message types the harness's network carries (`antStepTypes`). -/
def NetTy (ty : MsgType) : Prop :=
  ty = .app ∨ ty = .appResp ∨ ty = .vote ∨ ty = .voteResp ∨ ty = .heartbeat ∨ ty = .heartbeatResp

/-- **A `Ready`'s message to another node, as the drain hands it out** (from node `id`): from `id`;
of a type the network carries (`RawNode.Step`'s types at the receiver), or a proposal (forwarded,
which `Cluster.send` drops); a heartbeat or a heartbeat response with no context (no read-index
request is pending, the harness's scope); its entries normal. (Its nonzero term, but a proposal's,
is raft's `SentMsgShape`, in the `Ready`'s `isRaftMsg`.) -/
def ReadyMsgShape (id : w64) (q : Msg) : Prop :=
  q.src = id ∧ (NetTy q.ty ∨ q.ty = .propose) ∧
  ((q.ty = .heartbeat ∨ q.ty = .heartbeatResp) → q.ctx = []) ∧ EntsNormal q.entries

/-- **The shape of a `Ready`'s messages and the normality of its log**: a `Ready` taken at the state
`ps₁` node `n` reached from its view `v` (`Reach`, over the sent messages `net`; `NetOk`, `NodeOk`:
the binding's relation, as `readyMsgNums`), its messages the outbox's to other nodes, the view's log
and the handled message's entries normal, has its log normal, every message to another node
`ReadyMsgShape`, and each to one of the three nodes (`ReadyMsgsToVoters`). -/
abbrev msgShape.stmt : Prop :=
  ∀ (S : AntCheck.State) (net : List Msg) (n : Fin 3) (v : NodeView) (ps₁ : PState) (rd : ReadyD),
    NetOk S net → NodeOk S net n v → Reach (nodeId n) net v ps₁ →
    rd.msgs.Perm (ps₁.outbox.filter (fun q => decide (q.dst ≠ nodeId n))) →
    EntsNormal v.ps.log →
    (∀ m, v.cause = some m → EntsNormal m.entries ∧ (m.ty = .heartbeat → m.ctx = [])) →
    EntsNormal ps₁.log ∧ (∀ q ∈ rd.msgs, ReadyMsgShape (nodeId n) q) ∧ ReadyMsgsToVoters rd

end stmt

end AntSim
end EtcdGrove
end Perennial
