/-
Lean-first (no Rocq counterpart).

# A `Ready`'s messages' shape and the logs' normality: the statement (#33 S4, drain; parity B1:
N servers, the mask's message types, read contexts)

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

/-- Normal entries (`EntryNormal = 0`; `HarnessDefs.lean`'s `AllNormal`, restated here). -/
def EntsNormal (es : List EntryM) : Prop := ∀ e ∈ es, e.Type' = W32 0

/-- The harness's entries (`EntsHarness`): normal (a proposal's, a leader's empty entry, the boot
entry). Parity B3 adds conf entries that decode (`CCDecodes`). -/
def EntsHarness (es : List EntryM) : Prop := EntsNormal es

/-- The message types the harness's network carries under the mask `md` (`stepTypes md`'s protocol
types): `antStepTypes`, and pre-vote, read-index and snapshot messages when their features are on. -/
def NetTy (md : RnMode) (ty : MsgType) : Prop :=
  ty = .app ∨ ty = .appResp ∨ ty = .vote ∨ ty = .voteResp ∨ ty = .heartbeat ∨ ty = .heartbeatResp ∨
  (md.prevote = true ∧ (ty = .preVote ∨ ty = .preVoteResp)) ∨
  (md.reads = true ∧ (ty = .readIndex ∨ ty = .readIndexResp)) ∨ (md.snapshots = true ∧ ty = .snap)

/-- **A `Ready`'s message to another node, as the drain hands it out** (from node `id`): from `id`;
of a type the network carries, or a (forwarded) proposal; without reads, a heartbeat or a heartbeat
response with no context; its entries the harness's. -/
def ReadyMsgShape (md : RnMode) (id : w64) (q : Msg) : Prop :=
  q.src = id ∧ (NetTy md q.ty ∨ q.ty = .propose) ∧
  (md.reads = false → (q.ty = .heartbeat ∨ q.ty = .heartbeatResp) → q.ctx = []) ∧
  EntsHarness q.entries

/-- **The shape of a `Ready`'s messages and the harness's entries in its log**: a `Ready` taken at
the state `r₁` node `n` reached from its view `v` (`Reach`; `NetOk`, `NodeOk`: the binding's
relation), its messages the outbox's to other nodes, the view's full log and the handled message's
entries the harness's (and, without reads, a handled heartbeat with no context), has its full log
the harness's, every message to another node `ReadyMsgShape`, and each to one of the servers. -/
abbrev msgShape.stmt : Prop :=
  ∀ (R : RunCfg) (dec : CCDec) (Adm : List EntryM → CCState → Prop) (S : AntCheck.State)
    (net : List Msg) (xnet : List XMsg) (n : Fin R.N) (v : NodeView) (r₁ : RState)
    (xs : List XMsg) (rd : ReadyD),
    NetOk R S net → NodeOk R dec S net n v → Reach R dec Adm net xnet n v r₁ xs →
    (rd.msgs ++ rd.resp).Perm (r₁.p.outbox.filter (fun q => decide (q.dst ≠ nodeId n))) →
    EntsHarness v.r.full →
    (∀ m, v.cause = some m → EntsHarness m.entries ∧ (R.md.reads = false → m.ty = .heartbeat → m.ctx = [])) →
    EntsHarness r₁.full ∧ (∀ q ∈ rd.msgs ++ rd.resp, ReadyMsgShape R.md (nodeId n) q) ∧
    ReadyMsgsToVoters R.N rd

end stmt

end AntSim
end EtcdGrove
end Perennial
