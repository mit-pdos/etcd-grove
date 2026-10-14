/-
Port of `election_proof/election.v` (at 857d09190), the lemmas after its `Require`s; the
`Require`s themselves are `Link.lean` (generated) and `MemstorageInstance.lean`.

### Refinement of etcd raft

`Link.lean` is the aggregator. Every Hoare triple lives in its own spec/proof pair
under `Raft/` (`Spec/<fn>.lean`, `Proof/<fn>.lean`; Rocq's
spec/postulates/proof/link quadruple), and `Link.lean` instantiates every proof with
its callees' results; importing `Link.lean` from the root module (`EtcdGrove.lean`)
is what keeps the build honest, since `lake build` builds only what the root reaches, and
a link nothing imported would silently go unchecked.

The top-level result is `raft.wp_Step` (`Link.lean`): running `Step` on a
message takes the physical raft struct from a state refining the protocol state `s` to
one refining `s'`, and the ghost protocol state can be moved from `s` to `s'` at the same
time -- i.e. the implementation refines the protocol of `Protocol/`. Beside
it: `RawNode.wp_Propose`, the client's entry point (one `Step` of a `MsgProp`), and
`wp_newRaft`, the constructor, which establishes `ownRaftPhys` (`Spec/newRaft.lean`).
The `RawNode` results (`wp_Propose`, `wp_Ready`, `wp_Advance`, `wp_HasReady`) are
client-facing since 2026-10-09: stated on `ownRawNode γ rn id rs` (`InvRawnode.lean`),
with no protocol state in them; the refinement above is how they are proved.
`wp_Ready` is the composition of `wp_readyWithoutAccept` and `wp_acceptReady`
(2026-10-10), which `node.go` calls apart (through `ownRawNodeReady`,
`InvRawnodeReady.lean`).

Scope: see `notes/STATUS.md` (its first sections) for what the Go-level results cover today:
proposals, read index (`ReadOnlySafe`), leader transfer, learners and conf changes are in;
since 2026-10-14 (reconfiguration stage B7 part 2) **changing the voter set through the
`RawNode` API**: a `RawNode` in the dynamic mode (`RNState.mode`, `NewRawNode` from
`raft_dyn_alloc`'s ghost state) takes `ApplyConfChange` of the next committed conf entry and
`Advance` after it (A1), with the committed log handed out (`isCommitted`) and the read
states (`readStateOk`) as in the static mode; `node.go` and the register stay in the static
mode. Pre-vote is verified in `raft.Step` but off at the public API (`ownRawNode` holds
`prevote = false`); check-quorum, the lease-based read option, asynchronous storage writes
and crash-restart are out; a snapshot at a `RawNode` (from the network) is out.

**The boundary is the Go public API.** The specs of the public functions (`RawNode.wp_*`,
`node.wp_*`, `wp_NewRawNode`, ... in `Link.lean`) are what this development verifies. A
protocol-level theorem is scaffolding (notes/decisions.md, "Model-level theorems in
`Results.lean` are scaffolding"): the reconfiguration model's restatements (`raft_reconfig_*`,
with the collection `raft-dyn.txt`) and the static sanity check `raft_election_safety` were
deleted on 2026-10-14 (stage B7 part 2), once the public specs reached the dynamic ghost
state. This file now only prints the top-level results' trust base.

Trust boundary. Two kinds, and the layout keeps them apart:
  - A `Proof/<fn>.lean` of a function outside the scope is an `axiom <fn>.wp_proof`.
    These are Lean `axiom`s. The client-supplied interfaces are not: `isLogger` is a
    definition (the triples a client supplies), and `ownStorage` is a parameter, the
    field of `StorageModel GF`, so the results hold for every storage predicate
    (both axioms until 2026-10-08).
  - A function that is in scope but unfinished is a `sorry` inside its own
    `Proof/<fn>.lean`.
Nothing in a proof theorem's hypothesis list is an assumption: a callee spec taken as a
hypothesis (Rocq's `postulates_*.v`, a `Module Type`) is discharged in `Link.lean` by
the callee's own result, and adds nothing to `#print axioms`. The `#print axioms` at the
end of this file print the trust base of the top-level results in the build log.

Lean notes:
* `newRaft_post_init` takes its premise in the shape of `newRaft`'s postcondition
  (`Spec/newRaft.lean`) minus the `s.prevote = cv.PreVote'` conjunct, as the Rocq does.
-/
module

public import Proof.go_etcd_io.raft.v3.Link
-- `newRaft_post_init` (moved there 2026-10-09: `NewRawNode`'s proof uses it)
public import Spec.go_etcd_io.raft.v3.NewRawNode

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

end EtcdGrove
end Perennial

/-! The trust base of the top-level results, printed in the build log. -/
#print axioms Perennial.EtcdGrove.raft.wp_Step
#print axioms Perennial.EtcdGrove.RawNode.wp_Propose
#print axioms Perennial.EtcdGrove.RawNode.wp_ProposeConfChange
#print axioms Perennial.EtcdGrove.wp_newRaft
#print axioms Perennial.EtcdGrove.RawNode.wp_Ready
#print axioms Perennial.EtcdGrove.RawNode.wp_readyWithoutAccept
#print axioms Perennial.EtcdGrove.RawNode.wp_acceptReady
#print axioms Perennial.EtcdGrove.RawNode.wp_Advance
#print axioms Perennial.EtcdGrove.RawNode.wp_HasReady
#print axioms Perennial.EtcdGrove.RawNode.wp_Campaign
#print axioms Perennial.EtcdGrove.RawNode.wp_Step
#print axioms Perennial.EtcdGrove.RawNode.wp_Tick
#print axioms Perennial.EtcdGrove.RawNode.wp_ApplyConfChange
#print axioms Perennial.EtcdGrove.wp_NewRawNode
#print axioms Perennial.EtcdGrove.MemoryStorage.wp_Append
#print axioms Perennial.EtcdGrove.wp_NewMemoryStorage
#print axioms Perennial.EtcdGrove.wp_RestartNode
#print axioms Perennial.EtcdGrove.node.wp_run
#print axioms Perennial.EtcdGrove.wp_newNode
#print axioms Perennial.EtcdGrove.node.wp_Propose
#print axioms Perennial.EtcdGrove.node.wp_ProposeConfChange
#print axioms Perennial.EtcdGrove.node.wp_Step
#print axioms Perennial.EtcdGrove.node.wp_Tick
#print axioms Perennial.EtcdGrove.node.wp_Ready
#print axioms Perennial.EtcdGrove.node.wp_Advance
