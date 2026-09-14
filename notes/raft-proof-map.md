# Map of the Raft proof

Accurate as of 2026-09-13. Rewrite this when the layout changes.

To read any of these files at spec level — theorem statements, the
definitions they reach, and every axiom and hole, with proof bodies and
proved helper lemmas dropped — run `./etc/tcb-view.py <file>`, or
`./etc/tcb-view.py --summary new/proof/go_etcd_io/raft` for just the list of
what is assumed. Note `v3.v`'s public surface is a `Lemma`, so it needs
`--root wp_Node__Propose`; everywhere else the `Theorem`s are the roots.

## Layers, bottom to top

```
new/code/go_etcd_io/raft/v3/          Goose output — the model of the Go code
new/generatedproof/go_etcd_io/raft/   generated boilerplate proofs
        ↓ required by
new/proof/go_etcd_io/raft/v3_proof/base.v        IsPkgInit boilerplate
new/proof/go_etcd_io/raft/v3_proof/readonly.v    protocol ghost state + lemmas
new/proof/go_etcd_io/raft/v3_proof/protocol.v    node interface (axiomatized)
        ↓
new/proof/go_etcd_io/raft/v3.v                   public surface
        ↓
new/should_build.v:50                            what CI builds
```

## `v3_proof/base.v`

`IsPkgInit` / `GetIsPkgInitWf` instances, all `define_is_pkg_init True%I`, for
every Go package the raft translation touches: `raftpb`, `strconv`, `strings`,
`math`, `quorum`, `tracker`, `confchange`, `big`, `rand`, `bytes`. Pure
boilerplate — when a new package shows up in the translation, add it here.

Also fixes the ambient context used everywhere below:

```coq
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".
```

## `v3_proof/readonly.v` — the substance

The protocol-level development, and the file to read first. Despite the name it
holds the general Raft ghost state, not only read-index material.

**Ghost state.** `raft_names` (record, ~line 50) bundles the ghost names.
Commit log as a half-split `mono_list`: `own_commit_auth` / `own_commit` each
hold `1/2` of `mono_list_auth_own`, with `is_commit` the persistent lower
bound. Per-node terms as a gmap of `mono_nat`: `own_term` / `is_term_lb`.

**Quorums.** `is_quorum` plus `quorums_intersect` and `quorums_subseteq`. This
is where the "any two quorums share a node" argument lives; everything about
staleness leans on it.

**Reads queue.** `own_reads` is an authoritative monotone list of
`(start_index, Φ)` pairs, with persistent witness `is_in_reads`,
`reads_insert` to extend it, and `reads_agree` to use a witness. `is_read_index
γ index Φ` is the read-index witness: given any committed log at least `index`
long, `Φ` holds of it. `try_read` (~line 295) is the main client-facing lemma.

**Heartbeat context.** The mechanism that justifies a linearizable read:
`own_unused_heartbeat_ctx` (ownership of a fresh `(term, ctx)` pair, which lets
you *decide* its staleness quorum), `is_heartbeat_ctx` with agreement lemma,
`is_stale_term`, then `is_HeartbeatRequest` / `is_HeartbeatResp` /
`is_heartbeat_ack` and `heartbeat_ack_not_stale` / `start_heartbeat`. The
invariant is `is_raft_commit_inv` under namespace `Ncommit = N.@"commit"`.

Open questions are marked in the file — including one at the top asking what
the invariant for `MsgHeartbeat` / `MsgHeartbeatResp` should be, and a `TODO`
about backwards compatibility. Read those before redesigning anything here.

**Simplifying assumption:** single configuration. Stated in a comment near
`is_quorum`. Membership change will require revisiting the quorum lemmas.

## `v3_proof/protocol.v` — the trust boundary

`Section axioms` (lines 26–39) is what is currently *assumed* rather than
proved. Above it: `own_propose_message`, `is_node_inner` / `is_node`, and WPs
for `node.Ready`, `node.Advance`, `node.Propose`. Message-type constants are
defined locally (`MsgProp := W32 2`).

Discharging these axioms against `new/code/go_etcd_io/raft/v3/` is the main
outstanding structural task. Anything not proved should be either discharged or
explicitly justified here.

## `v3.v` — public surface

Thin. `is_Node γ n` wraps `is_node` for an `interface.mk (go.PointerType
raft.node)` value, and `wp_Node__Propose` lifts `wp_node__Propose` to the
interface method call. The `Propose` spec takes a fupd over `own_raft_log`,
i.e. the caller supplies the atomic update that appends `data` to the log.

Extending this file to the rest of the `node` interface is the obvious next
increment.

## `v3_proof/election_protocol.v` and `v3_proof/election.v` — leader election

Added 2026-09-12, after the rest of this map was written.
`election_protocol.v` (334 lines) is the protocol state machine: a node state
is `(term, vote, lead, role, votes)`, the `Inductive step` relation is
reflexive-transitive by construction, and `Section ghost` (lines 243–289)
axiomatizes `own_raft_ghost` / `is_message` along with the one refinement
obligation `own_raft_ghost_step` and the payoff `is_leader_unique`.

`election.v` (904 lines) connects that to the translated code: `own_raft_phys`
for the raft struct, `Section helper_axioms` (lines 110–253) for the raft
components election does not reason about, and the `wp_raft__Step` triples plus
`Corollary raft_election_safety` at the bottom. The log is deliberately absent
from the protocol model — `isUpToDate` can only make a node decline to vote,
and declining is always protocol-legal.

Full write-up, including what is still `Admitted` and in what order to attack
it, is in [raft-election-refinement.md](raft-election-refinement.md).
