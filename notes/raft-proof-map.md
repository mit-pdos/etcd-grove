# Map of the Raft proof

Accurate as of 2026-09-14. Rewrite this when the layout changes.

To read any of these files at spec level — theorem statements, the
definitions they reach, and every axiom and hole, with proof bodies and
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

new/proof/go_etcd_io/raft/v3_proof/election_protocol.v   election model
        ↓
new/proof/go_etcd_io/raft/v3_proof/election/{defs,inv_*,step_lemmas}.v
        ↓        shared vocabulary, outside the module system
new/proof/go_etcd_io/raft/v3_proof/election/spec_<fn>.v   one per Go function
        ↓            ↓ postulates_<fn>.v          ↓ proof_<fn>.v
new/proof/go_etcd_io/raft/v3_proof/election/link_<fn>.v
        ↓
new/proof/go_etcd_io/raft/v3_proof/election.v    aggregator + election safety
        ↓
new/should_build.v:51                            what CI builds
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

## `v3_proof/election_protocol.v` — leader election, protocol side

Added 2026-09-12. The protocol state machine: a node state is
`(term, vote, lead, role, votes)`, the `Inductive step` relation is
reflexive-transitive by construction, and `Section ghost` (lines 243–289)
axiomatizes `own_raft_ghost` / `is_message` along with the one refinement
obligation `own_raft_ghost_step` and the payoff `is_leader_unique`.

The log is deliberately absent from the protocol model — `isUpToDate` can only
make a node decline to vote, and declining is always protocol-legal.

## `v3_proof/election/` — leader election, implementation side

Restructured 2026-09-14 from a single 1072-line `election.v` into **one file
per Go function**, and extended on 2026-09-18 to cover *every* Go function
the path touches rather than only the thirteen top ones. 192 files, 44
collections; the shape, and why, is in [decisions.md](decisions.md). To find
a function's specification there is exactly one place to look:

    v3_proof/election/spec_<fn>.v

and `etc/check-module-discipline.py` fails if a triple is anywhere else.

**Per function**, 44 of them. The thirteen driving the election path
(`voteRespMsgType`, `raft__send_vote`, `raft__reset`, `raft__becomeFollower`,
`raft__becomeCandidate`, `raft__becomeLeader`, `raft__poll`,
`raft__campaign`, `raft__hup`, `stepCandidate_MsgVoteResp`,
`stepFollower_MsgVoteResp`, `stepLeader_MsgVoteResp`, `raft__Step`), and the
thirty-one they call:

- the log — `unstable__maybe{FirstIndex,LastIndex,Term}`,
  `raftLog__{firstIndex,lastIndex,term,lastEntryID,isUpToDate,hasNextOrInProgressSnapshot}`;
- the tracker — `ProgressTracker__{ResetVotes,RecordVote,TallyVotes,Visit}`,
  `tracker_NewInflights`, `Inflights__reset`,
  `Progress__{ResetState,BecomeReplicate}`;
- the rest of raft — `raft__{promotable,hasUnappliedConfChanges,appendEntry,bcastAppend,resetRandomizedElectionTimeout,abortLeaderTransfer}`,
  `newReadOnly`, the five `traceX` hooks;
- outside raft — `JointConfig__IDs`, `slices_Sort`.

Each of the 44 has the same four files:

| file | holds |
| --- | --- |
| `spec_<fn>.v` | `wp_<fn>_body` (all binders inside) + `Module Type <FN>` with one `Parameter` |
| `postulates_<fn>.v` | `Module Type <FN>_POSTULATES`, `Include`ing the **direct** callees' signatures |
| `proof_<fn>.v` | `Module <Fn>Proof (P : <FN>_POSTULATES) : <FN>.` — the Iris proof, sealed by the ascription |
| `link_<fn>.v` | `Module <Fn> := <Fn>Proof <Fn>Postulates.` plus the `Arguments` line |

**Shared, outside the module system** — these must stay transparent and
instance-visible, so they can never become Module Type fields:

| file | holds |
| --- | --- |
| `defs.v` | message-type/state constants, `state_w64`, `mtype_of`, `abs_msg`, `w32_ne` |
| `inv_storage.v` | `own_Storage`, `term_at`, and `is_Storage` — the client-supplied `Storage` interface contract |
| `inv_raftlog.v` | `own_raftLog`, `own_raftLog_at`, `own_raftLog_acc`, `log_indices_ok`, the `split_unstable` tactic |
| `inv_tracker.v` | `own_tracker`, `own_progress`, `own_inflights`, `visit_closure`, the pure quorum lemmas, `wp_ProgressMap_len`, `wp_tracker_progress_lookup` |
| `inv_logger.v` | `is_Logger`, `log_methods`, `wp_Logger__logf`, `solve_log_method` |
| `inv_misc.v` | `own_raft_misc` and `own_raft_misc_option` |
| `inv_raft_phys.v` | `own_raft_phys`, `own_raft_phys_at`, `step_func_of`, their intro lemmas, the `wp_log` tactic |
| `step_lemmas.v` | the `step_*` composition lemmas, `vote_resp_result`, `election_msg` |

Two kinds of `{{{ … }}}` legitimately remain outside a collection, and the
checker knows the difference: `wp_Logger__logf` and the three method specs
bundled inside `is_Storage` dispatch through `#(methods …)` on a
*client-supplied interface value*, so there is no Go function under
verification to specify; and `wp_ProgressMap_len` / `wp_tracker_progress_lookup`
are about a predeclared builtin (`go.len` on a named map type) and a
model-level map operation, not about Go functions either.

`election.v` is now only a `Require Export` of every `link_*.v` and
shared file, plus `Corollary raft_election_safety`. Requiring every link file
from there is load-bearing: `make ci` builds only what `new/should_build.v`
reaches, so a link file nothing re-exported would silently go unchecked.

**`Step` is one function with one spec.** Its three per-message-type branches
are internal lemmas — proof structure, not specification. Since 2026-09-17
they live in `proof_raft__Step_MsgHup.v`, `proof_raft__Step_MsgVote.v`
(which is a two-line case split over `proof_raft__Step_MsgVote_gt.v` and
`_le.v`) and `proof_raft__Step_MsgVoteResp.v`, each a functor over
`STEP_POSTULATES` with no `Module Type` of its own, so that `make -j` checks
them in parallel; `proof_raft__Step.v` instantiates them and proves the one
triple in `STEP`. Only `proof_raft__Step.v` may `Require` a branch file. If
some function ever seems to want two specs, that is a signal to look harder,
not to add a second `Module Type`.

Full write-up, including what is still `Admitted` and in what order to attack
it, is in [raft-election-refinement.md](raft-election-refinement.md).
