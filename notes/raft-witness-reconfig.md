# The witness across reconfiguration (W5 analysis, 2026-10-20)

**Correction (2026-10-20, W5-Lean).** The "`K = C(T, s)` joint" case below is wrong for the code
as it was (through fork `9ed005d46`): `OneLessThanQuorumInReplicationSet` sent the witness of both
halves an entry when only one half had it in its replication set, so the witness's write was
backed by that half's acknowledgements alone while it checks votes against the incoming half's
set. With both halves of odd size (two changes in one joint transition, which the model's `enter`
could not make) a candidate lacking a committed entry wins with the witness's vote:
`issues/raft-witness-joint-oltq.md`, fixed in the fork at `99cb9e2d9` (the witness of both halves
is sent an entry only when both halves include it). With the fix, every witness acknowledgement is
backed by quorum−1 acknowledgements of each half's replication set, and the case holds by the
static count in the incoming half. The model has `enter2` (joint changes of two adds) and `fixa`
since; the directed trace `traces/joint-oltq.txt` violates leader completeness without `fixa` and
is cut off at the witness write with it.

Question: is the witness design of the fork `raft-witness-goose-lean` (`9ed005d46`; raft#168 with
the fixes of `notes/raft-witness-vs-pr168.md`) safe when the configuration changes -- simple and
joint changes, adding or removing regular voters while the witness stays, adding or removing the
witness, the witness in one half of a joint configuration only? The static argument
(`notes/raft-witness.md`, "Why it is safe") and the Lean proof (W2) are for a fixed
configuration.

**Answer: yes, in raft's faithful mode** (the application calls `ApplyConfChange` for each conf
entry before `Advance`, `notes/reconfiguration-safety.md`'s precondition), **with no Go change**:
the model checker finds no violation (below), and the argument of the next section extends the
static one. It rests on three things raft already does and one the fork does:

1. raft's `hasUnappliedConfChanges` guard: a node with a committed, unapplied conf entry does not
   campaign;
2. the commit index carried by every `MsgApp` (`Commit: committed`), so a node that holds an
   entry also knows every index the sender had committed when it sent it (and `committed` never
   decreases);
3. one conf change at a time (`pendingConfIndex`, `DisableConfChangeValidation` off -- a premise
   of the existing proofs, `ownRaftPhys`'s `HnoCCV`);
4. (the fork) a leader starts a new subterm whenever it applies a change while a witness is
   involved (the old or the new configuration has one, or its epoch does: `switchToConfig`).

Outside the faithful mode the witness inherits raft's known reconfiguration failures (the lagging
and crash modes of `notes/reconfiguration-model-check.md`); with the guard dropped
(`lag-cand`) plain raft already fails, so nothing witness-specific is claimed there.

## The argument

Notation as in `notes/raft-witness.md`: `C(T, s)` is the configuration the leader of `T` had
applied when it started subterm `s` (its epoch's), `cidx(T, s)` the index of the last conf entry
of that configuration, `RS(T, s)` the replication set (a half per configuration half), `H` the
regular members of a half's replication set that acknowledged the entry the witness was sent, `G`
the votes the candidate had been granted when it asked the witness (the request's responders).

**(Cfg) A candidate whose last entry is of `(T, s)`, `s ≥ 1`, has applied `C(T, s)` or the
configuration one conf entry after it.**
- *At least `C(T, s)`*: every node holding an entry of `(T, s)` has `committed ≥ cidx(T, s)`. The
  leader created the entry after applying `cidx(T, s)`, so its `committed` was at least that
  then; a node receives an entry only in a `MsgApp` whose `Commit` is the sender's `committed`,
  and the receiver's commit becomes at least `min(Commit, lastnewi)` with `lastnewi` past the
  entry; by induction over the nodes the entry passed through (the sender holds it too), and
  `committed` never decreases. With (1), the candidate has applied every conf entry up to
  `cidx(T, s)`.
- *At most one entry more*: the candidate's log is a prefix of the leader of `T`'s log ending in
  subterm `s` (log matching). A conf entry proposed in subterm `s` is applied by the leader before
  the next can be proposed (3); its application starts subterm `s + 1` (4); so the candidate's log
  holds at most one conf entry past `cidx(T, s)`, and no conf entry lies between `cidx(T, s)` and
  the start of subterm `s` (the leader proposes the next change only after applying the previous).

**(Count)** For configurations `C` and `C'` differing by one member, `q_C + q_C' > |C|`
(computed in both parities), so `(q_C - 1) + (q_C' - 1) > |C| - 2 = |RS ∖ W|` when the replication
set excludes a regular voter: two such sets inside `RS ∖ W` meet.

**Leader completeness, the witness case.** As in the static case, the case the witness adds is a
vote of the witness whose stored `(lt, ls)` equals the candidate's last `(T, s)` (the other cases
-- newer term, later subterm -- do not involve the configuration). The witness checks
`G ⊆ rsin`, the stored *incoming* half of `RS(T, s)`. By (Cfg) the candidate's configuration `K`
is `C(T, s)` or one step past it:

- `K = C(T, s)`, simple: the static argument (`G` has `q - 1` of `K` by the readiness check).
- `K = C(T, s)` plus a simple change (add or remove a regular voter or the witness): if `K` has no
  witness, the candidate does not ask one. Otherwise readiness gives `|G| ≥ q_K - 1` within
  `RS(T, s)`'s incoming half, and `H` (the witness's write needs `q_C - 1` of that half) meets
  `G` by (Count).
- `C(T, s)` simple, `K` the joint configuration entering from it (`K = C_new && C(T, s)`):
  readiness asks a witness only when the outgoing half -- `C(T, s)` -- needs at most one vote
  (`v2 ≤ 1` in each branch of `getWitnessVoteRequestReadiness`; with the witness only in the
  outgoing half, `v2 == 1`), so `G` has `q - 1` of `C(T, s)`, inside `rsin = RS(T, s)` (the
  incoming set of the simple configuration): the static count. If the witness is in the
  incoming half only (added by the joint change), it is not `C(T, s)`'s witness, so it never
  stored `(T, s)`; the outgoing half then needs a regular majority of `C(T, s)`, which meets the
  commit's quorum of `C(T, s)` in a regular voter.
- `C(T, s)` joint (`C_new && C_old`), `K` after `LeaveJoint` (`C_new`): if the witness is not in
  `C_new` the candidate does not ask it; otherwise `G` has `q - 1` of `C_new` and `rsin` is
  `RS(T, s)`'s incoming half -- `C_new`'s -- where the witness's write had `q - 1` acks: the
  static count. (This is the case that needs the witness to store the *incoming* set.)
- `K = C(T, s)` joint: a commit of the joint configuration needs both halves, and so does the
  election. The witness's write had `q - 1` acks of the incoming half's replication set,
  readiness gives the candidate `q - 1` of the incoming half (or the whole incoming majority
  without the witness, in which case the incoming majorities meet in a regular voter): the static
  count in the incoming half.

In each case `G ∩ H` holds a regular voter that acknowledged the entry and voted for the
candidate: the regular case of Leader Completeness (`lc_adj_gen`), as in `lc_wit`.

**Commit with a stale witness acknowledgement.** The witness's `Match` survives configuration
changes (its `Progress` is kept), so a leader may count it in a later configuration's quorum, but
only for indices at or below an acknowledged one, which were committed when acknowledged.

**Two witnesses** (`Witnesses = [W2, W1]`, replacing the witness through a joint configuration):
`sendAppendToWitness` sends both `ReplicationSet[0]` (incoming) and `[1]`, and the witness stores
the incoming one, so the outgoing witness `W1` checks responders against `C_new`'s set, not its
own half's. Safe all the same: in the joint configuration the incoming half protects (a commit
and an election both need it, through `W2`'s own check or a regular majority), and after
`LeaveJoint` `W1` is not a voter. The model has one witness identity; this case is argued only.

## The model checker

`issues/raft-witness-reconfig-model/` (`model.py`, `README.md`, logs in `runs/`). Validated: the
witness vote rule without its replication-set check (`norscheck`) fails leader completeness at
depth 8 (BFS) and in random walks; without raft's campaign guard (`lag-cand`, no witness) the
walks find raft's known lagging-candidate violation.

Runs (faithful mode; `w0`: the witness in the initial configuration; `wops`: it may be removed
and re-added; `joint`: joint changes):

| Run | Arguments | Result |
|---|---|---|
| `s1-static-bfs` | `2 2 faithful 3 5 0 2 w0` (2 regular + witness, no conf change) | exhaustive: no violation, 1.43·10^6 states, diameter 27 |
| `v1-norscheck-bfs` | the same, `norscheck` (validation) | leader completeness violated at depth 8 |
| `v2-nowitness-lagcand-walks` | `4 3 faithful 6 10 4 3 joint lag-cand`, no witness (validation) | leader completeness violated (walk 2509, step 44) |
| `r1-simple` | `3 2 faithful 3 5 2 1 w0`: simple changes, the witness stays | complete to depth 13 (1.4·10^7 states seen), no violation; then out of memory (16 GB) |
| `r2-wops` | `3 2 faithful 3 5 2 1 w0 wops`: the witness removed / re-added | complete to depth 10 (1.9·10^6), no violation (stopped for CPU) |
| `r3-joint` | `3 2 faithful 3 5 1 1 w0 joint wops` | complete to depth 12 (1.4·10^7), no violation; then out of memory |
| `r4-joint2` | `3 2 faithful 3 6 2 0 w0 joint wops` | complete to depth 11 (3.3·10^6), no violation (stopped for CPU) |
| `w1-walks-4reg` | `4 3 faithful 6 10 4 3 w0 joint wops`, 150 000 walks of ≤ 100 steps | 1.49·10^7 steps, no violation |
| `w2-walks-5reg` | `5 4 faithful 6 11 4 3 w0 joint wops`, 30 000 walks of ≤ 100 steps | 2.98·10^6 steps, no violation |
| `w3-walks-4reg-deep` | `4 3 faithful 7 12 5 3 w0 joint wops`, 100 000 walks of ≤ 120 steps | 1.19·10^7 steps, no violation |
| `t1-joint-oltq-replay` | `REPLAY=traces/joint-oltq.txt`, `4 2 faithful 3 12 1 2 w0 joint enter2` | leader completeness violated (the bug of `issues/raft-witness-joint-oltq.md`) |
| `t2-joint-oltq-replay-fixa` | the same, `fixa` | the witness write is not enabled: the trace stops there |
| `w4-walks-enter2` | `4 2 faithful 4 12 3 2 w0 joint enter2`, 40 000 walks of ≤ 100 steps | see the run's log |
| `w5-walks-enter2-fixa` | the same, `fixa` | see the run's log |

The BFS depths are shallow (a witness write after a reconfiguration takes 10-14 steps), so the
exhaustive runs cover the first changes only; the walks reach the deep interleavings
(elections, conf changes, replication-set changes, witness writes from the store and the
caches, joint configurations, the witness removed and re-added) but are not exhaustive. A
Go-checker transcription (as `issues/raft-conf-lag-model/checker/` did for `model.py`) would push
the exhaustive bounds; not done.

What the model does not cover: two witness identities (the replaced-witness joint case,
argued above); pre-vote; snapshots (a candidate whose log ends at a snapshot reports subterm 0,
which can only make the witness refuse); the witness's `Lead` field beyond the vote rule's
`(vote == 0 && lead == 0)`; delayed messages (each witness request is processed at once, from the
store or the requester's cache, which may be stale; elections are atomic, as in `model.py`). A
delayed append to the witness is covered by the argument: a write needs a strictly newer
`(lt, ls)`, and `(T, s)` always comes with `RS(T, s)`.

## The Lean proof (W5, 2026-10-20, branch `raft-witness-w5`)

Done, in the protocol layer (`Proof/go_etcd_io/raft/v3/Protocol/`), with no new axiom or
`sorry`. The pieces, as the argument above uses them:

- **The rules** (`StepR`): the witness rules at the node's configuration (`newSub`, `sendWApp`
  with the witness one of its incoming voters, `askWitness` with `quorum - 1` granted votes of
  each half, `sendWPre`) and `applyConfWit`, the change a leader applies together with its new
  subterm (point (4) above); a plain `applyConf` at a leader needs a configuration without a
  witness. `propose` stamps the leader's subterm.
- **(Cfg), the leader's half** (`RInv.lf`): a leader past its first subterm has the subterm's
  configuration prefix `PState.scp` (ghost) = its full log's first `p0` entries, `p0` at most the
  commit index, and, when its configuration or the prefix's has a witness, no conf entry between
  `p0` and the configuration index (so the configuration is the prefix's: `lf_cfgAt`).
- **(Cfg), every holder's half** (`entWit`, in `ownRaftGhostR`'s `witR`): each entry of a node's
  full log past the first subterm has, when its subterm prefix's configuration has a witness,
  the prefix committed at the node's commit index (the "at least" half: `MsgApp` and `MsgSnap`
  carry the sender's `entWit`, the receiver's commit index covers the prefix) and at most one conf
  entry past the prefix up to the entry (the leader's `RInv.lf` and I3 at its appends,
  `entWit_leader_app`; log matching for a receiver, `appAccept_full`).
- **The campaign**: a witness vote request carries the campaign's `campDyn` and `entWit`
  (`wVoteReq`); `wJust` the acknowledged entry's configuration prefix and configuration.
- **(Count), the shape of one change** (`DynCfg.shape`, `fold_shape`, `ccApplyM_shape`): after at
  most one change, a half of the new configuration is at most one voter smaller than the old
  incoming half (simple: symmetric difference at most one; leaving a joint configuration: the
  same incoming half), or the outgoing half is the old incoming one (entering a joint
  configuration). With the fixed sending rule (quorum−1 acknowledgements of each half's
  replication set) and the readiness counts of each half, `wit_count_meet` gives the meeting
  voter.
- **Leader Completeness** (`lc_wit_gen`, `lc_wit`): the equal-`(term, subterm)` case reads the
  campaign log's last entry's `entWit`, so the campaign configuration `K` is at most one change
  after the acknowledged entry's `cA`; a half of `K` meets the acknowledgements in a regular
  voter. The cases where a quorum meets another only at the witness, in `lc_core` (adjacent),
  `lc_far_older` and `win_fresh`, go to `lc_wit`/`lc_wit_gen`; `voteJust_campDyn` reads a
  winner's campaign facts from the witness's vote too. `reWit_ok` admits the dynamic mode.

Not covered: crashes and restarts (the "at least" half of (Cfg) needs the restarted commit
index to cover the entries' prefixes; out of the faithful mode, as above), and two witness
identities (one `reWit`).
