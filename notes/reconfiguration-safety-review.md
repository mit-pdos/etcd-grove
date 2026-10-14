# Adversarial review of the reconfiguration paper proof (2026-10-14)

The paper proof is `notes/reconfiguration-safety.md` (stage B1, `bfa867336`). This review read it
against the Go code at the pinned revision (`40f8be730b18`; a scratch copy, file:line below is
`raft.go` unless named) and tried to break each claim. This is parallel task 3 of
`notes/parallel-work.md`. No Lean file was touched.

## Verdicts, most severe first

| # | Claim (section of reconfiguration-safety.md) | Verdict |
|---|---|---|
| 1 | Read index at every configuration (8) | **False for the code**: the single-voter shortcut. A Go counterexample, a new issue, a fix |
| 2 | A node added later is unpromotable until it has a snapshot or the bootstrap prefix (0, 4.12) | **False** when `c0` is set by an index-0 `ConfState`, which `MemoryStorage` explicitly supports. A Go counterexample, a new issue |
| 3 | The decoder `dec` is a function of the entry (1) | **Gap** (scope): etcd's application changes the decoded change depending on the prefix |
| 4 | Scope A1/A3: what the application must do | **Gap** (statement): in log order, once per entry, compaction and snapshots at most `applied` |
| 5 | Winners table, `win_fresh`, ES (5) | **Holds**, gap 2's repair included; the Go re-vote rule is why the `d` branch is real |
| 6 | Commit-fact witnesses and their well-foundedness (2, 4.7, 6) | **Holds** |
| 7 | Generalized `lc_core` (7) | **Holds**; one step should be written out (below) |
| 8 | Read index with joint quorums, apart from #1 (8) | **Holds** |
| 9 | Snapshots and compaction, `base > applied` (4.8, 4.10) | **Holds** at synchronous storage, given #4 |
| 10 | Pre-vote and `MsgTimeoutNow` campaigns (4.1) | **Holds** |
| 11 | Auto-leave (4.4, 4.9) | **Holds** (a liveness remark) |
| 12 | A leader's step-down on removal (4.11) | **Holds**; two notes for the ghost (pending reads survive it; a demoted leader can still propose) |
| 13 | Learners, demotion, campaigning with a stale configuration (4.2, 4.12) | **Holds** |
| 14 | Restarts with persisted state | Out of scope (as the proof says); one more precondition to add when they come in |

Counterexamples (Go tests, in package `raft`; each passes by asserting the violation):

- `issues/raft-conf-lag-model/readindex_singleton_test.go`: two stale reads,
  `issues/raft-readindex-singleton-stale.md`; the fix `readindex-singleton-fix.patch` makes both
  tests fail (no stale read) and leaves `go test ./...` passing otherwise.
- `issues/raft-conf-lag-model/joiner_empty_confstate_test.go`: two different entries committed
  at index 3 with faithful applications (A1 holds), `issues/raft-joiner-empty-confstate.md`.

Neither breaks the paper's core argument (I1-I3, `W`, the table, the case analysis). #1 is a
code path the argument does not model, and #2 contradicts a scope claim. Both should be settled
in B2's scope before the model is fixed.

## 1. Read index: the single-voter shortcut (section 8). False for the code

Section 8 assumes that a leader answers a read only after a quorum of its configuration has
acknowledged a heartbeat sent after the request arrived, and only once the leader's commit is at
an entry of its term. `stepLeader`'s `MsgReadIndex` (`raft.go:1341-1348`) does neither when
`r.trk.IsSingleton()` (`tracker/tracker.go:160-162`: one incoming voter, no outgoing half). It
answers at once with `raftLog.committed`, before the `committedEntryInCurrentTerm` check
(`1350-1355`), and it does not check that the voter is `r.id`. At a fixed voter set this is
sound: the only voter is the leader, and every commit is its own. That is why the static
proof's premise `1 < size cfg` could exclude the path (STATUS, "Read-index"). Once
configurations change, both assumptions fail:

- **New leader, commit index behind.** `{1,2}` becomes `{1}`. Node 1 learns that the removal is
  committed but not that the next entry `x` is. It wins alone, and before its first `Advance` as
  leader a `ReadIndex` gets index 2. `x`, at index 3, was committed and applied by node 2 before
  the read.
- **Removed leader.** Node 2, removed but still leader (`StepDownOnRemoval` defaults to false,
  `1986-1994`), sees `IsSingleton()` for configuration `{1}` and answers every read from its own
  commit index, with no confirmation at all. Meanwhile node 1 leads term 2 and commits `y`.

Both execute in `readindex_singleton_test.go`.

**What B2/B6 should do.** Either keep a premise that rules out the shortcut, or prove the fixed
code. Under reconfiguration the premise cannot be a local premise of `raft.Step`: the caller
does not control the configuration. It becomes a restriction on the run: "no configuration that
a leader holds when a `MsgReadIndex` arrives is a single incoming voter with no outgoing half".
Since the configurations are `C_j`, that is a property of the committed log. With the patch
(the shortcut moved into `sendMsgReadIndexResponse`, after `committedEntryInCurrentTerm`, and
only when the voter is `r.id`), the shortcut is a degenerate confirmation: the leader is a
`JQuorum` of `{r.id}` by itself, and its commit is at an entry of its term. Section 8's argument
then applies with `Q = {L}`, and the patched path can be modelled as `readFwd` plus an immediate
`readState`.

Liveness aside: reads that are unconfirmed when the configuration shrinks to `{L}` wait for a
heartbeat response that may never come (no other node, or only removed ones). `maybeAdvance`
(`read_only.go:79`) is called only from `MsgHeartbeatResp`. This affects liveness only.

## 2. Nodes added later (sections 0 and 4.12). False as stated

Section 0 says that every node starts from `c0` and the same initial log. It also says: "a node
added later starts with an empty configuration and log and is unpromotable until it has applied
a snapshot or the bootstrap prefix". Section 4.12 repeats the second claim. The second claim
assumes that `c0` is the fold of a bootstrap prefix of the log (`RawNode.Bootstrap`'s conf
entries). `MemoryStorage.ApplySnapshot` (`storage.go:211-219`) explicitly supports the other
bootstrap: an index-0 snapshot carrying only the `ConfState`. Then the log starts at index 1 with
no trace of `c0`. The leader's first index is 1, so it catches a new node up by `MsgApp` from
index 1 and never by snapshot. The new node folds the log's conf changes onto **its empty
configuration**. After `add 4` its configuration is `{4}`: it is promotable, has no unapplied
conf change, and wins on its own vote. `joiner_empty_confstate_test.go` commits `x` and `""` at
index 3 this way, with every application faithful.

This repository's own harness does exactly this. In `leaderlag_test.go`, node 4 ends with
configuration `voters=(4)` (checked by a log line added in the scratch copy). The test's
violation stands: node 3 has the right configuration, and node 4 only votes. Its control claim,
that applying before `Advance` makes the violation go away, holds only for its schedule, in
which node 4 never campaigns.

**Repair (scope).** Section 0 should fix one of these setups:

- `c0 = cfgFold dec ∅ (P.take b)` for a bootstrap prefix of `b` conf entries
  (`Bootstrap`/`StartNode`; etcd's case, `server/etcdserver/bootstrap.go:581-583`);
- every node, including one added later, starts with `c0` as its `ConfState` (the proof's
  `cfgFold dec c0` then applies to it unchanged);
- the bootstrap snapshot has index ≥ 1, so a new node can only be caught up by snapshot
  (`bootstrap.go:25-29`'s recommendation).

Section 4.12's "a node whose configuration is not yet `cfgFold dec c0 _` neither campaigns nor
leads" is then true in each case. In the first two the node's configuration is always
`cfgFold dec c0 (log.take a)`, possibly with `id ∉ voters`. In the third it is empty until the
snapshot. The Lean model (`Cfg`) should carry the choice as a premise on the initial state.

## 3. The decoder (section 1). Gap

The paper takes `dec : Entry → Option CCOp`, "a function of the entry", and A1 has the
application pass `dec e` to `ApplyConfChange`. etcd's application does not do that.
`EtcdServer.applyConfChange` (`server/etcdserver/server.go:2001-2007`) validates the change
against its membership store, and if validation fails it calls `ApplyConfChange` with
`NodeId = raft.None`. `confchange.Changer.apply` skips a zero id
(`confchange/confchange.go:152-157`: "etcd replaces the NodeId with zero if it decides
(downstream of raft) to not apply a change"). The applied change is therefore a function of the
committed prefix, through the membership state, and of the entry.

Nothing in the argument needs `dec` to ignore the prefix. Every node applies the same committed
entry at the same prefix, `fold_adjacent` needs only that each step is a `ccApplyM` step (a
no-op is one: `Simple` with nothing changed, symmetric difference 0), and `j` counts conf entries,
not configuration changes. **Repair**: make `dec` take the prefix (`dec : List Entry → Entry →
Option CCOp`, `cfgFold` passing the prefix), or say in A1 that the scope is applications that
pass the entry's own change. The first is more general and costs nothing in `CfgOverlap.lean`'s
proofs: they are generic in `dec`.

## 4. What A1 and A3 must say (section 0). Gap in the statement

The argument uses more of the application than A1 and A3 state:

- `ApplyConfChange` is called for the committed conf entries **in log order, exactly once
  each** (Cfg: "`a` moves past the next conf entry"). Calling it twice for one entry, or for
  something that is not a committed entry, is outside the scope.
- **Compaction and snapshots at or below `applied`**. Cfg's "a leader, candidate or
  pre-candidate has ... `base ≤ applied`" is not raft's to keep:
  `MemoryStorage.Compact`/`CreateSnapshot` check only `lastIndex`. Above `applied`,
  `hasUnappliedConfChanges` scans compacted entries and `Panicf`s (`1013`). Also, A3's "the
  snapshot's `ConfState` is the configuration at its index" needs the snapshot index to be the
  one whose configuration the application passes. etcd snapshots at its applied index, with the
  `ConfState` of the last `ApplyConfChange`.

## 5. Winners table, `win_fresh`, ES (section 5). Holds

- **Configuration fixed from campaign to win** (4.1). Checked. The candidate's commit does not
  move: `stepCandidate`'s `MsgApp`/`MsgHeartbeat`/`MsgSnap` make it a follower first
  (`1674-1682`), and messages of lower terms are ignored (`1120-1185`). `applied` only grows,
  so `(applied', commit] ⊆ (applied, commit]` holds no conf entry. `restore` refuses a
  non-follower (`1853-1864`); its defensive `becomeFollower(r.Term+1)` is unreachable, since
  `stepCandidate` turns the node into a follower before calling `handleSnapshot`. Under A1 the
  only `ApplyConfChange`s are for entries in `(applied, applying]`, none of them conf entries.
  `TallyVotes` reads `trk.Config.Voters` at the same configuration as at the campaign.
- **Case `|j_c - j_c'| ≤ 1`**. `isVote_agree`: a node grants at most one `MsgVote` per term
  (`canVote`, `1201-1209`; `Vote` recorded at `1243`, persisted with the `HardState`). Pre-votes
  are not recorded.
- **Case "table's winner older"**. Checked step by step. `k_c ≥ p_{j_c'+2}` holds because
  `c`'s committed prefix has `j_c ≥ j_c'+2` conf entries. The witness of `c`'s campaign record
  has index `j_c'+1`, adjacent to `j_c'`. `lc_adj(T, c', w)` puts `p_{j_c'+1}` and `p_{j_c'+2}`
  into `F0_c'`, and both are `> k_c'` (`F0_c'.take k_c'` has `j_c'` conf entries): against I1 at
  `c'`'s campaign.
- **Case "new winner older"** (gap 2). The repair is needed, and the Go code shows why. A voter
  re-grants a vote it already cast (`r.Vote == m.From`, `1201`) even after learning of a leader
  (`lead ≠ None`). Its log at the re-vote can be a log of `c'` at `T` truncated to entries of
  terms `< T`: `c'`'s `MsgApp` may carry only the old part of `F0_c'` without its empty entry
  of term `T`. Such a log passes the up-to-date check against `c` (last term `< T`). So the `d`
  branch is open, and closing it with `lc_core(T, c', w)` is right: `w`'s term is `< T`, and
  `c'`'s logs extend `F0_c'`. Also checked: `lc_core(T, c', w)` meets only `j_c' ≥ j_w + 1`, and
  its far case uses `w`'s at-most-one, which `cqW` stores. No circularity: `lc_core(T, c')` uses
  ES of the table without `c`, and `c` is added only after the contradiction.
- One wording point: in 5 and 7, "`lc_core`" and "`lc_adj`" are statements about a table entry
  and *any* commit fact of a smaller term, whenever it was created. A stale leader of term
  `t < T` can commit after `T`'s winner won; the ack-before-vote argument does not care when.
  B4 should state them that way (as invariants of the table, not facts frozen at win time),
  since section 8 uses `lc_core(t, ldr_t, w_L)` for a `w_L` created long after `ldr_t` won.

## 6. Commit-fact witnesses and well-foundedness (2, 4.7, 6). Holds

- **The witness construction at commit** (4.7). Checked against `maybeCommit` (`773-777`,
  `log.go:453-462`: commits `trk.Committed()` only if its term is `r.Term`). The new conf
  positions in `(commit, n]` number at most one (I3(b), with `commit ≥ applied`), each is `> a`
  (since `a ≤ applying ≤ commit`), and no conf entry lies in `(a, p)` (it would be a second one
  above `applied`). So `confCount (G.take a) = confCount (G.take (p-1))`, and the fact is its own
  witness for `p`.
- **Well-founded**: a witness's `a' < p ≤ a`, a strict decrease on `Nat`. Also checked: a
  witness's own witnesses are at positions `≤ a' < p`.
- **`W` is node-local** (gap 5). A node's commit moves only in these places: `maybeCommit` at a
  leader; `maybeAppend` (`log.go:107-129`, `min(m.Commit, lastnewi)`) and `commitTo(m.Commit)`
  for a heartbeat (`1822-1825`; `m.Commit = min(pr.Match, committed)`, `sendHeartbeat`,
  `692-707`), both from the leader of its term; `restore` (`log.go:466`, commit set to the
  snapshot index) and the fast-forward `commitTo` (`1900-1907`), both from an `MsgSnap` of its
  term. The snapshot's index is at most the sender's `applied`, which is at most its commit, so
  the sender's `W` covers it. Nothing else (`loadState` is a restart). The statement is right.
- **I1 for `MsgApp`** (4.5). Checked the three sub-cases against `maybeAppend`/`findConflict`
  (`log.go:107-178`). If both conf positions are `≤ lastnewi`, the sender's slice gives `p1 ≤
  m.commit` and `p1 < p2 ≤ lastnewi`. If `p2 > lastnewi`, no truncation happened (a conflict
  replaces everything above it and leaves nothing beyond `lastnewi`), so the log is unchanged.
  A conflict at or below `committed` panics (`log.go:118-119`), so `log.take a` never changes.
  The leader's side: a second conf entry is proposed only when `pci ≤ applied ≤ commit`, and
  every `MsgApp` built after that carries `m.commit ≥` the first one (`m.Commit =
  raftLog.committed`, `649-656`).

## 7. Generalized leader completeness (section 7). Holds

All three cases were re-derived. One step should be written out in B5: in the far case
`j_c ≥ j_m + 2` with `n > k_c`, "both `> a`" needs `a < p_{j_m+1}`. That follows from
`confCount (G.take a) = j_m` and `G.take k_c = P.take k_c`: if `a ≥ p_{j_m+1}` then `G.take a`
has more than `j_m` conf entries. In the case `j_c ≤ j_m - 2`, `p_{j_c+2} ≤ a` holds because
`G.take a` has `j_m ≥ j_c + 2` conf entries. Also checked: the witness's agreement "`G'`
agrees with `G` up to `p`", plus log matching from `(t_w, n_w)` with `n_w ≥ p`, does put
*both* `p_{j_c+1}` and `p_{j_c+2}` into `F0`, since `p_{j_c+1} < p_{j_c+2} = p`.

## 8. Read index with joint quorums, apart from #1 (section 8). Holds

- The confirmation quorum is taken at confirmation time, at the configuration of that moment:
  `maybeAdvance(r.trk.Voters)` runs on each `MsgHeartbeatResp` (`1590-1597`) and uses
  `JointConfig.CommittedIndex` over the acknowledged positions. Acknowledgements from non-voters
  are recorded but not counted, and the leader's self-acknowledgement (`2143`) counts only if
  it is a voter. An acknowledgement of position `p` comes from a heartbeat whose context was
  `heartbeatCtx()` at send time (`read_only.go`), so it answers a heartbeat sent after request
  `p` arrived. This matches "a quorum `Q` of `C_{j_r}` (`L`'s configuration then)".
- The three cases were re-derived. `j_r ≥ j_m + 2` (gap 4's repair) is right; it needs only the
  doom fact's at-most-one and `lc_core` at the doom term `t` (see the wording point in 5). In
  `j_r ≤ j_m - 2` with `t_w > T`, "the witness predates the doom fact" is what makes `w`'s
  acknowledgements precede the arrival. That is true because `cqW` stores its witnesses at
  creation. Two conf entries above `a_L ≥ applied` contradict I3(b) at confirmation.
- `pendingReadIndexMessages` (`1352-1354`, released at `2115-2132`) is never cleared, not by
  `reset`, not by any step-down (see 12). A request postponed at term `T` can be answered by the
  same node as leader of a later term, after that term's first commit. That is safe (the later
  commit covers everything committed before the arrival), but the ghost for postponed requests
  must not tie them to `T`. The static proof already meets this through `becomeFollower` at a
  higher term; B6 should check it still holds.

## 9. Snapshots and compaction (4.8, 4.10). Holds, given #4

- `restore` (`1849-1931`) refuses: an index `≤ committed`; a non-follower; a recipient that is
  not in the `ConfState` (`1866-1897`, so a node is never restored into a configuration without
  itself). It fast-forwards the commit when the log has the snapshot's entry (`1899-1907`): the
  configuration is unchanged, `a` unchanged, commit grows; the paper's "snapFastfwd: commit only"
  is right. Otherwise: commit `= index`, the configuration from the `ConfState`, and a pending
  snapshot (`unstable.snapshot`, `log.go:287-289`).
- While a snapshot is pending, the node is unpromotable (`promotable`, `1934-1937`) and gets no
  committed entries (`nextCommittedEnts`, `log.go:223-225`). At synchronous storage, `Advance`
  steps the `MsgStorageAppendResp` carrying the snapshot, and `appliedSnap` (`764-768`) does
  `stableSnapTo` and `appliedTo(index)` together, so `applied = base = a` before the node is
  promotable again. A second `MsgSnap` before that replaces the pending snapshot and the
  configuration together (`a :=` the new index); nothing breaks.
- The asynchronous-storage window of 4.10 is real as described (`stableSnapTo` and
  `appliedSnap` come from different responses). It is out of scope.

## 10. Pre-vote and `MsgTimeoutNow` (4.1). Holds

- Pre-vote: `hup` checks `promotable` and `hasUnappliedConfChanges` (`968-985`). After a pre-vote
  win, `stepCandidate` calls `campaign(campaignElection)` directly (`1688-1689`), and `campaign`
  only warns if the node is unpromotable (`1021-1025`). Between the two, the pre-candidate's term,
  log and commit are fixed: any `MsgApp`/`MsgHeartbeat`/`MsgSnap` of its term makes it a follower
  (`1674-1682`), and any message of a higher term does too (`1100-1118`, except a granted
  `MsgPreVoteResp`, which does not touch the log). Its configuration is fixed by the argument of
  5. So the guard and `promotable` still hold at the real campaign, and `(F0, k)` is the log and
  commit of the `hup`.
- `MsgTimeoutNow`: a follower calls `hup(campaignTransfer)` (`1745-1750`), with the same checks.
  A candidate or pre-candidate ignores it (`1699-1700`), and a leader drops it (no case after the
  `Progress` lookup). `campaignTransfer` only bypasses the lease (`1087-1098`). Up-to-date checks
  and quorums are unchanged.

## 11. Auto-leave (4.4, 4.9). Holds

`appliedTo` (`735-761`) proposes the empty `ConfChangeV2` when the configuration is `AutoLeave`,
the node leads, and `newApplied ≥ pci`; it goes through `stepLeader`'s checks (`1312-1333`).
Checked that no double leave arises under A1. Say a new leader inherits a joint `AutoLeave`
configuration and its log already has the leave entry `q` above `k`. Then `pci = lastIndex ≥ q`,
and by the time `applied ≥ pci` the application has applied `q` (A1), so the configuration is no
longer joint and nothing is proposed. The leader's joint/leave validation also matches what the
entry meets at apply time. Every earlier conf entry of the leader's log is `≤ pci ≤ applied ≤
a`, so `trk.Config` at `a` is the fold of the prefix just before the new entry. The only
mismatches are the `Changer` errors already filed (`raft-joint-empty-transition-panic.md`).

Liveness remark: a removed leader without step-down drops every proposal (`1285-1290`), the
auto-leave included. But a joint configuration always contains its leader in a half or among the
learners-next, so the leader is not removed while the configuration is joint. Nothing to do.

## 12. Step-down on removal (4.11). Holds; notes for the ghost

- `switchToConfig` (`1967-1994`): with `stepDownOnRemoval`, a removed or demoted leader calls
  `becomeFollower(r.Term, None)`. `reset` keeps `Vote` (same term), so it votes again in `T` only
  for itself, and its next campaign is at a higher term, from which it is unpromotable anyway.
  `pci` resets to 0 and `readOnly` is renewed (`779-812`), but `pendingReadIndexMessages` is not
  (see 8).
- Without step-down, a *demoted* leader (now a learner) still has a `Progress` and so still
  accepts proposals, conf changes included (`1285`). Its own acknowledgement no longer counts.
  I3 and the propose rule do not need it to be a voter, so 4.11's "nothing in the argument needs
  it to be a voter" is right for demotion too. A *removed* one drops proposals.
- As 4.11 says, the known-leaders ghost (`klOk`) must allow a leader of `T` to become a follower
  of `T`. Nothing else in the argument assumes that leadership lasts to the end of the term.

## 13. Learners, demotion, stale configurations (4.2, 4.12). Holds

- Votes ignore the voter's configuration (`1199-1253`; the comment at `1210-1227` explains
  why). `TallyVotes`/`VoteResult` count only voters of the candidate's configuration. A
  learner, a node with an empty `Progress`, and a node with a pending snapshot are unpromotable.
- Demoting a voter in `Simple` is a symmetric difference of 1, so the quorums overlap
  (`simpleM_overlap`). Through a joint configuration (learners-next), the node stays in the
  outgoing half until the leave.
- A node that campaigns with a stale configuration (it never learned a later change) is the case
  `j_c ≤ j_m - 2` of 7, and the voters' up-to-date checks are what defeat it. Tried by hand on
  "remove 3, then add 4, with node 3 unaware": the witness of `p_2` (index 1) overlaps `C0`'s
  quorums, as the argument needs. No counterexample.
- A node in the outgoing half only can campaign and win, since a joint quorum includes the
  outgoing majority. It then leads at the joint configuration, and step-down or auto-leave (11)
  follows. This is covered.

## 14. Restarts (out of scope)

When restarts come in, there is one more precondition next to A2 (atomic persistence). `newRaft`
(`437-485`) restores the configuration from `InitialState`'s `ConfState` and sets `applied :=
Config.Applied` (`482-484`) without re-applying the conf entries in between.
`MemoryStorage.InitialState` returns the *snapshot's* `ConfState`. If an application restarts
with `Applied` past a conf entry newer than its stored `ConfState`, its configuration is behind
`applied`: the window of `raft-advance-before-applyconfchange.md`, opened at restart. Noted in
`issues/raft-joiner-empty-confstate.md` ("Related"); not reproduced.

## Model runs

`issues/raft-conf-lag-model/model.py` was run as random walks (`WALKS=20000`, 60 steps each)
with `4 3 faithful 4 8 3 2 joint`, `5 3 faithful 4 8 3 2 joint` and `4 3 lag 4 8 3 2 simple`. No
violation in any of the three, not even in `lag` mode, whose known counterexamples need specific
schedules of about 22-26 steps. The walks are therefore no evidence for the faithful mode (see
parallel task 5). The model does not have #1 (it has no reads) or #2 (every node starts from
`INIT`).
