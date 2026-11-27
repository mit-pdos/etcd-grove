---
upstream: none
checked: 2026-11-27
links:
  - etcd-io/etcd#22028 issue open: related, not this: the backend-ahead-of-WAL state the keep guard handles
blocks-proof: yes
---
# etcdserver (our fork's keep guard): a snapshot kept below the backend leaves raft's configuration at the snapshot's

**This is about our fork's keep guard, not upstream.** Upstream has no keep guard; see "Upstream"
below. The fork's `applySnapshot` keeps the backend when a leader snapshot's index `k` is at or below the
backend's consistent index `ci` (8aa40fd5c; in the pinned lineage as 47d6cdeeb; extended by a453b08a1,
branch `goose-lean-discardfix-ttlkeys-keepfix`). raft has installed the snapshot's configuration `C_k`.
The conf changes in `(k, ci]` are then replayed with `ApplyV2storeOnly`, so raft's `ApplyConfChange` is
never called for them. raft's tracker, `ep.confState` and the backend's stored ConfState stay at
`C_k` (plus later changes applied on top of it) until the member restarts. The cluster and every other
member are at `C_ci`. A member whose raft configuration misses two voter changes can be elected, and
can commit, with a quorum that is disjoint from a quorum of the real configuration.

**Why not an issue:** the code is only on our fork, never upstream. The stale state is shown by a unit
test at the `applySnapshot`/`apply` level. The whole crash schedule is an argument from code reading and
has not been run end to end.

## The gap (fork a453b08a1, raft v3.7.0 as in etcd's `go.mod`; the verified raft fork d2c16c5 agrees)

1. **Bootstrap.** At restart, raft's configuration is built from the backend's members at `ci`
   (`bootstrap.go:133-141`, `buildConfStateFromV3store`). The WAL replay skips raft for entries
   `≤ ci`: `apply` marks them `ApplyV2storeOnly` (`server.go:1993-1998`), and `applyConfChange` calls
   `s.r.ApplyConfChange` only under `ApplyBoth` (`server.go:2108-2114`). Raft is right after a plain
   restart, because it starts at `C_ci`.
2. **raft installs `C_k`.** A leader snapshot at `k`, with `raft.committed < k ≤ ci`, is accepted by raft's
   `restore` (`raft/v3@v3.7.0/raft.go:1860`), which switches the tracker to the snapshot's ConfState
   (`:1925`, `confchange.Restore`). The verified fork does the same switch later, at `appliedSnap`, on
   `Advance` (`raft.go:766-788` at d2c16c5). Either way raft's tracker is now `C_k`, older than `C_ci`.
3. **etcd keeps the backend** (`server.go:1077-1116`). `ep.confState` is set to `C_k`, and `ci` stays.
4. **raft re-delivers `(k, ci]`.** `raftLog.restore` drops every entry and leaves `committed = applied = k`.
   The leader sends `k+1…` in a `MsgApp`, because its log holds them: it compacts only to `applied -
   SnapshotCatchUpEntries`. They come back in `Ready.CommittedEntries`. `applyEntries` applies them,
   since `ep.appliedi = k`, but `apply` marks each `≤ ci` as `ApplyV2storeOnly`. raft's tracker changes
   only through `ApplyConfChange`: its own applied index moves at `Advance` whatever the entries are, and
   it never applies a conf change by itself. So the tracker stays at `C_k`. `beHooks.SetConfState(ep.
   confState)` (`server.go:2115`) writes `C_k` into the backend's meta beside consistent index `ci`.
5. **It persists until a restart.** Later conf changes `> ci` are applied by raft on top of the stale
   tracker. `ep.confState` is raft's result, and it goes into this member's raft snapshots
   (`CreateSnapshot(ep.appliedi, ep.confState)`) and its merged snapshots to followers
   (`createMergedSnapshotMessage`, `server.go:1013`). A merged snapshot at the backend's index takes its
   ConfState from the backend's meta when `replayConf` does not cover it (`snapshot_merge.go:49-58`),
   and that is stale too. A follower that installs such a snapshot above its own backend replaces its
   backend (its members are right) and restores raft to the stale ConfState. A restart heals a member,
   because bootstrap rebuilds raft's configuration from the members.

**Reproduction (state only):** `TestKeptSnapshotLeavesRaftConfStateStale` and
`TestReappliedConfChangesUpdateRaft` in
[`etcd-keepguard-raft-confstate-stale/snapshot_below_backend_confstate_test.go`](etcd-keepguard-raft-confstate-stale/snapshot_below_backend_confstate_test.go).
They were run on the fork's local branch `keepfix-confgap-repro` (ac60ac826, on a453b08a1; not pushed)
in `server/etcdserver`, with go1.27.3. The setup: a real `raft.Node`, a backend at `ci = 7` with members
1..5, bootstrap configuration 1..5, and a WAL at 3. The leader's snapshot at 5 has voters 1..3, and
entries 6 (add 4) and 7 (add 5) follow:

```
--- PASS: TestKeptSnapshotLeavesRaftConfStateStale
    member 1: leader of term 3 with votes {1,2}; cluster voters [1 2 3 4 5]; raft voters [1 2 3]
--- PASS: TestReappliedConfChangesUpdateRaft      (backend at 5: ApplyBoth, raft reaches 1..5)
```

The first test asserts these points. Raft re-delivers 6 and 7. raft's tracker, `ep.confState` and the
backend's meta ConfState are 1..3. On `Campaign` the member asks only 2 and 3 for votes, and it becomes
leader with 2's vote alone.

## 1. Safety

**What a stale tracker does.** raft uses its own tracker for the voters it asks (`campaign`), for the
votes it counts, for commit (`maybeCommit`), for ReadIndex quorums and for CheckQuorum. Voting does not
check the configuration, so other members grant votes to the stale member normally. Let `T` be the real
voter set and `S` the stale one.

- **One voter missing from `S`** (an add or a promotion in the window). A majority of `T∖{d}` and a
  majority of `T` always intersect: `⌊(n−1)/2⌋+1 + ⌊n/2⌋+1 > n`. Elections and commits stay safe. The
  missing member gets no replication from this member when it leads, which hurts liveness only.
- **One extra voter in `S`** (a removal in the window). The removed member is unreachable: it stops
  itself, the transport is rebuilt from the members (a453b08a1), and peers drop its messages. The stale
  member's quorums are a superset of real ones. Liveness only.
- **Two voter changes away from `T`**: quorums can be disjoint. For example, the window adds 4 and 5 to
  `{1,2,3}`. The stale member 1 is elected with `{1,2}` (2 of 3) while `{3,4,5}` (3 of 5) elects another
  leader. Under a partition `{1,2} | {3,4,5}`, both commit writes and acknowledge them to clients. When
  the partition heals, the higher term overwrites the other side's committed entries. Acknowledged
  writes are lost, and a follower that had applied them panics on the conflict ("conflict with
  committed entry"). This breaks raft's safety, and with it linearizability and durability.
- **Two members each one voter away, in different directions.** Two separate keep events can each leave
  one member stale. In `T = {1,2,3,4}`, member 1 may miss 4 and member 3 may miss 2. Their quorums,
  `{1,2}` of `{1,2,3}` and `{3,4}` of `{1,3,4}`, are disjoint. Each event needs only one conf change in
  its window.
- **Propagation**: a stale member's snapshots carry its stale configuration to the followers that
  install them (point 5), so a stale configuration can spread from one member to others. A restart
  heals each member.

**Reachability.** Three things are needed. (a) The member crashes with its backend ahead of its WAL
across a conf change. The follower applies before `Save` and sends its acks after it (`raft.go:274-322`);
the backend's batch commit lands during `Save`; this is shown for puts by
`TestBackendAheadOfWALAfterKill` in `etcd-crash-backend-ahead-snapshot-regress`. (b) After the restart,
a leader whose log is compacted above the member's WAL. (c) That leader's merged snapshot index, `max(
applied, ci)` of the leader, is below the conf change.

Two mechanisms constrain (c):

- The fork's leader wait (4d9282b0f): a leader whose `Ready` commits a conf change waits for its apply
  loop before `Advance`.
- raft's one-pending-conf-change rule (`raft.go:1326`, `pendingConfIndex > applied`), with the refusal
  to campaign over committed but unapplied conf changes (`:984`).

Together they mean the following:

- **One conf change in the window, one leader throughout:** possible. raft broadcasts the commit index
  `≥ j` in a `Ready` whose `CommittedEntries` stop before `j`, because they are capped at
  `MaxCommittedSizePerReady`, which is `MaxSizePerMsg`, 1 MiB (`raft.go:320`; etcd `raft.go:38`). That
  `Ready` has no conf change, so the leader neither waits nor stops `Advance`. Its apply loop, which
  can lag by up to 5000 entries, then merges the member's snapshot at a batch boundary `k < j`, while
  the crashed member had already applied `j`. With a single change in the window, the stale tracker is
  one voter off. That is not unsafe alone, but it is the building block of the two-member case above.
- **Two conf changes `j1 < j2` in one window:** a single leader cannot produce it. `j2` is proposed only
  after the leader's raft applied `j1`, so after its leader wait, so its etcd applied `j1`. Every later
  merge is at `k ≥ j1`. It needs a leader change between: a new leader is elected with its raft commit
  below `j1`, which the campaign check does not see. Its first commit then spans `j1` and `j2` in a
  size-capped `Ready` that stops before `j1`, and its apply lags at `k < j1`.
- **Compaction:** the leader's first index must exceed the member's WAL end. So the member's unsaved
  window, one `Ready`, must exceed `SnapshotCatchUpEntries` (5000 by default; tests set it lower).

Each condition is reachable on its own. The conjunction is improbable, but it is not excluded, so the
window can contain conf changes. A crash-form proof cannot rule them out, and the keep guard as it
stands is not provably safe. An end-to-end test would need coordinator-E's `keepguard/` integration
harness (crash images, held raft loops) plus failpoints to cap the leader's `Ready` and stall its apply.
It would help for (c); it was not attempted here.

**Upstream** (no keep guard), in the same scenario: `applySnapshot` replaces the backend by the
snapshot's (`ci := k`), and `(k, ci]` is re-applied with `ApplyBoth`. Each conf change is re-validated
against the backend at that point, which is the same deterministic state as at the original apply, so it
gets the same verdict. Valid ones go to `ApplyConfChange`, and invalid ones are applied with `NodeId =
None`. The cluster applied the same sequence to `C_k` in the same order, so each change is raft-valid
again. raft ends at `C_ci`: no configuration gap. What upstream does have:

- the backward move of the backend, not client-visible (`etcd-crash-backend-ahead-snapshot-regress`);
- coordinator-E's report that upstream panics under `ETCD_VERIFY` with "update of consistent index not
  advancing" (`schema/cindex.go:78`). That is a verification-mode check only, and I did not re-derive it.

I found no upstream-reachable safety bug here.

## 2. Options

| option | change | Goose | proof impact | verdict |
|---|---|---|---|---|
| (1a) replay each conf change in `(k, ci]` into raft | Per-entry validity is needed: blind replay diverges where etcd rejected a change. A rejected add of an existing learner would promote it in raft; a rejected add with a duplicate peer URL would add a voter. Validity can be recomputed only from the membership at `k`, which means reading the snapshot's `.snap.db` members and simulating `ValidateConfigurationChange` in memory over the window. About 100-150 lines, plus window state in `ep` | translatable (maps, JSON contexts) | a ghost membership track over `(k, ci]`, and an in-memory validator proved equal to the backend one | correct but the most code |
| **(1b) set raft to `C_ci` at the keep point** | In the keep branch, compute `C_ci` (`buildConfStateFromV3store(s.be)`) and bring raft from the snapshot's ConfState to it with one-voter `ConfChange`s (adds before removes, then learner moves), or one `EnterJoint` + `LeaveJoint`. Set `ep.confState` and `beHooks.SetConfState` to `C_ci`. It must run after raft's `Advance` of the snapshot's `Ready` (`applyAll` after `<-raftAdvancedC`), because the verified raft switches to the snapshot's configuration at `appliedSnap`, which would overwrite an earlier change. About 40 lines. This is the restart's own state (point 1): `(k, ci]` is then skipped for raft exactly as in any restart replay | translatable (sorted ID diff, a loop of `ApplyConfChange`) | needs the fact the crash-form restart already needs for `bootstrap.go:138`: a member may run at the configuration of a committed index ahead of its log. No new ghost track | **recommended** |
| (2a) reject the snapshot in raft | Etcd gives raft a floor (its backend's `ci`), and raft's `restore` refuses snapshots at or below it (it answers with its commit, and the leader retries). Liveness holds: the leader's merged index `max(applied, ci)` grows past the member's `ci` | a raft API change in the verified raft fork | changes `restore`'s spec and the raft proof; an API no upstream user wants | workable, but heavier than (1b) |
| (2b) fail-stop in etcdserver | In the keep branch, when the snapshot's ConfState differs from `C_ci`, exit (`lg.Fatal`). The restart heals: bootstrap rebuilds `C_ci`, and the WAL snapshot is already saved, so each further snapshot is strictly higher and the loop ends | 5 lines | an exit is a safe run of `Robust` (`AngelicExit`) but a liveness hole; there is also a window between raft's switch and the check | stopgap only |
| (3) show the window holds no conf change | — | — | false: see Reachability | rejected |
| (4) drop the keep guard and prove upstream | Revert 47d6cdeeb/a453b08a1 | upstream code | a second, decreasing ghost track for the backend through `applyAll`, `applyEntries`, `kv.Restore`, `lessor.Recover`, the raft restart lemmas, plus "nothing served while `ci < \|A\|`". Estimated at several thousand lines over the server's largest proofs (`notes/etcd-dist-d6.md:318-336`). Upstream is correct here, apart from the verify-mode check | none | correct, most proof |

**Recommendation: (1b).** It makes the keep path's raft state equal to the restart path's, which the
proof has to cover anyway. It is small, and it needs no new ghost track. Fix the backend's meta
ConfState in the same change, so that merged snapshots at `ci` stop reading `C_k`. Add a unit test
like `TestKeptSnapshotLeavesRaftConfStateStale`, with the tracker and the meta at `C_ci`.

## 3. The pattern: what the re-apply path does that the keep path skips

**Method.** The replacing path (upstream) re-applies `(k, ci]` with `ApplyBoth` after rebuilding every
store from the snapshot's backend. The keep path applies `(k, ci]` with `ApplyV2storeOnly` over stores
recovered at bootstrap from the backend at `ci`. So the difference is, per entry kind, the effects that
run only under `ApplyBoth` or that read state differing between the two paths, plus the replacing
branch's own epilogue. I walked:

- `apply` (`server.go:1977-2027`);
- `applyEntryNormal` (`:2030-2085`);
- `apply.Apply` → `uberApplier.Apply`/`dispatch` (`apply/uber_applier.go`), its wrapper chain (auth,
  quota, capped, corrupt) and every `applierV3backend` method;
- `applyConfChange` (`:2093-2163`);
- the `RaftCluster` setters (`membership/cluster.go`);
- `rafthttp.Transport` peers;
- the replacing branch of `applySnapshot` (`:1118-1239`).

For each, I listed the writes to state other than the backend.

| effect for an entry in `(k, ci]` | keep path |
|---|---|
| mvcc data, index, revision; lease, alarm and auth data; members; consistent index | matched: in the backend at `ci`, and the stores were recovered from it at bootstrap |
| mvcc watchers notified | matched: none exist (restarted process, not serving: publish is above `ci`) |
| wait registry `s.w.Trigger` (normal entries, `ApplyBoth` only) | matched: no waiters. Request IDs are per process, and this member's proposals after the restart are above `ci` |
| `applyWait`, applied index and term, `firstCommitInTerm`, `lessor.Promote` on empty entries, conf `w.Trigger`, `removedSelf` stop | matched: both paths run them |
| uber applier chain (alarms) | matched: built at bootstrap from the alarms at `ci` (the replacing branch rebuilds it) |
| cluster in memory: version, member attributes, peer URLs, downgrade info (replayed in memory even under `V2storeOnly`) | **a453b08a1** recovers it from the backend. The replay then rewrites it transiently in index order and ends at the `ci` values. `Add/Remove/PromoteMember` are no-ops under `V2storeOnly` |
| transport peers (`AddPeer`/`RemovePeer`/`UpdatePeer` run under both) | **a453b08a1** rebuilds them from the members. The replay changes them transiently and ends at `ci`, except as noted in the next row |
| a conf change that failed `ValidateConfigurationChange` | **remains, also upstream on any restart:** validation is skipped under `V2storeOnly` (`cluster.go:307`), so the replay calls `transport.AddPeer` for a rejected add (a non-member ID). Not safety: the peer refuses an ID mismatch, so the effects are connections and log noise. Recorded separately: `etcd-restart-replay-rejected-confchange-addpeer` |
| raft `ApplyConfChange` | **remains: this file** |
| `ep.confState` (and from it raft snapshots and merged snapshots) | **remains: this file** |
| backend meta ConfState via `beHooks.SetConfState` | **remains: this file.** It is written as `C_k` beside `ci` and read by `createMergedSnapshotMessage` |
| `ep.replayConf` (the replacing branch sets it to nil) | matched: kept as bootstrap's `C_ci`, which is right for a merge at `ci` while `replayTerms` covers it |
| simple-auth tokens of `Authenticate` entries | **remains, liveness only:** re-apply would re-assign the tokens issued in `(k, ci]`, and the keep path (like any restart) does not. Clients re-authenticate |
| NOSPACE alarm re-proposal (`applyEntryNormal`, `ApplyBoth` only) | benign: the original alarm entry is in the log |
| metrics (mvcc and lease counters for re-applied operations) | differ, metrics only |

So, of the work the keep path skips, the only gap left that affects safety is raft's configuration. It
shows up in three places: the tracker, `ep.confState`, and the backend's meta ConfState. (1b) closes all
three. The member-state gap was the first gap, closed by a453b08a1. Both gaps have the same cause: work
that upstream's re-apply does under `ApplyBoth` and the keep path skips. The table is the list of that
work, so it is where a third such gap would show up.

## Proof

yes: the pinned fork carries the keep guard (47d6cdeeb). With a conf change in `(k, ci]`, raft's
configuration no longer follows the applied log or bootstrap's rule, and with two of them the crash
results (linearizability) are false. The crash-form `NewServer.wp_proofC` is still `sorry`, so no
current result is affected, but it cannot be proved over the guard as it stands. The graceful results
are unaffected: no crash, so no backend ahead of the WAL.

## Notes

The test file is a whole `_test.go` for `server/etcdserver` at fork a453b08a1. It reuses that branch's
`peerTransporter` (in `snapshot_below_backend_test.go`).
