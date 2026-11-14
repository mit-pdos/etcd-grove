# Restart with three members: Scope for generalizing `etcd_restart1_safe` (2026-11-14, for etcd-grove-81; notes only, nothing built)

The user's question (2026-11-14): can `etcd_restart1_safe` be generalized to a cluster of three?

**Short answer.** Yes, but no sound route costs only 2-3 weeks. Two routes are compared below:
- **(A)** `etcd_restart3_safe` with snapshots allowed. It needs R2s-A, the rest of S8, and S9.
  Est. **10-14 weeks of work** (about 8-11 weeks of calendar).
- **(B)** No member compacts its raft log past index 1, and no member ever sends a `MsgSnap`.
  Its sound form is B0. B0 also needs the restarted member to have **no** WAL snapshot past index 0.
  Est. **8.5-12.5 weeks of work**. B0 gives a weaker theorem, reverses a recorded decision, and adds a
  trusted text.

The cheap law the brief hoped for does not suffice. The law "no `MsgSnap` without compaction" covers the
members that keep running. It does not cover the restarted member. That member's own raft log starts at
its WAL snapshot (§3.2), and the restart rows are about the `MsgSnap`s that this member sends.

**Recommendation: (A).** Start with a one-week R2s-A Draft and probe. Use B0 as the fallback if the probe
blows the estimate (§6).

Inputs read:
- `notes/restart-scope.md` (R2s-A, S8, S9, S10);
- `notes/restart-s7-{scope,probe,p2a,freeze,handoff}.md`;
- `notes/decisions.md`: "D21" (the earlier multi-member design, D21c) and "R2s";
- `notes/raft-unified-plan.md`: "U8 v2", where the no-snapshot mode was pinned off;
- `notes/repair-design.md`: D2;
- `Proof/net/http/ListenerClose.lean` and `notes/axiom-review/http-boundary-fix.md` ("The second review", item 3);
- the restart3 draft (`examples/etcd/restart`, `Proof/.../examples/etcd/restart/`).

Abbreviations:
- `E/` = `Proof/go_etcd_io/etcd/server/v3/etcdserver/`;
- `R/` = `Proof/go_etcd_io/raft/v3/`;
- `X/` = `Proof/github_com/mit_pdos/etcd_grove/examples/`.

Go citations:
- etcd at the pin `2eaeb872bc` (`git -C .lake/go-src/etcd show 2eaeb872bc:<path>`; that clone's working tree is
  at `249d76bea7`, not the pin);
- raft at the pin `d2c16c5`, which is `565c2bd` plus the `ConfState.Equivalent` fix. `.lake/go-src/raft` is at
  `565c2bd`. `raft.go`, `log.go` and `storage.go` are identical at both revisions (checked against the module
  cache's `d2c16c558247`).

Estimates are marked (est.).

---

## 1. Where things stand

| Piece | State | Use for three members |
|---|---|---|
| `etcd_restart1_safe` | landed | template: KV ghost `r1Inv`, in-process `put`/`check`, `MainLinked`/`Adequacy`/`Results`, collection |
| `BuildServer.specRestart`, `wp_BuildServerRestart` | proved, linked (S7.4) | the restarted member's construction (old S8's C4: **done**) |
| `wp_Start_builtR` | proved (S7.2'); `Start_builtR_spec` deleted | restart3's `startMember.wp_proofRestart` already uses it |
| `srvRestartRows` | the premise of `NewServer.specR`, restated as fancy updates (P2-a) | **the open item**: for one member it is discharged by `srvRestartRows_single`; for three it is false as stated in general (row 1, `srvWinPend`) |
| P2-a raft law (`snapTo`, `snapTo_confAt`) | landed | single-voter only: a `MsgSnap`'s `To` is a committed voter other than the sender. It does not help with three voters |
| restart3 draft | `Run.wp_proof` proved over `hRows : ∀ γ id, ⊢ □ ∀ A σ, srvRestartRows γ id A σ` (`X/etcd/restart/Run.lean:142`), `startMember` over `http.registerClosable_spec`, `stop` over `http.ListenerClose_spec` (HS3, DRAFT) | the starting point of both routes |
| restart3 Go | `SnapCount = 1`, `SnapCatchUp = 1`, `NPuts = 20` writes of one key, a gRPC `Get` checked against the last value; test 15/15 counts a snapshot sent to and installed at the restarted member | route A as is; route B changes the settings |
| per-type stage B | landed (`51e51adb99`) | no longer blocks a `_safe` result |

**Why the rows are the crux.** Both rows are about `MsgSnap`s sent by the restarted member.
- Row 4, `rnSnapTermAbove` (`E/InvRaftNode.lean:464`), says that each `MsgSnap` this incarnation hands out
  is above the restored term `t0`. This is true of Go, but not provable from raft's API. Route (B) of
  `restart-s7-p2a.md` proves it in general (5-8 d, est.).
- Row 1, `srvWinPend` (`E/InvRun.lean:62`), quantifies over `sentMsg … id st`, which is keyed by member id,
  not by incarnation. It says that no `MsgSnap` this member sent at a term above `t0` is merged while the
  replay window is pending. As stated, `n` is free, so row 1 is **false on every restarted run in which the
  member is later elected and snapshots a lagging follower** (its docstring).
- R2s-A removes both rows by following the merged snapshot in the ghost state. Short of that, a three-member
  closed theorem needs a reason why the restarted member never sends a `MsgSnap`.

## 2. Route (A): `etcd_restart3_safe` with snapshots

### 2.1 The theorem in plain words
- Three etcd members run in one process.
- Writes are made through member 1. A follower other than member 1 is stopped gracefully (`HardStop`). More
  writes are made while it is down.
- The stopped member is started again in the same process, on its data directory and at its addresses. It
  replays its WAL past a snapshot record, and it may be caught up by a leader's snapshot. Leaders compact
  their logs (`SnapCount = SnapCatchUp = 1`).
- A linearizable read at the restarted member then returns exactly the acknowledged writes: every key at
  version 1, the response at revision `1 + N`.
- The program never panics.
- What it does not cover: a kill, a SIGKILL or a power loss (N2 of S7, unchanged). The premises are listed
  in §2.2.

The statement has the shape of `restart-scope.md` §S9 (`restart3_safe`): `putget3_safe`'s hypotheses
(three ids, `ps`, `BootFacts`, `ckptEffectsOk`, …), plus `bootstrapRestartContract` for the restarted member
inside `Hprem`. **`srvRestartRows` must not appear.** Neither must HS3, unless HS3 is admitted as axioms
(D-R3-4).

### 2.2 Trusted text and world assumptions

**Inherited.** These are as in `etcd_restart1_safe` and `etcd_putget3_safe`:
- `storage.diskOk`, `storage.dbOpensOk`, `apply.backendUnderQuota`, `authRecordsFit`, `grpcRepliesFit`;
- `dataDirsAbsent`, `addrsUnclaimed` (with the closed-world clause the user accepted on 2026-11-14),
  `namesUnclaimed`, `verifyEnvOff`, the context premises, `ckptEffectsOk`;
- `bootstrapContract` for each member (with the inherited `#Hmembers` flaw, S11);
- `bootstrapRestartContract` for the restarted member (N1, accepted for restart1);
- request-id freshness across incarnations (accepted on 2026-11-11);
- "graceful" (N2).

**New, hard stops:**
- **HS3** (`Proof/net/http/ListenerClose.lean`, DRAFT): `registerClosable_spec` and `ListenerClose_spec`
  become trust-boundary axioms, with an `axiom`-skill attack. They are needed only if the restarted member
  re-listens on its peer address. The alternative is D-R3-4, the handler swap, which needs no trusted text.
  - *Port re-listen.* `ListenerClose_spec` gives `netAddrFree a` back.
    - Go evidence: Go sets `SO_REUSEADDR` on Linux TCP listeners (`net/sockopt_linux.go:26-28`), so a re-listen succeeds even while the
      old connections live.
    - Both restart3's test (15/15) and the probe in §5 (18/18) re-listen on the same peer address.
  - *The keep-alive behaviour.* After the close, the OLD `http.Serve` keeps serving the connections it had
    accepted. A peer's idle keep-alive connection therefore starts new runs of the OLD raft handler, even
    after the address serves the new incarnation. Evidence: `examples/premisefix/httpkeepalive` and
    `ListenerClose.lean`'s header.
    - In restart3, the other members' rafthttp clients can reach the stopped member's handler. The
      **pipeline** handler calls the old `EtcdServer.Process`, whose `node.Step` on the stopped node returns
      an error. The **stream** handler finds no peer, because the stopped `Transport` set `t.peers = nil`
      (`rafthttp/transport.go:212-231`), and answers `404`.
    - The **snapshot** handler first saves the db file with `SaveDBFrom` into the snapshot directory, which
      **the new incarnation shares**, and only then calls the old `Process` (`rafthttp/http.go`,
      `snapshotHandler.ServeHTTP`).
    - In route A, snapshots do flow. So an old snapshot handler run that writes into the restarted member's
      `snap/` is a reachable Go behaviour: the snapshot sender uses the pipeline round tripper
      (`snapshot_sender.go:160`), which can reuse an idle connection to the old server.
    - The proof must account for those runs. Three checks:
      - (i) the handler runs of the old server need only its persistent facts (`srvProcOk`,
        `E/InvNet.lean:43`, is persistent) and per-run resources (an `lgMu` reader slot, `netRecv`) that the
        stop did not collect. `HardStop`'s `srvStopReaders` takes the store readers only;
        `EtcdServer__HardStop.lean:24-27` says that handlers in flight keep what they hold.
      - (ii) the transport contract tolerates a message delivered to the dead incarnation: it is wasted, and
        its credit is one-shot.
      - (iii) for route A only: the snapshot directory's ghost state (`γd`, keyed by member id) admits a
        `.snap.db` file written by the old handler next to the new incarnation's files.
    - The pin's head commit `2eaeb872bc` ("snap: SaveDBFrom links its file into place, keeping an existing
      one atomically") bears on (iii).
    - In the probe (§5) no request reached an old handler after the close in 18 runs. The phenomenon is
      possible, but rare in this program. The proof must still cover it.
  - *The peers' transports reconnecting* is liveness. It does not need a world assumption for a safety
    theorem: a read that never succeeds makes `Main` return without its check.
- **R2s-A's trusted pieces** (`restart-scope.md`, R2s-A; `decisions.md`, "R2s"):
  - the re-attack of the snapshot slot and of `clusterImageOk_restModel` (§6 risk 9 there);
  - the weakening of the stop's WAL slot (`σ.b ≤ i ≤ σ.commit` → `σ.b ≤ i` plus a configuration point),
    which `bootstrapRestartContract` takes, so the restart contract's text changes;
  - a raft API law, "a snapshot's index is above the receiver's commit", which is proved and shows up as an
    interface diff.
  - All of these are hard stops.

### 2.3 Stages and estimates (est.)

| Stage | Work | Est. |
|---|---|---|
| A0 | R2s-A Draft + probe: the `srvNet` snapshot certificate at a consistent index `j ≥` the raft index; the receiver's install of an image above the snapshot index, followed by the replay window; `winNoMergedSendR`'s deletion. A go/no-go checkpoint | 1 wk |
| A1 | R2s-A proper: delete `srvWinPend`, `srvWinSupply`, `srvWinAdd` and row 4. Its own Freeze (`srvNet` is exported) | 5-8 wk |
| C1 | restart3's Go: the workload of §4, the counting test, the Goose translation | 3-4 d |
| C2 | restart3's example proofs: restart1's `r1Inv`/`put`/`check` generalized to the cluster, `Run`/`stop`/`startMember` updated | 1.5-2 wk |
| C3 | HS3 as axioms with the attack, including the keep-alive accounting (i)-(iii); or the handler swap (D-R3-4: 0.5-1 wk, no trusted text) | 1-1.5 wk |
| C4 | link: `Init`/`PkgTable` (gen-init), `MainLinked`, `Adequacy`, `Results`, `etc/tcb-collections/restart3.txt`; Freeze of the statement before linking | 1 wk |

Total: **10-14 wk of work**. C1-C3 run in parallel with A1, so the calendar is about 8-11 weeks. What S7 removed
compared with `restart-scope.md`'s S7+S8+S9 figure (9-14 wk, which also counted R2s-A):
- old S8's `BuildServer.specRestart` and `Start_builtR` are done;
- F4 (many restarts) is not needed for one restart; it stays with S10;
- the rows are already fancy updates, so their deletion is mechanical.
- What S7 did *not* shrink: R2s-A itself, which has no Draft and no probe yet. It carries the risk.

### 2.4 Overlap with ongoing work
- **auth-guards** (the server's auth files). R2s-A's receiver path restates `applySnapshot.specSnapM`, whose
  install calls `authStore.Recover`. If auth-guards changes the auth store's specs, rebase A1 over it.
  Moderate.
- **auth-on-leases** (later; touches `lease`, `NewServer`'s auth-on blocks and `etcdstart`):
  - the install's `lessor.Recover` and `NewServer` (R2s-A's `srvNet`/hub texts): moderate;
  - restart3's `startMember` goes through `etcdstart`: low, an interface to regenerate;
  - leasehttp's forwarded `POST`s (http-boundary-fix, second review, item 2) do not reach restart3, because
    `RaftHandler` routes only `/raft*` and the forwarded `POST`s get a `404`.
- **k8s 7f-5** (the etcd3 watcher, `context` axioms): no shared file beyond regenerated `Link`/`Results`.

## 3. Route (B): no compaction, no `MsgSnap`

### 3.1 What raft does (checked at the pin)
- `maybeSendAppend` (`raft.go:618-662`) falls back to `maybeSendSnapshot` (`:666-689`, the only `MsgSnap`
  sender) only when `raftLog.term(pr.Next-1)` fails (`:625-629`) or `raftLog.entries(pr.Next, …)` fails
  (`:640-647`).
- `term(i)` fails with `ErrCompacted` when `i + 1 < firstIndex`, and with `ErrUnavailable` when `i > lastIndex`
  (`log.go:387-413`). `entries` fails with `ErrCompacted` when `pr.Next < firstIndex` (`log.go:415-419`,
  `mustCheckOutOfBounds` `:551-565`).
- The proof already knows that a leader's `1 ≤ Next ≤ lastIndex + 1` (`PrOk`, `R/Defs.lean:700`). So
  `ErrCompacted` is the only failure (`raft.maybeSendAppend.spec`'s docstring), and **a `MsgSnap` needs
  `pr.Next ≤ firstIndex - 1`, which requires `firstIndex ≥ 2`**.
- So the brief's claim is right: a leader whose storage was never compacted (`firstIndex = 1`) sends no
  `MsgSnap`.

### 3.2 But etcd always compacts, and the restarted member's log starts at its snapshot
- **etcd compacts at index 1 even with no catch-up pressure.**
  - `snapshotIfNeededAndCompactRaftLog` (`server.go:1240-1249`) takes a memory snapshot every
    `memorySnapshotCount = 100` applied entries (`:112`, `:1255`; a constant, not configurable), and every
    snapshot is followed by `compactRaftLog`.
  - `compactRaftLog` compacts at `1` unless `snapi > SnapshotCatchUpEntries` (`:2176-2177`).
  - `MemoryStorage.Compact(1)` makes `firstIndex = 2` (`storage.go:268-288`).
  - So "never compact" is not a fact of any run longer than 100 entries, and the proof's model bounds no run
    below that.
  - What is a fact of the program, with `SnapshotCatchUpEntries = math.MaxUint64`, is **"never compacted past
    index 1"**. The examples' `etcdstart.NoSnapCatchUp = 1 << 48` gives the same thing below `2^48` applied
    entries.
  - At `firstIndex = 2` a `MsgSnap` needs `Next = 1`. This is excluded by the tracker invariant `Next ≥ 2`,
    which holds because every log holds the committed bootstrap entries at term 1: D21c (A)'s argument, `PrLo`.
- **The restarted member's raft log starts at its WAL snapshot.**
  - `bootstrappedWAL.MemoryStorage()` (`bootstrap.go:741-753`) calls `ApplySnapshot` of the newest WAL
    snapshot record (`recoverSnapshot`, `:448-480`). So the restarted storage has `firstIndex = σ.b + 1`
    (`storage.go:218-237`). At `σ.b = 0` (the record `wal.Create` writes, `wal.go:181`) the index stays 1.
  - So whenever the restarted member replays its WAL **past a snapshot record** (`σ.b > 0`), its own log is
    compacted at `σ.b`.
  - As a leader, it then sends a `MsgSnap` to any follower whose `Next ≤ σ.b`. Whether this happens depends
    on the other members' logs, not on anyone's compaction.
  - In this program Go never does it once the writes made during the downtime commit: those writes commit
    with quorum `{A, B}`, so both running members hold the entries past `σ.b`, and rejection hints stay at
    or above `σ.b`.
  - But that is a cluster-level, temporal invariant ("every member's log holds index `σ.b`, from the first
    write committed while the member was stopped"). It is not a per-node raft law. Est. 3-5 wk on raft and
    the program.
  - **A local snapshot without compaction exists for the running members**: `SnapshotCount = 1` with
    `SnapshotCatchUpEntries = MaxUint64` gives WAL snapshot records and storage compacted at 1 only (probe
    B1). **It does not exist for the restarted member**, which is the member whose `MsgSnap`s the rows are
    about.
- **The model also admits a disk snapshot when `SnapshotCount = MaxUint64`.**
  - `ClusterVersionSet` forces a disk snapshot on a cluster-version downgrade (`apply/backend.go:270-285`,
    `ForceSnapshot`).
  - The proof's monitor permission admits any valid version at most the server's (`monitorReq`,
    `E/InvMonitors.lean:62`), so `3.0.0` after `3.7.0` is admitted.
  - So `σ.b ≤ 1` at the stop is not provable today. To get it, either strengthen the names-only monitor's
    trusted text to "never below the cluster's version" (trusted text about names-only code), or add a
    premise.
  - Whether Go itself can reach such a downgrade was not checked. The candidate path: a lagging former
    leader's monitor proposes `3.0.0` while its `Cluster.Version()` is still nil, and the proposal is
    forwarded and committed after a `3.7.0` entry. It is not recorded as an issue: it is unconfirmed.

### 3.3 The sound form of route B: B0
- **Configuration:** `SnapshotCount = SnapshotCatchUpEntries = math.MaxUint64` for every member.
- **What it needs:**
  1. **Raft: the no-snapshot mode re-added.**
     - This is D21 M3's mode: `NGhost.ns`, the cluster's `reNoSnap`, `PrLo` in `PrvalsOk`, `LogNsOk`, and the
       reject-hint clause `RejHintOk`. The flag, `PrLo` and `RejHintOk` are still in the code. U8 v2 pinned
       the mode off (`NsCap ns st := ⌜ns = false⌝`), so its `ns = true` branches hold vacuously today (about
       22 sites).
     - It needs a storage compaction cap in U8 v2's range-ownership storage contract: `storCompactCap`, never
       built (`raft-unified-plan.md:544-552`, "the fallback").
     - It needs `RestartNode` in the mode. The old mode derived `reNoSnap = false` at a restart.
     - Then the API law `isRaftMsg_not_snap` returns for a cluster in the mode.
     - **This reverses a recorded direction**: `repair-design.md` D2 (b), "re-adding the no-snapshot mode to
       raft … reverses U8 v2's recorded direction (the user's 'follow recorded direction')". So it is the
       user's decision.
     - Est. 2.5-4 wk, plus an interface diff.
  2. **Server: the cap supplied.**
     - `compactRaftLog` at `MaxUint64` compacts only at 1.
     - Every member's boot contract gives the mode (old `%Hnosnap`).
     - The restarted storage is capped only if `σ.b ≤ 1`: that is `memStorRestarted` inside
       `bootstrapRestartContract`, whose text changes (a premise of the closed theorem).
     - The snapshot paths (`applySnapshot`, the merged send) are dead under the mode.
     - Changes to linked specs (`NewServer.spec`/`specR`, `bootOk`/`bootOkR`) go to a Freeze. Est. 1.5-2 wk.
  3. **`σ.b ≤ 1` at the stop:** `SnapshotCount = MaxUint64`, plus the no-downgrade trusted text of §3.2.
     Est. 0.5-1 wk, plus an attack.
  4. **The rows:** `srvRestartRows_noSnap`, like `srvRestartRows_single`, vacuous from the mode's law.
     Est. 2-3 d.
  5. Common work C1-C4 (§2.3), with restart3's Go settings changed to B0's. Est. 4-5 wk.
- **Total: 8.5-12.5 wk of work.** That is about 1.5 weeks below A. The raft half is a known design (it was
  built once, 2026-10-19), so its risk is lower than R2s-A's.
- **The theorem B0 gives, in plain words.** As in §2.1, but:
  - no member's raft log is compacted past index 1;
  - no snapshot is ever sent;
  - the restarted member replays its whole WAL from the index-0 record.
  - So B0 adds what three members bring (catch-up by `MsgApp`, read index across members, a follower
    restarted while two keep the quorum). It drops the "WAL past a snapshot record" path, which restart1
    covers for one member, and the snapshot catch-up, which etcd uses for a member that lags.
- **Not recommended: B1** (disk snapshots, compaction at 1). The restarted member's rows need the
  cluster-level invariant of §3.2 (3-5 wk more), which makes B1 cost more than A for less.

### 3.4 Trusted text and world assumptions of B0
- Everything in §2.2's "Inherited" and HS3 (or the handler swap).
- New, hard stops:
  - the no-downgrade text for the version monitor;
  - the restart contract's `memStorRestarted` at `σ.b ≤ 1`;
  - the no-snapshot mode's storage cap (`storCompactCap`, raft API vocabulary; proved, but a new client
    obligation);
  - D2 (b) reversed (user).
- The keep-alive accounting is (i)-(ii) only, because no snapshot handler runs.

### 3.5 Overlap
- B0's server half edits `bootOk`/`bootOkR`/`NewServer`, which **auth-on-leases' `NewServer` auth-on blocks**
  also edit: direct, so sequence one after the other.
- Its raft half touches about 150 sites that carry the `ns` flag (`raft-unified-plan.md:1067-1068`); no
  ongoing track owns them.
- auth-guards and k8s 7f-5: as in §2.4.

## 4. The workload and the check (both routes)

*Recommended* (as the brief proposes, restart1's shape):
- **Before the stop:** `N1` in-process `EtcdServer.Put`s of distinct keys through member 1. member 1 may be a
  follower; the proposal is forwarded, which raft's `fwdP` path already covers.
- **The stop:** a follower other than member 1 (restart3's rule, so no election is forced). Wait for
  `AppliedIndex() ≥ NBoot`, then `HardStop`. Then either close its peer listener (HS3) or swap its handler
  (D-R3-4).
- **While it is down:** `N2` more `Put`s of distinct keys through member 1. The quorum is `{1, other}`.
- **The restart:** `BuildServer` + `Start` on the same directory and addresses. Wait for `Leader() ≠ 0`
  (restart1's pitfall).
- **The check:** one in-process linearizable `Range` of the keys' prefix at the restarted member. It panics
  unless the result is exactly the `N1 + N2` pairs, each at version 1, with `Header.Revision = 1 + N1 + N2`.
- **Why in-process:** the program then serves no gRPC at all, so `serveClient`/`NewClient` and the client
  stack drop out. restart1's `put`/`check`/`r1Inv` proofs carry over, with the KV invariant being the
  cluster's (`kvInv`, shared through `restartNames`). The read goes through the restarted member's read
  index (`MsgReadIndex` to the leader, the multi-voter path already proved).
- **The alternative:** restart3's gRPC `Get` (already proved, `restartCheck.wp_proof`), at about +3 d for the
  client stack (D-S7-3's reasoning).
- **Revision:** only the `Put`s advance the KV revision. The members' `ClusterMemberAttrSet` and
  `ClusterVersionSet` entries do not. restart1 proved `1 + NPuts` with one member, and the probe measured
  `1 + N1 + N2` with three.
- **Sizes:** route A needs `N2` large enough that the leader compacts past the stopped member, which any
  `N2 ≥ 1` does at `SnapCatchUp = 1`. Route B0 has no constraint. `N1 = 5`, `N2 = 20` would do.

## 5. Go evidence (probe, 2026-11-14)

`examples/etcd/restart3probe/probe_test.go` (committed with this note; skipped unless `$PROBE_CFG` is set):
- the program is restart3 with a configurable snapshot setting, `NPre = 5` client `Put`s, a follower stopped
  (`HardStop` + listener close), `NDown = 150` `Put`s (more than `memorySnapshotCount`, so a memory snapshot
  and a compaction happen), the member restarted, and a prefix `Get` at it;
- a counting logger and a per-incarnation counter of raft-handler requests, split before and after the
  listener's close.

Each setting ran 6 times, each run in its own process, under the 32G cap with `GOWORK=off`. The outputs are
in `/shared/tmp/restart3-scope/run-*.txt`.

| Setting | WAL snapshot index at the restart (σ.b) | compaction indices | merged `MsgSnap` sent after the restart | check (155 pairs, version 1, revision 156) | old handler runs after close |
|---|---|---|---|---|---|
| A (`1`, `1`) | 12 or 13 | many (2…163) | 1 in every run, installed | 6/6 | 0 |
| B1 (`1`, `MaxUint64`) | 12 or 13 | **only 1** | 0 | 6/6 | 0 |
| B0 (`MaxUint64`, `MaxUint64`) | **0** | **only 1** | 0 | 6/6 | 0 |

What it shows:
- etcd compacts at 1 even when nothing needs compacting (B1, B0).
- The restarted member replays past a snapshot record exactly when disk snapshots are on (A, B1).
- B1 sends no `MsgSnap` in practice although the restarted log starts at 12-13. This matches §3.2: the
  running members are ahead, but nothing in raft's API says so.
- The exact check holds in every setting.
- Old-incarnation handler runs after the close are possible (`httpkeepalive`) but were not observed here.

## 6. Decisions needed

- **D-R3-1. Route.** *Recommended: (A)*, `etcd_restart3_safe` with snapshots. Three reasons:
  - it covers the path etcd relies on for a lagging restarted follower;
  - it keeps the recorded direction (snapshots verified, no no-snapshot mode);
  - its result deletes the restart-only rows for every configuration, which S10 (the schedule theorem) needs
    anyway.
  - (B0) costs about 1.5 weeks less, with less risk on the raft side. It needs the user to reverse D2 (b) and
    to accept a new trusted text (no cluster-version downgrade), and it proves less: no snapshot, no WAL
    snapshot replay.
  - Not doing either keeps restart1 as the only restart theorem.
- **D-R3-2. A go/no-go after A0** (R2s-A's one-week Draft and probe). If the probe's estimate exceeds 9 weeks,
  or it hits a blocker, report it, with B0 as the fallback. *Recommended.*
- **D-R3-3. The workload of §4**: in-process writes through member 1, in-process read at the restarted member,
  checked exactly. *Recommended*, over restart3's one-key gRPC check, which cannot see a lost earlier write.
- **D-R3-4. HS3 or a handler swap.**
  - Restart3 closes and re-listens the stopped member's peer address. That needs HS3 (two new axioms) and
    exposes the keep-alive runs.
  - Alternative: the example keeps the listener and serves it through its own small handler, which forwards
    to the current incarnation's `RaftHandler()` and is swapped under a mutex at the restart. This is
    verified example code with no trusted text, and its proof is 0.5-1 wk.
  - The swap still has old-server runs that were in flight at the swap, so check (i)-(ii) remains.
  - Neither variant is how etcd restarts: a new process's exit closes the old connections. Both are
    artifacts of restarting in the same process.
  - *Recommended: the swap for restart3; HS3 at S10*, where gRPC addresses must be re-listened anyway.
- **D-R3-5 (only if B0).** Re-add raft's no-snapshot mode, reversing D2 (b), and accept the no-downgrade text.
  This is for the user.
- **D-R3-6. Name and stage label.** "restart3" for this track, theorem `etcd_restart3_safe`, with R2s-A as
  its first stage. *Recommended.*

Hard stops for whoever does the work:
- A0's checkpoint;
- every Freeze (`srvNet`, the theorem);
- every trusted text: HS3 if chosen, R2s-A's slot re-attack, the restart contract's changes, and for B0 the
  no-downgrade text and the cap;
- every `etc/land.sh`.
