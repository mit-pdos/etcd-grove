---
upstream: none
checked: 2026-10-19
links:
  - etcd-io/etcd#7470 issue closed: a different bug in the same merge (`createMergedSnapshotMessage` looked up the snapshot's term in a possibly compacted raft log, a panic); not the message's term
  - etcd-io/etcd#7513 pr merged: the fix of #7470 (the snapshot's term from `etcdProgress.appliedt`), which is the code this finding is about
---

# A merged snapshot message can carry a term older than its content

- **Status**: with a gap of one term between the message and its content, no wrong result,
  panic or lost write was found, by code reading or in the reproduction. **With a gap of two or
  more terms, a reachable raft panic** (2026-10-19, below: "A gap of two terms"): the stale
  receiver can step up to a term in between and accept, at that term, a log the leader of that
  term never had, which puts the leader's `Match` past its last index; the leader's next send
  panics (`need non-empty snapshot`) if its storage has no snapshot. No wrong commit was found
  (by reasoning only, below). What breaks first is a Raft invariant: etcd can send a `MsgSnap`
  whose term `m.Term` is older than the snapshot it carries. It pairs a message made by the
  leader of term `T` with content applied later, which can come from a newer term or have been
  committed by a later leader. A follower still at term `T` accepts it. Its log then ends at a
  term above its own `currentTerm`, which Raft's "`currentTerm` ≥ last log term" rules out. The
  proof's protocol invariants rest on that rule (below), so the verified fork carries a fix: the
  merge checks the term (below; user's decision, 2026-10-19). One consequence is untraced:
  restarting such a member with `--force-new-cluster` writes log terms that go down (below).
  Reproduced deterministically at raft level with the real raft code and an emulation of etcd's
  pipeline, and the etcd half with the real `raftNode` and `applyAll`; not end to end. The panic
  is reproduced with the real raft code from the receiver's stale state, with the messages built
  by hand. The fork's check excludes every gap.
- **Where**: etcd fork pin `8a24be2a3` (`etc/goose.py`). Upstream `main` has the same
  `applyAll` (`server.go:978-998`, read, not run). raft fork `c8217eb9` (raft v3.7.0 has the
  same code; the raft test passes there too).
  - raft `raft.go:543` (`send`): every message but `MsgProp`/`MsgReadIndex` is stamped
    `m.Term = r.Term` when it is created. `maybeSendSnapshot` (`raft.go:666-690`) creates the
    `MsgSnap` while leader at `T`.
  - etcd `server/etcdserver/raft.go:358-400` (`processMessages`): a `MsgSnap` is not sent. It
    is pushed onto `msgSnapC` (capacity `maxInFlightMsgSnap = 16`, `server.go:102`; `raft.go:145`,
    `:380`). For a leader this happens before the `Save` (`raft.go:242`, `:256`), for a follower
    after it (`:299`). Either way it comes after the Ready's `toApply` was handed to `applyc`
    (`:232`).
  - etcd `server/etcdserver/server.go:978-1009` (`applyAll`): each job takes at most one message
    off `msgSnapC`, at its end (`:1004`), after `<-apply.notifyc` (`:989`) and `raftAdvancedC`
    (`:996`). Nothing checks the term or the leadership.
  - etcd `server/etcdserver/snapshot_merge.go:32-53` (`createMergedSnapshotMessage`): replaces
    only `m.Snapshot` with `(ep.appliedi, ep.appliedt, confState)`. `m.Term` and `m.From` are
    unchanged.
  - raft `raft.go:1089-1130` (`Step`): a `MsgSnap` at the receiver's term is not filtered.
    `stepFollower` (`:1735-1738`) or `stepCandidate` (`:1690`) calls `handleSnapshot`
    (`:1837`). `restore` (`:1857-1945`) checks the index against `committed`, the follower state
    and the id in the `ConfState`. It never compares the snapshot's term with `r.Term`.
- **What happens** (terms as in the reproduction: the old leader's term `T = 1`, the new
  `T+1 = 2`). Five members A..E. A is leader at `T`. D and E were cut off long enough that A
  compacted its raft log past their logs. E stays cut off from B, C, D but can reach A.
  1. A's raftNode loop stalls in the `Save` of a Ready (a slow WAL fsync, longer than an
     election timeout). It neither ticks nor takes a Ready meanwhile. `node.run` still steps
     incoming messages: `recvc` is served while `advancec` is armed (raft `node.go`).
  2. In the stall, D's and E's heartbeat responses reach A. A, still leader at `T`, finds their
     next entries compacted and makes `MsgSnap`→E and `MsgSnap`→D, both stamped `T`. They stay in
     raft's `msgs`.
  3. B, C, D hear nothing from A for an election timeout. B wins `T+1` (pre-vote) with C and D,
     and B's append reaches A. A becomes a follower at `T+1`. Its reply waits for the next Ready.
     E's pre-votes reach only A, which ignores them (in lease), so E stays at `T`.
  4. The fsync returns. A's next Ready (`k`) is a follower's. It carries `T+1`, the two term-`T`
     `MsgSnap`s and the reply to B. `processMessages` pushes D's, then E's. Job `k` merges D's
     with A's term-`T` content. D is at `T+1` and drops it.
  5. B gets A's reply and sends it its commit. Ready `k+1` commits B's term-`T+1` entry. Job
     `k+1` applies it (`appliedt = T+1`) and takes E's message: "`MsgSnap` term `T` from A",
     snapshot `(idx, T+1)`.
  6. E, at `T`, accepts it. Its raft log ends at `(idx, T+1)` and its raft term is `T`.

  Two queued messages are needed, and the order of the steps matters. In the stall A cannot learn
  B's commit: B's probe of A pauses after its first `MsgApp` (`tracker/progress.go` `SentEntries`),
  B's heartbeats carry `min(pr.Match, committed) = 0` (`raft.go:694-709`), and A's replies wait
  for a Ready. A Ready whose `MsgSnap`s were made while A was leader therefore cannot also commit
  a newer term. The newer content comes one job later, in the job of the next queued message.
  Three-member clusters cannot hit this: only one follower can lag past compaction, and a lone
  queued message is merged by its own Ready's job.

  Second shape (code reading, not reproduced): no newer term in the content, but its prefix was
  committed by a later leader. A applies only up to `j < c` in a size-limited batch. A's entries
  up to `j` are committed at `T+1` by B (Figure 8). The merged message has `appliedt ≤ T`, so
  E's terms stay bounded, but the content is not committed in the term-`T` leader's log. A check
  `appliedt ≤ m.Term` would miss this; the term check below does not.

  What the receiver can do afterwards (code reading, `notes/snapshot-path-s0.md`, part 1): no
  wrong result found. E cannot lead at any term `≤ T+1`. Below `T+1`, the quorum that
  acknowledged `T+1` refuses its votes. At `T+1` B leads. Above it, its log is ordinary again. A
  stale `MsgApp` of term `T` cannot change its log, because it either is below its commit or
  mismatches. A stale heartbeat's `commitTo` is a no-op: the old leader's committed index is
  below `idx`. Restarting in normal mode is fine. raft's `loadState` (`raft.go:2034-2041`) checks
  only the commit range, and the WAL's snapshot record check (`wal.go:533-536`) compares the
  record's term with the snapshot's, both `T+1`. `s.Term()` (the applied term, `T+1`) feeds only
  the response headers' `RaftTerm`: cosmetic.

  Untraced consequence: if E is then restarted with `--force-new-cluster`, `bootstrapRaftFromWAL`
  (`bootstrap.go:612-630`) appends the forced conf-change entries made by
  `NewConfigChangeEntries` (`bootstrap.go:754-762`, `CreateConfigChangeEnts`,
  `storage/util.go:34`). They are stamped `wal.st.GetTerm() = T` (`:759`), after a snapshot of
  `T+1`. E's log terms then go down, which raft assumes never happens (for example,
  `findConflictByTerm`'s rejection hints, `log.go:182-194`, scan down for the first term `≤` a
  given one). This is a disaster-recovery mode and the consequences are not traced. The fix
  below excludes the state.

  **A gap of two terms** (2026-10-19; the question the gap-of-one analysis left open). The
  content is of term `T + 2` (or later) under a message of term `T`; E installs it at `T`, with
  commit `idx`. Unlike a gap of one, there is now a term in between, `T + 1`, whose leader L
  need not be the sender and need not have left its term: it can be a leader cut off from the
  term-`T + 2` quorum, still up (check-quorum steps it down only after an election timeout of
  ticks without a quorum, which raft's safety and panic-freedom do not assume). L's probe of E
  at `T + 1` makes E step up to `T + 1` (`Step`, `raft.go:1089`), and its index is below E's
  commit, so `handleAppendEntries` (`raft.go:1793-1796`) answers `MsgAppResp{Index: idx}` at
  `T + 1`: an acceptance, at L's term, of a log L never had. L's `MaybeUpdate` puts
  `Progress[E].Match = idx`, past L's last index when L's log is shorter (raft's tracker assumes
  `Match ≤ lastIndex`), and in the same `Step` L sends to E from `Next - 1 = idx`:
  `raftLog.term(idx)` is `ErrUnavailable` (`log.go:401-403`), so `maybeSendAppend` falls back to
  `maybeSendSnapshot` (`raft.go:666-690`), which panics `need non-empty snapshot` when L's
  storage has no snapshot (a member that has not taken one yet: raft's `MemoryStorage` starts
  with an empty snapshot, as does etcd's until its first `CreateSnapshot`). With a snapshot, L
  sends it; it is at or below L's commit, so below E's, E answers `MsgAppResp{Index: idx}` again,
  and L loops between probe and snapshot for E. With a gap of one there is no such L: the only
  leader E can hear at `T` is the sender, which has left `T` (step 3), and E's acceptance at `T`
  reaches it at a later term, where it is dropped.

  What L can commit with E's acceptance (by reasoning, static configuration; not checked by a
  tool): nothing wrong, it seems. The quorum that committed E's content did so at a term above
  `T + 1`, before E installed it; none of its members can later answer at `T + 1`, and L, at
  `T + 1` throughout, is not one of them. So it meets L's commit quorum in a member that acked L
  genuinely, before it acked at the later term; and every leader elected after `T + 1` before
  E's install has a voter of L's quorum other than L and E, whose genuine acknowledgement came
  before its vote, so every such leader's log has L's entries up to the index L commits. The
  content E holds was made by those leaders. This is a Leader Completeness argument over commit
  quorums that mix genuine and false acceptances; the proof has none.

  For the proof: permitting the state (`TermsLe`, `CampOk` and the commit justification's term
  bound weakened, the snapshot clause carrying only a commit certificate) is not enough. The
  leader's progress invariant (every `Match` an `isAcked` of the peer, at most the last index)
  would have to admit false acceptances, and `stepLeader`'s proof would have to show the panic
  above unreachable, which it is not. So the proof cannot permit a gap of two terms without a
  premise on the leader's storage, and then only with the snapshot loop.

  **Reproduction** (`issues/etcd-merged-snapshot-stale-term/`):
  - `merged_snapshot_stale_term_test.go` (package `raft`; copy into a raft checkout, `go test
    -run TestMergedSnapshotStaleTerm .`). Five real `RawNode`s with `PreVote` and `CheckQuorum`
    play the steps above, with messages routed by hand. Node 1 is driven as etcd drives it: one
    job per Ready, `MsgSnap` pushed onto a `msgSnapC` in reverse order, its Ready saved and
    advanced only when the test says (the stalled fsync) while it steps messages, and each job
    taking one queued message and replacing only its `Snapshot` with `(appliedi, appliedt)`. It
    ends with E (node 5) at raft term 1 (`Status()`) whose `MemoryStorage` has `Term(22) = 2`
    at its last index (log `restored snapshot [index: 22, term: 2]` at `term: 1`).
    `TestMergedSnapshotStaleTermFixed` runs the same with the fix's check: both stale messages
    are dropped and E's last term stays `≤` its term. Passes at the fork `c8217eb9` and at raft
    v3.7.0.
  - `merged_snapshot_term_test.go` (package `etcdserver`; copy into `server/etcdserver/`, `go
    test ./etcdserver -run TestMergedSnapshotKeepsStaleTerm` from `server/`, Go 1.27). It runs
    the real `raftNode` loop and `applyAll`, as `TestSnapshotOrdering` does, fed two Readys by a
    fake raft node. Ready 1 is a follower's, with two term-1 `MsgSnap`s and the entry `(1, 1)`.
    Ready 2 has HardState term 2 and the entry `(2, 2)`. The transport records the second merged
    message, to 5: `Term=1, Snapshot (index 2, term 2)`. Passes at `8a24be2a3`, 30 of 30 runs.
  - `stale_term_gap2_ack_test.go` (package `raft`; copy into a raft checkout, `go test -run
    TestStaleSnapGap2 .`). From E's stale state with a gap of two (E at term 1 after stepping a
    `MsgSnap` of term 1 with snapshot `(index 3, term 3)`), node 1 as leader of term 2 with log
    `[(2, 1)]` probes E. E answers `MsgAppResp{Term: 2, Index: 3}`, node 1's `Progress[5]`
    becomes `StateReplicate match=3 next=4` with its last index 1, and its `Step` panics `need
    non-empty snapshot`. Passes at the fork `c8217eb9`. The messages are built by hand: the state
    is the gap-of-one reproduction's with one more election (term 3, by C, D and A after A's
    stall) before A's job takes E's message, and term 2's leader kept up and cut off from them;
    that run is not written.
  - What is shown: each half with the real code. raft reaches the state (steps 1-6), and etcd
    merges as emulated. Not shown end to end: an integration test would need the fsync stall
    (gofail's `raftBeforeSave` is a comment unless the tree is rewritten by `gofail enable`; the
    in-process integration framework has no failpoint build), an asymmetric partition of E, and
    D's and E's heartbeat responses landing within the stall. That was not attempted.
- **Expected**: a message's term is the sender's term when the message's content was true of
  the sender. A `MsgSnap` of term `T` carries a snapshot of the term-`T` leader's committed log,
  as raft's own `MsgSnap` does. No follower ends with a last log term above its `currentTerm`.
- **How the proof handles it**: today no member installs a snapshot (`bootOk`'s `"%Hnosnap"`,
  `Proof/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__applyAll.lean:56,202`). The snapshot
  track (T-S, `notes/decisions.md` D22) needs the `.snap` message clause: the content is in the
  term-`m.Term` leader's log and committed at `m.Term`. The stale merged message falsifies it,
  and with it the receiver's `TermsLe` (`Proof/go_etcd_io/raft/v3/Protocol/GhostState.lean:492`),
  `commitIn` at its term, the acknowledgement invariants and, after a campaign, `CampOk`, the
  measure of Leader Completeness's induction (`notes/snapshot-path-s0.md`, part 1;
  `notes/decisions.md`, "D22 S-0 carried out", D22a). Proving without the fix would mean
  redesigning those invariants (D22a (A″)). With the fix the clause holds of the merged message
  unchanged.
- **Possible fixes**:
  1. (The fork's, 2026-10-19.) The raft goroutine keeps the latest `rd.HardState.Term` it has seen
     and passes it in `toApply` (a new field). `applyAll`'s `msgSnapC` branch merges and sends
     only when it equals `m.GetTerm()`; otherwise it drops the message. Then the sender is not
     leader at `m.Term`, so raft has dropped its progress for that peer and the current leader
     catches the follower up. Term equality suffices because terms are monotone. At term `T`,
     only the leader of `T` changes a node's log or commit. After a check-quorum step-down at
     `T`, both are frozen until a higher term. So content applied while the node is still at
     `m.Term` is a prefix of the term-`m.Term` leader's log, committed at `m.Term`. This also
     excludes the second shape, which needs the sender at a later term.
  2. Read raft's status in `applyAll` (`s.r.Status()`) and merge only if it is leader at
     `m.Term` (`notes/decisions.md` D22a (D)). Same effect, but it goes through `node.Status`.
     etcd's cached `s.isLeader()` is not enough (it passes after a re-election at a later term),
     and neither is `s.Term()` (the applied entry's term).
  3. Restamp `m.Term` with the term the content is committed at. Not sound: the sender need not
     be leader at that term.
- **Found**: 2026-10-19, by stage S-0 of the snapshot track (T-S). The plan's `.snap` clause was
  checked against what `applyAll` sends (`notes/snapshot-path-s0.md`, part 1). The reproduction
  was written the same day. Building it showed that the step-down has to happen inside the stall,
  in the same window as the `MsgSnap`s are made (step 4), and not after a Ready that already
  carried them.
