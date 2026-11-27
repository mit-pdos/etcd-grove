# The boot step's term: a reachable raft panic in our fork change (2026-11-27)

A bug in this repository's own fork change, not in upstream etcd: the keep guard's replacement
(`keepfix-d-crashpin/2026-11-27` @`01b0497d0`, `server/etcdserver/bootstrap.go`'s `catchUpWithBackend`). Found while
trying to prove the raft boot law `raftBootFix.law` under R7 option (a): raft's `durPers` needs the node's durable
term to be at least the term of the commit certificate for its commit index, and the boot step does not give that.
The branch that pins `01b0497d0` (`etcd-safe-keepfix/2026-11-27`) is held from landing. Nothing on `lean` pins it.

## What goes wrong

The boot step raises `HardState.Commit` to the backend's consistent index `ci` with
`Term = max(Term_w, t)`, where `t` is the term of the ENTRY at `ci`. The term `L` at which the node learned that `ci`
was committed (at least the committing leader's term `T_c`) was only in memory and is lost in the crash, because
etcd applies a `Ready` before saving it. The restarted node then sits at a term below the term that committed its
own commit index, a state upstream raft never reaches.

## Trace (scenario S6, 5 nodes; the fork's raft `d2c16c5` and upstream v3.7.0 behave the same) [checked: test]

1. Entries 3..10 are at term 4 on A and N; index 10 is committed by A at term 7 (votes A, B, Z).
2. N receives A's term-7 `MsgApp` (commit 11), applies through 10, and crashes before saving term 7. The boot step
   restarts N with `{Term 5, Commit 10}` (branch A: entry 10 is in N's WAL).
3. A delayed term-6 `MsgVote` from C (log `[1@1 2@1 3@5]`, missing the committed 3..10) reaches N, which grants it:
   C becomes leader of term 6 (C, Z, N), a leader missing committed entries.
4. C's `MsgApp` gets N's stale `MsgAppResp Index:10` (N's commit); C's progress for N becomes `Match=10 Next=11`
   while C's last index is 4.
5. C's next send to N needs `term(10)`, which is unavailable, so it falls back to `maybeSendSnapshot` and panics
   with `"need non-empty snapshot"` (raft `raft.go:681`), its storage snapshot being empty. etcd starts members with
   an empty storage snapshot until their first snapshot file. With a snapshot, C instead loops sending `MsgSnap`s
   that N refuses, and Progress's `Match < Next` is broken.

Control: N restarted at term 7 (what upstream reaches) ignores the term-6 vote; nothing breaks. Scenario S5 (a stale
term-5 leader still leading, no CheckQuorum) reaches the same ack and panic. No conflicting commit in any run
(1000 random continuations per configuration, a 5000-seed crash simulation); agreement appears to hold by quorum
intersection, but a top-level panic breaks the no-panic theorem.

Tests (scratch, not committed): `~/.claude-F/jobs/03d8018a/tmp/staleack/{raft-fork,raft-v370}/staleack{,_tail,_sim}_test.go`,
outputs `fork-out.txt`, `v370-out.txt`, `tail-fork.txt`, `sim-fork.txt`.

## Consequence for the proof and the fix

- R7 option (a) (justify the stale ack by commitment over the current invariant) is not provable, and option (b)
  (restate the invariant) is not viable: the Go program panics.
- Proposed fix (c), pending Upamanyu: when etcd applies committed entries it also stores raft's current term in
  the backend (in the same commit as the consistent index), and the boot step raises `HardState.Term` to at least
  that stored term (vote cleared when raised). The restarted node is then at a term at least `T_c`, as in the
  control. The S5/S6 scenarios become regression tests of the fork change.
