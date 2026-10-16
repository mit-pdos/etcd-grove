# etcd-io/raft#515: MoreUpToDateCorrectInv in etcdraft.tla is false

<https://github.com/etcd-io/raft/issues/515>. Open, filed 2026-09-10, no comments, no PR. It
concerns the TLA+ model `tla/etcdraft.tla` in etcd-io/raft, not the Go code.

**The report.** The invariant (`tla/etcdraft.tla:848-853` on `raft-upstream/main`)

```tla
MoreUpToDateCorrectInv ==
    \A i, j \in Server :
       (\/ LastTerm(log[i]) > LastTerm(log[j])
        \/ /\ LastTerm(log[i]) = LastTerm(log[j])
           /\ Len(log[i]) >= Len(log[j])) =>
       IsPrefix(Committed(j), log[i])
```

says that a log at least as up to date as `j`'s contains `j`'s committed prefix. Five servers
give a counterexample. `a` leads term 2 and replicates `(t2)` to `b`. `e` reaches term 3 and
appends `(t3)`. `a` leads term 4 and commits `[(t2),(t4)]` with `{a,b,c}`. `a` then sends
`[(t2)]` with commit 1 to `d`. Now `e`'s log `[(t3)]` is more up to date than `d`'s `[(t2)]`, but
it does not contain `d`'s committed `(t2)`. The reporter checked this with TLC and notes that `e`
still cannot win an election.

## Classification

**N** (not a bug in the Go code). The false statement is an invariant of the TLA+ model, and the
counterexample is right. Up-to-dateness compared with *any* node that has committed an entry
does not imply containing the entry. It holds only against a member of the quorum that
committed it, which is how leader completeness uses it. No Go behavior is involved, and no
spec here depends on the TLA+ invariant.

## The code path and its verification state

There is no Go path. The Go counterparts of the invariant's ingredients are verified (source:
the spec and proof files directly, because `verified.txt` was not available):

| Go function | State | Spec |
|---|---|---|
| `raftLog.isUpToDate` | verified | `Spec/go_etcd_io/raft/v3/raftLog__isUpToDate.lean:41` (`b = plogUpToDate ...`) |
| `raftLog.maybeCommit`, `raft.maybeCommit` | verified | `Spec/go_etcd_io/raft/v3/raftLog__maybeCommit.lean:41`, `raft__maybeCommit.lean:76` (`CommitOk`) |
| `raft.Step` (vote handling) | verified | `Spec/go_etcd_io/raft/v3/raft__Step.lean`, model rule `Step.grantVote` (`Protocol/Model.lean:1644`, premise `plogUpToDate ... = true`) |

## The argument

The Lean proof does not state an invariant like `MoreUpToDateCorrectInv`. It proves the true
property this invariant was meant to support:

- **Leader completeness**, `leader_completeness` (`Proof/go_etcd_io/raft/v3/Protocol/Facts.lean:480`):
  an entry that a node has committed at a term no later than a leader's is in the leader's log.
  It is proved by `lc_core` (`Protocol/LeaderCompleteness.lean:573`) over the vote table. The
  pivot is a voter that is in both the commit quorum and the election quorum, with its vote
  record and its acknowledgement history (`votesTbl_just`, `ev_pair`). The up-to-date
  comparison is applied only to that voter, which is the restriction the TLA+ invariant drops.
- The system results (`raft_dyn_committed_agree`, `raft_dyn_election_safety`,
  `Protocol/ResultsDyn.lean:103,130`) rest on that, not on any "more up to date ⇒ contains
  committed" statement.

In the reporter's trace, `d` grants its vote to `e`, and the Lean model allows that
(`Step.grantVote` only needs `plogUpToDate`). `e` cannot collect a quorum: every quorum meets
`{a,b,c}`, whose members all refuse. So the model allows exactly what the reporter says the
TLA+ system allows, and nothing more.

The obvious repair, `Committed(j)` replaced by the globally committed prefix, is still false on
the same trace, because `(t2)` at index 1 is globally committed. A true version has to restrict
`j` to the members of the quorum that committed the entry. That is `lc_core`'s case split,
which needs history (the vote and acknowledgement records), not only the current state.

## Proposal

None (class N). The property that matters, leader completeness, is already proved for the Go code
(`leader_completeness`, `raft_dyn_committed_agree`). Not for the upstream thread, but worth
noting: this is the second false statement in `etcdraft.tla` reported this year (with
etcd-io/raft#456), and the TLA+ model has no maintainer (#456's thread). The Lean results are a
machine-checked alternative for these properties.

## Files

None in `issues/` or `notes/` besides this report.
