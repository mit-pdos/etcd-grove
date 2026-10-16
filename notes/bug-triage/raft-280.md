# etcd-io/raft#280: leader election may select a leader without all committed entries (Figure 8)

<https://github.com/etcd-io/raft/issues/280>. Closed 2025-08-31 with no fix. Filed as a
"Discussion".

**The report.** The reporter reads Figure 8 of the Raft paper as showing that the election
check (last term, then last index: `raftLog.isUpToDate`, `log.go:442` at the raft pin
`509271dac`, used by `raft.Step`'s `MsgVote` handling) can elect a leader that lacks a committed
entry. They propose also comparing commit indices. Commenters explain the misreading. Figure 8
shows why a leader must not commit an entry of an earlier term by counting replicas. Raft
commits only entries of the leader's current term, and earlier entries follow by log matching,
so the scenario in which `S5` wins without a committed entry cannot happen.

## Classification

**N** (a misreading of the paper, no Go bug). The Go code has the Figure 8 rule.
`raft.maybeCommit` passes `entryID{term: r.Term, ...}` (`raft.go:778`), and `raftLog.maybeCommit`
commits only if `matchTerm(at)` (`log.go:459`). Leader completeness is proved for the code.
The specs state both the rule and its consequence.

## The code path and its verification state

Source: the spec and proof files directly (no `verified.txt`). All are verified and linked in
`Proof/go_etcd_io/raft/v3/Link.lean`.

| Go function | State | Spec |
|---|---|---|
| `raftLog.isUpToDate` | verified | `Spec/go_etcd_io/raft/v3/raftLog__isUpToDate.lean:41` |
| `raftLog.maybeCommit` | verified | `Spec/go_etcd_io/raft/v3/raftLog__maybeCommit.lean:41` |
| `raft.maybeCommit` | verified | `Spec/go_etcd_io/raft/v3/raft__maybeCommit.lean:76`, post `CommitOk` (`:21-27`: "the entry there is of the leader's term") |
| `raft.Step` (vote, commit) | verified | `Spec/go_etcd_io/raft/v3/raft__Step.lean`; model rules `Step.grantVote`, `Step.commit` (`Protocol/Model.lean:1644`, `:1779-1786`) |

## The argument

1. **The commit rule.** `Step.commit` (`Protocol/Model.lean:1781-1786`) needs
   `plogTermAt s.base s.log n = some s.term`: the leader commits index `n` only if the entry there
   is of its own term. `raft.maybeCommit.spec` gives `CommitOk`, which contains that conjunct.
   So the code cannot do Figure 8(c)'s "commit (2,2) by counting".
2. **The consequence the reporter asks for.** `leader_completeness` (`Protocol/Facts.lean:480`):
   an entry a node has committed, at a term no later than a leader's, is in that leader's log.
   With reconfiguration it is `raft_dyn_committed_agree` (`Protocol/ResultsDyn.lean:103`). In
   Figure 8(d), `S5` can win term 5 only because index 2 (term 2) was never committed. Once
   the term-4 entry at index 3 is committed in (e), `S5`'s last entry (term 3, index 2) is
   less up to date than that of every member of the commit quorum, and `S5` cannot win.
3. **The proposed extra check.** Comparing commit indices in the vote is unnecessary for
   safety, because the proofs go through without it. A follower's commit index can also lag
   the global one arbitrarily.

As a counterfactual (the behavior was never in the code): a `maybeCommit` that committed
earlier-term entries by counting would fail `CommitOk`, and `lc_core`'s
`plogTermAt ... = some t` of a commit fact (`Facts.lean:315`, `cq`) would be unprovable. The
specs exclude the Figure 8 bug, as an F+ would.

## Proposal

None (class N).

## Files

None in `issues/` or `notes/` besides this report.
