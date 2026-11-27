# `bootstrap`'s restart contract claimed the WAL's read facts of any files (2026-11-27)

A bug in this repository's own specs, found by the independent review of the interim axiom
`bootstrap.wp_proofRestart` (branch `etcd-safe-rule41rm/2026-11-27`; the review: R2).

**What was false.** `bootstrapRestartContract` (`Proof/go_etcd_io/etcd/server/v3/etcdserver/InvRestart.lean`) is
`bootstrap(cfg)`'s contract on a stopped member's data directory. Its post `bootOkR` holds `wal.restartOk`, which
includes `walReadFacts σ` (the WAL interface's I1-I4 of the records `σ` the files hold: entries consecutive
from the base, the last index at most `2^61 - 1`, base ≤ commit ≤ last, the snapshot record at the base). The
contract claimed them for every `σ` its precondition's `srvFiles` admits. Go does not give them: `wal.ReadAll`
checks the entries' order (I1) but not that the hard state's commit is at most the last entry (I3), and the
WAL's own `Save` accepts any hard state. Until 2026-11-27 the contract was the Iris premise `bootPremiseR`
of the landed single-process theorem (`etcd_robust_single_process`'s `Hprem₅`, `HpremR`): a false premise.

**Reproduced.** `examples/axiomcx/bootrestartcommit` (`TestRestartCommitPastLast`, at the pinned etcd): a
one-member cluster started and stopped gracefully, its WAL then given one `Save` of a hard state with
`Commit = last + 5` through etcd's `wal` package (`Open`, `ReadAll`, `Save`, `Close`); restarting the member
(`bootstrap`'s restart branch succeeds) panics in raft's `RestartNode` (`loadState`): `state.commit 6 is out
of range [0, 1]` [checked: `go test`, go1.27.3]. The reviewer's original test ran through `embed.StartEtcd`
at the fork `d26dd5da6` (`… state.commit 9 is out of range [0, 4]`).

**The fix (same branch).** The facts become a premise of the contract (`clusterVerLogOk L ∧ walReadFacts σ`),
which the caller supplies from the stopped image: `wal.stopImage` (`WalApi.lean`) carries them, and the
graceful stop proves them (`StopShutdown.lean`, `StopReadFacts.lean`): I1 and I4 of the files' read
(`walFiles_readShape`, `storage/WalRecs.lean`); I3 from raft's durable log (`raftState_logView`: the durable
log reaches the node's commit, and `StorageHolds` makes the records' last index the node's); I2 from the
interim law `raftStateLastFits.law` (axiom `raftStateLastFits_law_holds`, `raftStateLastFits.lean`: a node's
durable log ends within its cluster's room `readyFits`; to be retired by a raft law).
