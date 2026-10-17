# Verifying etcd-io/raft#452

- PR: etcd-io/raft#452, "raft: reduce async storage missing entry log noise",
  https://github.com/etcd-io/raft/pull/452, head `a775bccb5d28521b656769192299295894714d2d`
  (one commit; base upstream `main` at `3f4062b3c`). Fixes etcd-io/raft#307.
- Verified at fork commit `e8f2206f1` (branch `pr-raft-452-goose-lean` of `~/etcd`, worktree
  `~/etcd-pr/raft-452`): the PR's non-test diff applied with `git apply -3`, cleanly, onto the
  pinned `raft37-goose-lean` (`509271dac`, raft v3.7.0 `b867cf13` plus the read-index fix).
  No conflicts, no rewrites. Upstream `main` has not touched `log_unstable.go` since it split from
  release-3.7, so no upstream commits were needed. The PR's testdata change
  (`testdata/async_storage_writes.txt`) came along with it, and `go build ./...` and `go test .` pass.
- This repository's branch: `pr-verify/raft-452` (worktree `/shared/etcd-grove-pr/raft-452`).

## Verdict

The PR is sound. Its only code change replaces one `Infof` with `Debugf`, on the
"entry missing from unstable log" exit of `unstable.stableTo`. Raft's proof treats every
`Logger` formatting method alike: it returns, has no observable effect, and `Debugf` is
among them (`logMethods`, `Proof/go_etcd_io/raft/v3/InvLogger.lean`). So the existing spec
of `unstable.stableTo` holds of the new code, and the existing proof goes through unchanged.
No caller is affected, and the trust base is the same. The proof does not cover what the PR is
about: which messages reach an application's logger at which level, so how noisy the logs are.
That observable is outside the model. The only other place the change shows is the PR's
updated datadriven test expectations.

## Changed functions

| Package | Function | Kind | State before | State after | Outcome |
|---|---|---|---|---|---|
| `go.etcd.io/raft/v3` | `unstable.stableTo` (`log_unstable.go`) | refactor (log level only; same state transitions) | verified | verified | old spec re-proved, proof unchanged |

No types, struct fields or package-level variables change.

## Specs

`unstable.stableTo.spec` (`Spec/go_etcd_io/raft/v3/unstable__stableTo.lean`) is unchanged. It
says nothing about which `Logger` method each exit calls, only that a hit drops the persisted
prefix and anything else leaves the state as it was. The doc comment's sketch of the body says
`Infof` on all three exits; on this branch it says `Debugf` for the first.

## Callers (step 6)

None to check: the spec did not change. The direct caller is `raftLog.stableTo`, and its caller
`raft.Step` (on `MsgStorageAppendResp`). Both are verified on `lean`, and both were rebuilt here
against the unchanged spec.

## Trust base

No new postulates or `sorry`s. `#print axioms` of the three results, `unstable.wp_stableTo`,
`raftLog.wp_stableTo` and `raft.wp_Step` (from `Proof/go_etcd_io/raft/v3/Link.lean`), gives the
same output on this branch as on `lean`, byte for byte (the probe `raft-452/Ax.lean`, its
output `raft-452/axioms-pr-branch.txt`, and how to rerun them in `raft-452/README.md`), and none of them reaches `sorryAx`.
`unstable.wp_stableTo` and `raftLog.wp_stableTo` rest on 294 axioms each: Lean's three
(`propext`, `Classical.choice`, `Quot.sound`) plus the opaque Go types and their
`underlying`/`zero_val` instances (standard library, protobuf internals). `raft.wp_Step`
rests on 304: those, plus raft's existing trust boundary (the nine `proto.*` specs,
`fmt.Errorf`, `DescribeConfChange`, `raftpb.ConfChangeType.String`). The `Logger` triples are not
axioms: they are a hypothesis carried in `ownUnstable` (`InvLogger.lean`) that a client of raft
supplies.

`etc/tcb-collections/pr-raft-452.txt` names these roots. `etc/tcb-report.py` was not run on
this branch: it requires every root of the repository to be up to date, and the changed
`Code.go_etcd_io.raft.v3` would mean rebuilding all of the server's proofs downstream of it. The
built modules were `Proof.go_etcd_io.raft.v3.Link` and `Proof.go_etcd_io.raft.v3.Results`, which
covers every raft proof (`raft-452/build-excerpt.txt`). So the collection's baseline lines are not written; a run of
`etc/tcb-report.py --collection etc/tcb-collections/pr-raft-452.txt --check --update` after a
full build fills them in. `etc/verified-code.py` would count the same for `go.etcd.io/raft/v3`
before and after: one function's body changed and it stays verified.

## Findings

- No bug in the PR.
- No bug in the existing code found. `issues/` has no finding about `stableTo`.
- Open point (not a bug): the term-mismatch exit stays at Info, though its own comment says
  it can happen in normal operation under async writes. The PR is scoped to the missing-entry
  message, as issue #307 asks.
- Reviewer's open point (client side, not a PR bug): raft's own `DefaultLogger.Debugf`
  (`logger.go`) reads `l.debug`, which `EnableDebug` writes without synchronization. With
  `DefaultLogger`, this path now reads that field, where `Infof` did not. A concurrent
  `EnableDebug` is a data race. This is not new in kind: raft already calls `Debugf` on many
  other paths (`raft.go`), so a client that calls `EnableDebug` concurrently races already. A
  client meets the `Logger` contract (`InvLogger.lean`) only when `debug` is fixed after setup,
  the usual use. `DefaultLogger` is not verified here.
- Not covered: the PR's motivation, that with async storage writes this exit is expected and not
  actionable. It is consistent with the spec: a miss leaves the state unchanged, and
  `raftLog.stableTo`'s caller only needs that.

## Draft review comment

> LGTM. The change only affects the level of the log line on the early return in
> `unstable.stableTo` when the entry is no longer in the unstable log; the state handling on
> that path (return without touching `entries`/`offset`) is unchanged. The other two early
> returns (index matched the unstable snapshot, term mismatch) stay at Info; the comment on the
> term-mismatch one says it is also possible in normal operation (the unstable log replaced
> while a write was in flight), so it may be worth deciding whether it should follow this one
> to Debug, here or separately.
