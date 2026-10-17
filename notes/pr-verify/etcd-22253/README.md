# etcd-io/etcd#22253: files the report relies on

The report is `notes/pr-verify/etcd-22253.md`. Revisions: the PR head is etcd-io/etcd
5cb98a85a969cc2e23962d397bfe46d598ba8d8f (upstream base 7d7f884852f728972bf1e20c3f26840b6bbeb94c);
the verified fork code is `mit-pdos/etcd-grove` branch `pr-etcd-22253-goose-lean` (commit 363c8a896 =
the fork pin 09669450f plus the PR, its test file included); etcd#22291's head is 71d57990b.

The tests are not new: they are etcd#22291's verification's (`notes/pr-verify/etcd-22291/`, see its
`README.md`), the PR's own `TestCloseRequireLeaderRemovesKeepAliveWithoutSubscribers`
(`client/v3/lease_internal_test.go` at the PR head) and etcd#22291's
`TestLessorCloseRequireLeaderRemovesOrphanedKeepAlive` (`client/v3/lease_requireleader_internal_test.go`
at 71d57990b).

| File | What it shows | Runs against | Command |
|---|---|---|---|
| `tests.log` | (1) at the PR head, both PRs' tests pass, and the etcd#22291 review tests observe the same as at 71d57990b: `ka.donec` left open on the delete path, and etcd#22081's mispairing (`TestLessorCloseRequireLeaderKeepsPairing` fails, as on every revision); (2) the PR's test fails on the upstream base; (3) the PR's test passes on etcd#22291's head. | the PR head, the upstream base, 71d57990b | copy `../etcd-22291/*.go` and 71d57990b's `client/v3/lease_requireleader_internal_test.go` into `<head>/client/v3/`, then `go test -count=1 -race -v -run 'TestReview\|TestLessorCloseRequireLeader\|TestCloseRequireLeader' .`; copy the PR's `lease_internal_test.go` into the base's and 71d57990b's `client/v3/` and `go test -count=1 -race -v -run TestCloseRequireLeader .` |
