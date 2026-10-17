# Files for `notes/pr-verify/etcd-21845.md`

Revisions: upstream base = etcd-io/etcd `6640131cb64c6927ee94ba806de15c9c0471f110` (the PR's merge
base with `main`); PR head = `7b8af956ee27f2a911cc38f664ef9cb0d32ce436`; pinned fork =
`upamanyus/etcd` `goose-lean` `09669450f` (its `server/auth/store.go` is upstream's: the bug is
there too); fork branch = `mit-pdos/etcd-grove` branch `pr-etcd-21845-goose-lean` (`e45698e8c`:
`09669450f` plus the PR, its test included). Go toolchains: `go1.27.1` for the fork, `go1.26.4` for
the PR head (its `go.mod` names go 1.26).

| File | What it shows | Runs against | Command |
|---|---|---|---|
| `store_grant_downgrade_test.go` | `TestRoleGrantPermissionDowngradeSameKey`: write on `[foo, fop)` and `[foo, foq)`, then read on `[foo, foq)`; the user must no longer be able to write `fop`, and the role must hold 2 permissions | pinned fork `09669450f` (fails: write still permitted), fork branch (passes), PR head (passes) | `cp store_grant_downgrade_test.go <checkout>/server/auth/ && cd <checkout>/server/auth && go test -run TestRoleGrantPermissionDowngradeSameKey .` |
| `downgrade-base.log` | its failure at `09669450f` ("write on fop still permitted after downgrading [foo, foq) to read"; logger lines removed) | `09669450f` | as above |
| `store_grant_existing_duplicate_test.go` | `TestRoleGrantPermissionExistingDuplicate`: a role as an etcd without the fix stores it after write `[foo, fop)`, read `[foo, foq)`, write `[foo, foq)` (`[W fop, R foq, W foq]`, written through `UnsafePutRole`); downgrading `[foo, foq)` to read again must remove write access to `fop`. With the PR it does not: the PR updates only the first permission on the range (the read one) | PR head (fails), fork branch (fails) | `cp store_grant_existing_duplicate_test.go <checkout>/server/auth/ && cd <checkout>/server/auth && go test -run TestRoleGrantPermissionExistingDuplicate .` |
| `pr-head.log` | `go test -run TestRoleGrantPermission .` at the PR head with both tests above: the downgrade test and the PR's tests pass, the existing-duplicate test fails (the stale `WRITE` permission on `[foo, foq)` is kept) | PR head | `cp *_test.go <pr-head>/server/auth/ && cd <pr-head>/server/auth && go test -run TestRoleGrantPermission .` |
| `store_grant_reviewer_test.go` | the reviewer's probes: A, 3000 random grants/revokes against a map model (no duplicates, sorted, types as the model, up to 46 permissions: past `sort.Sort`'s insertion-sort size); B, nil and empty `RangeEnd` are one range; C, `[a]` and `[a, "a\x00")` are two spellings of one range, a downgrade through the other spelling keeps write (pre-existing); D, a role stored unsorted (no etcd writer does this) defeats the scan: the `SortedByKey` premise is needed. C and D only log | PR head (all pass; C/D log what they observe) | `cp store_grant_reviewer_test.go <pr-head>/server/auth/ && cd <pr-head>/server/auth && go test -v -run TestReviewer .` |
| `reviewer-pr-head.log` | its output | PR head | as above |

On the fork branch, `go build ./...` and `go test ./auth/` in `server` pass (with the PR's test).
The PR's own `TestRoleGrantPermissionSameKeyDifferentRangeEnd` fails at `09669450f` (3 permissions,
the duplicate) and passes with the PR.
