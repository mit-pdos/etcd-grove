# etcd-io/etcd#22518: files the report relies on

The report is `notes/pr-verify/etcd-22518.md`.

| File | What it shows | Revision | Command |
|---|---|---|---|
| `pr-tests.log` | The PR's own tests (`Test_t1`–`Test_t5`) and the existing `TestSaveDBFromSyncsDirectory` pass on the fork branch with the PR applied. | `mit-pdos/etcd-grove` branch `pr-etcd-22518-goose-lean` (`82ce41f6f`), plus the PR's `*_test.go` changes (`git diff 64f26db45 7a68a7c89 -- '*_test.go'`, applied for the run and then removed) | `cd server && GOTOOLCHAIN=go1.27.1 go test -count=1 -v -run 'Test_t\|TestSaveDBFromSyncsDirectory' ./storage/ ./etcdserver/api/snap/` |

No Go test or probe was written for a finding. The run found no bug in the PR. Its points are
about the tests and the code's structure, and no test can show them.

The reviewer ran the same PR tests at the PR head, in a scratch upstream worktree, and they passed
there too. The PR's failure path (the directory sync fails after the rename) has no test in the PR,
and none could be written here without a seam. The environment runs as root, so permissions cannot
make `fileutil.OpenDir` fail. `DBFilePath` reads the directory before the rename, so making the
directory unreadable fails the call earlier. The proof covers that path instead (the `(nil, err)`
branch of the spec).
