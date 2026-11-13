# Fork commits pending the user's push (WAL over fsExt)

On upamanyus/etcd, branch `goose-lean-walfs`, on the pin `0b50f0426`: apply with `git am notes/wal-fsext-fork/*.patch`.
They fix the two blocks-proof nonissues `etcd-fileutil-filebufreader-stat-panic` and
`etcd-wal-create-cleanup-panic` (`notes/wal-fsext-plan.md`, section 8). After the push: bump the etcd pin in
`etc/goose.py` and the examples' go.mod/go.sum.
