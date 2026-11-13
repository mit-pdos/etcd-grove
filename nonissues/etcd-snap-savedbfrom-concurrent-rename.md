---
upstream: none
checked: 2026-11-13
links: []
blocks-proof: no
---

# snap: two concurrent `SaveDBFrom` calls for one index both write the file, the second replacing the first

`Snapshotter.SaveDBFrom(r, index)` checks whether `<index>.snap.db` exists and renames its temporary
file onto that name only if it does not, but with no lock between the check and the rename. Two
concurrent saves of the same index (two snapshot streams of one index received at once, or, in one
process, a stopped server's snapshot handler still streaming while the restarted server receives
the same snapshot again) can both pass the check, and the second rename replaces the file the first
one wrote. Both calls return nil.

**Why not an issue:** no wrong result: both files are snapshots of the same index, which etcd
treats as interchangeable (hence the kept-file branch); the test shows only the double rename.

## Proof

no: the axiom `snap.Snapshotter.SaveDBFrom.spec`
(`Spec/go_etcd_io/etcd/server/v3/etcdserver/api/snap/Snapshotter__SaveDBFrom.lean`) states a kept
file's ghost step as nothing; its docstring's justification (restart S6a, M2) covers a rename over an
existing file, including one the apply thread already took to open (`snapDir_take`,
`Proof/go_etcd_io/etcd/server/v3/etcdserver/SnapRO.lean`): the stored image is a function of the
index (every save at `i` carries the certificate `img i D`), and the file claims are data-level
(`fileHolds`), so the claim on the file stays true.

## Notes

Found by the restart S6a axiom review (2026-11-13); the user decided (via etcd-grove-81) that no
code change is wanted. The test calls `SaveDBFrom` from two goroutines on two snapshotters of one
directory, as rafthttp's snapshot handler calls it:
[`nonissues/etcd-snap-savedbfrom-concurrent-rename/s6a_review_test.go`](etcd-snap-savedbfrom-concurrent-rename/s6a_review_test.go),
copied into `server/etcdserver/api/snap` at etcd-io/etcd@673da07c8fabc5a544d0017ff0cc241802bcd9b1
(the goose fork's pin), go1.27.1:

```
$ go test ./etcdserver/api/snap -run TestS6aTwoSnapshottersDoubleRename -v -count=1
    s6a_review_test.go:62: both renamed (TOCTOU) in 2749 of 3000 iterations
--- PASS: TestS6aTwoSnapshottersDoubleRename (20.94s)
```

It counts the iterations in which both calls logged "saved database snapshot to disk" (the rename
branch). A fix, if wanted: rename without replacing (`RENAME_NOREPLACE`, or `os.Link` then remove),
so that the second writer takes the kept-file branch.
