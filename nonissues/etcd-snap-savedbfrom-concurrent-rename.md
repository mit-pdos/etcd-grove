---
upstream: none
checked: 2026-11-13
links: []
blocks-proof: yes
---

# snap: two concurrent `SaveDBFrom` calls for one index both write the file, the second replacing the first

`Snapshotter.SaveDBFrom(r, index)` checks whether `<index>.snap.db` exists and renames its temporary
file onto that name only if it does not, but with no lock between the check and the rename. Two
concurrent saves of the same index (two snapshot streams of one index received at once, or, in one
process, a stopped server's snapshot handler still streaming while the restarted server receives
the same snapshot again) can both pass the check, and the second rename replaces the file the first
one wrote. Both calls return nil.

**Why not an issue:** no wrong result etcd shows: both files are snapshots of the same index,
which etcd treats as interchangeable (hence the kept-file branch). Their data can differ (two
members' databases at one applied index differ in a compaction's progress, which
`scheduleCompaction` makes in batches without moving the applied index), but every reader opens
whichever file is there, so the difference is invisible. The test shows only the double rename.

## Proof

yes: the axiom `snap.Snapshotter.SaveDBFrom.spec`
(`Spec/go_etcd_io/etcd/server/v3/etcdserver/api/snap/Snapshotter__SaveDBFrom.lean`) states a kept
file's ghost step as nothing, and the snapshot directory's invariant (`snapDirInv`,
`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/Net.lean`) records the data of the file at
each saved index (`backend.fileHolds p D`), which `snapDir_take`
(`Proof/go_etcd_io/etcd/server/v3/etcdserver/SnapRO.lean`) hands to the apply thread to open. With
the double rename the second writer's file replaces the first's, and the recorded data is false
when the two differ: the certificate `img i D` the stream carries does not determine `D` (the
image leaves a compaction's progress free), so "both writers' data are the same" cannot justify
it (restart S6a item 4, 2026-11-13).

**Fixed on the fork** (restart S6a, 2026-11-13; the user's decision via etcd-grove-81):
upamanyus/etcd@2eaeb872b (branch `goose-lean-snaplink`, on 0b50f0426; the pin of `etc/goose.py`'s
`etcd` project) links the temporary file to the path (`os.Link`, which never replaces a file),
takes `ErrExist` as the kept file, and removes the temporary file: of two concurrent saves of one
index exactly one puts its file in place. Its test `TestSaveDBFromConcurrentSameIndex`
(`server/etcdserver/api/snap/db_test.go`: 500 iterations of two concurrent saves of one index with
different data from two snapshotters of one directory; after both return exactly one logged the
save and the file holds its data, and no temporary file is left) fails at 0b50f0426 (iteration 1:
both saves put their file in place) and passes at 2eaeb872b. The ghost steps of the axiom are then
those of the code.

## Notes

Found by the restart S6a axiom review (2026-11-13). The user first decided (via etcd-grove-81) on no
code change and a restated justification; when that justification turned out false (the image does
not determine the data), the user decided on the fork's fix (2026-11-13, via etcd-grove-81). The
review's test calls `SaveDBFrom` from two goroutines on two snapshotters of one
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
branch). The fork's fix is the one this suggested: `os.Link` then remove, so that the second writer
takes the kept-file branch.
