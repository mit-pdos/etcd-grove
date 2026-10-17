# etcd-io/raft#96: files behind the report

The report is `../raft-96.md`. Everything here runs against **upstream** raft, not the Goose fork:
the PR head `0e643b1b3eea6529572c08741f7ef920c13ba40d` (branch `pr-raft-96` in `~/etcd`, fetched
from `raft-upstream pull/96/head`) and its merge base with upstream `main`,
`89c97ed7f982084796b5572693fac6f3d6a995f7` (gogoproto raftpb, `[]pb.Entry`).

| File | What it shows |
|---|---|
| `log_unstable_mem_test.go` | Three probes, in package `raft` (copy next to `log_unstable.go`). `TestUnstableRetainedMemoryIssue71`: the append/persist sequence of raft#71 retains 162 MB of entries when no more than 64 MB were ever unstable, on the base **and** with the PR (the PR does not fix #71). `TestUnstableRetainedMemorySpareCap`: 60 entries of 1 MB in an array of capacity 100, the first 29 persisted: the base copies the 31 left out and keeps 31 MB; the PR keeps the array, 60 MB (a regression: the old `len*2 < cap` check is gone). `BenchmarkUnstableStableToLongLog`: `stableTo` of one entry on a 10000-entry unstable log, ~1-1.6 us/op on the base, ~0.3-0.76 ms/op with the PR (the new O(len) `proto.Size`/`Size()` loop on every partial `stableTo`). |
| `results.log` | The output of the commands below on both revisions (2026-10-16, a loaded 32-core machine; the benchmark's absolute numbers vary between runs, the ratio stays above 300x). |

Commands, in a checkout of either revision (`git -C ~/etcd worktree add --detach <dir> <rev>`):

```
cp log_unstable_mem_test.go <dir>/
cd <dir>
GOTOOLCHAIN=go1.27.1 go test -run TestUnstableRetainedMemory -v .
GOTOOLCHAIN=go1.27.1 go test -run XXX -bench BenchmarkUnstableStableToLongLog -benchtime 20000x -benchmem .
```

Expected: on the base, `...Issue71` fails (162 MB) and `...SpareCap` passes (31 MB); with the PR
both fail (162 MB, 60 MB). Retained memory is measured with `runtime.ReadMemStats` after two
`runtime.GC()`s, so it counts entries kept alive by the backing array before the slice's start.
