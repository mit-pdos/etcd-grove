---
upstream: none
checked: 2026-11-13
links:
blocks-proof: no
---
# etcd: `fileutil.Preallocate(f, n, true)` truncates a file longer than `n` when `fallocate` is unsupported or interrupted

`Preallocate`'s extending fallback `preallocExtendTrunc` (taken when `fallocate(2)` returns
`ENOTSUP` or `EINTR`) computes `size, _ := f.Seek(sizeInBytes, io.SeekEnd)`, the end *plus*
`sizeInBytes`, so its guard `if sizeInBytes > size { return nil }` never holds, and it always calls
`f.Truncate(sizeInBytes)`: a file longer than `sizeInBytes` is cut to `sizeInBytes`, losing its tail,
where the documentation promises only to "allocate the space for given file".

**Why not an issue:** a precondition etcd meets (found by code reading): every caller passes a size
at least the file's. The WAL preallocates fresh files (`filePipeline.alloc`, `wal.Create`: size 0)
and `ZeroToEnd` the length it measured before truncating to the current offset. The guard was
presumably meant to compare against the current size (`f.Seek(0, io.SeekEnd)`).
Code: [`preallocExtendTrunc`](https://github.com/etcd-io/etcd/blob/ea8b59433d82/client/pkg/fileutil/preallocate.go#L38).

## Proof

no: the spec of `preallocExtendTrunc` (and `Preallocate`'s, extending) takes `m.size ≤ sizeInBytes`
as a premise (`LinuxFs/Spec/go_etcd_io/etcd/client/pkg/v3/fileutil/preallocExtendTrunc.lean`), which
the WAL's calls meet.
