---
upstream: none
checked: 2026-11-14
links:
  - etcd-io/etcd#10689 pr merged: related (added `cleanupWAL` and the parent-directory fsync's error path)
blocks-proof: yes
---

# wal: Create returns a nil WAL and a nil error when the parent directory's fsync fails

When `wal.Create` has renamed the new WAL directory into place and the fsync of its parent fails,
it calls `dirCloser()`, which assigns the close's result to the same variable `perr` that holds the
fsync's error. When the close succeeds, `perr` becomes `nil`: `Create` returns `(nil, nil)`, its
deferred `cleanupWAL` (run only on `perr != nil`) is skipped, and the WAL stays open with its lock
file and file pipeline. Its caller `bootstrapNewWAL` checks only the error and then dereferences
the nil WAL (`w.SetUnsafeNoFsync()` with `--unsafe-no-fsync`, or later through `bootstrappedWAL.w`): a
nil-pointer panic. Code: [wal.go](https://github.com/etcd-io/etcd/blob/d622ec5/server/storage/wal/wal.go#L223-L233)
(`if perr = fileutil.Fsync(pdir); perr != nil { dirCloser(); ...; return nil, perr }`, with
`dirCloser` doing `if perr = pdir.Close(); perr != nil {...}`); the same at the fork's pin `0b50f0426`
and on `goose-lean-walfs`.

**Why not an issue:** found by code reading, no test: reaching it needs fsync(2) of the parent
directory to fail (EIO on ext4) after the open of the same directory succeeded, which etcd's test
harness cannot inject (no failpoint there; a faulty block device, dm-error or dm-flakey, would).

## Proof

yes: `Create.spec`'s success arm promises the open WAL handle when the error is `nil`, and over
`fsExt` the parent's fsync may fail (`fileutil.Fsync.specDirS`) and its close succeed, so the arm is
false on this path. The fix, `pdir.Close()` in place of `dirCloser()` on that path (the fsync's error
returned, the cleanup run), is `notes/wal-fsext-fork/0005-wal-keep-the-parent-fsync-error-in-Create.diff`
(pending the user, with 0001-0004); until it is on the fork and translated, `Create.wp_proof` keeps a
marked `sorry` on that path (W4 log, twenty-fourth session).

## Notes

Upstream not searched beyond `dirCloser`.
