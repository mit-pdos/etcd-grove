---
upstream: none
checked: 2026-11-14
links: []
blocks-proof: no
---

# Go os: `File.ReadFrom` undercounts when `copy_file_range` falls back after progress

`(*os.File).ReadFrom` (Go 1.27.3, `os/zero_copy_linux.go:89`) copies with
`poll.CopyFileRange` (`internal/poll/copy_file_range_unix.go:13`), which loops over
`copy_file_range(2)` rounds and, through `handleCopyFileRangeErr`
(`copy_file_range_linux.go:95`), reports "unhandled" (`handled = false`, `err = nil`) on `ENOSYS`,
`EXDEV`, `EINVAL`, `EIO`, `EOPNOTSUPP` or `EPERM` even when earlier rounds of the same call already
copied bytes (`written > 0`). `readFrom` then falls back to `spliceToFile` and
`genericReadFrom`, which copy the rest from the source's (advanced) offset, and `ReadFrom` returns
only the fallback's count: the bytes of the first rounds are in the destination but missing from
the `n` that `io.Copy` returns.

**Why not an issue:** reachable only if the kernel returns one of those errnos after a successful
round of the same copy, which on configuration C (Linux 7.0, ext4) needs an I/O error part way
(`EIO`); the comments of `handleCopyFileRangeErr` assume those errnos come only before any data.
etcd's one `io.Copy` of files (`wal.Repair`, `repair.go`) discards the count. Found by code
reading while modelling `copy_file_range` (`notes/wal-fsext-plan.md`, "io.Copy log"); no test
(it needs fault injection in `copy_file_range`).

## Proof

no: the model (`LinuxFs/TrustedCode/os.lean`, `model.copyFileRangeRound`) allows that outcome
(`PRead` may fail with any errno at any round), so the `io.Copy` triple of `Repair` claims nothing
of the count.
