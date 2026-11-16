---
upstream: none
checked: 2026-11-14
links: []
blocks-proof: no
---

# fileutil (the Goose fork only): `TouchDirAll` returns success without syncing the parent of an existing directory after a failed `Stat`

The fork's `TouchDirAll` (upamanyus/etcd, the WAL part's translation, `client/pkg/fileutil/fileutil.go:49`;
the fork's F-N2 change) fsyncs the parent of `dir` when `Exist(dir)` reports it present, and otherwise fsyncs
the parent of each directory its loop finds missing (`created`). If `dir` exists but the first `os.Stat(dir)`
fails (any errno: a transient `EIO`, `ENOMEM`), the loop's own `Exist(dir)` may then succeed, so `created` is
empty, `os.MkdirAll` returns `nil` on the existing directory, and `TouchDirAll` (and `CreateDirAll`) returns
`nil` with no fsync of `dir`'s parent: `dir`'s entry need not survive a power failure.

**Why not an issue:** found by code reading, in the fork's own durability change (upstream `TouchDirAll`
syncs nothing and promises no durability); reaching it needs a `Stat` failure on an existing directory
followed by a success. No test.

## Proof

no: `wal.Create` does not rely on `CreateDirAll`'s commit of the temporary directory (its commit bound comes
from `syncDir(nm.tmp)` and the later fsync of the WAL directory's parent); the spec it uses,
`fileutil.CreateDirAll.specTmp`, drops the commit bound (`notes/specs-only/ledger.md`, 2026-11-14,
"the commit bound on an existing directory"). A fix would sync `filepath.Dir(dir)` whenever `created` is
empty.
