---
upstream: none
checked: 2026-11-13
links: []
blocks-proof: yes
---

# fileutil: NewFileBufReader panics when fstat fails, on every WAL read

`fileutil.NewFileBufReader` calls `panic(err)` when the reader's `FileInfo` (an `fstat` of the WAL
file) fails ([filereader.go](https://github.com/etcd-io/etcd/blob/1b969e26a2c6/client/pkg/fileutil/filereader.go#L50-L54),
"This should never happen"). The WAL decoder builds one for each file
([decoder.go](https://github.com/etcd-io/etcd/blob/1b969e26a2c6/server/storage/wal/decoder.go#L63)),
so every `Open`, `OpenForRead`, `ValidSnapshotEntries` and `Repair` would panic instead of returning
the error.

**Why not an issue:** a precondition etcd meets: the WAL hands the decoder files it has just opened,
and `fstat` of an open descriptor of a regular file on Linux does no I/O and does not fail short of an
LSM policy denying `getattr` on a file it allowed to open. The test reaches the panic only through a
closed descriptor, which no etcd caller passes: `TestDecoderStatError` in
[etcd-fileutil-filebufreader-stat-panic/](etcd-fileutil-filebufreader-stat-panic/) (`NewDecoder`
over `fileutil.NewFileReader` of a closed file) panics at the fork's pin `0b50f0426` and at upstream
main `1b969e26a2c6` (2026-11-12) with `stat ...: file already closed`.

## Proof

yes: the WAL's proof over `fsExt`, where any syscall may fail (`fstat` included), needs the fix: on
the fork's local branch `goose-lean-walfs` (not pushed), `0fa9710dc` on the pin `0b50f0426`:
`NewFileBufReader` keeps the error (`FileBufReader.Err`, `FileInfo` nil) and the decoder returns it
from `Decode`; tests `TestFileBufReaderStatError` (fileutil) and `TestDecoderStatError` (wal) pass.
The alternative, an `fsExt` assumption that `fstat` never fails, goes against the model's rule
(`notes/wal-fsext-plan.md`, §0 item 5, Q5).

## Notes

The fix keeps `NewFileBufReader`'s signature (the package is public, in `client/pkg`). Upstream not
searched beyond "NewFileBufReader" (nothing).
