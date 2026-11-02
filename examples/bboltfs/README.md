# bboltfs: the acceptance test of the Linux file extension

The least code that exercises every rule of the Linux file extension
(`GooseLang/Ext/OsFs/Impl.lean`, `notes/osfs-ext-plan.md`) that bbolt reaches. That code is
**minibolt** (`minibolt.go`), a two-meta-page store, and three programs over it. The OS calls
are bbolt's own (`bolt_unix.go`, `bolt_linux.go`, `db.go`, `tx.go` of the fork
`upamanyus/bbolt` `goose`), with bbolt's flags. The extension is good enough to approach bbolt
when the three programs are proved.

The trusted definitions themselves are checked by `GooseLang/Ext/OsFs/Tests.lean`. Those are
lemmas about the step and crash relations: misuse is stuck, a crash may lose an unsynced byte
and keeps a synced one, and so on. `linux_test.go` checks the Linux facts the model rests on
where they are not obvious.

## The programs

| program | spec | what it exercises |
|---|---|---|
| `testMinibolt` (`programs.go`) | `{{ True }} testMinibolt(dir) {{ RET true }}` | the sequential rules: OpenFile (O_RDWR\|O_CREATE), Flock, Stat, init's WriteAts and Fdatasyncs, Mmap (longer than the file) and Madvise, metas read through unsafe views of the mapping, a commit's WriteAt seen through the mapping, the remap (Munmap, then a larger Mmap), the grow (Truncate, then Sync), Close, then Open again, whose page-size read uses ReadAt before the mapping |
| `testMiniboltConcurrent` (`programs.go`) | the same | a `Get` and a `Snapshot` reader while the writer commits. The mapped loads are disjoint from the writer's in-flight changes. `Snapshot` (tx.go's `WriteTo`) copies the file with ReadAt up to the page the next commit writes, so the copy races that WriteAt, the Truncate and the meta WriteAt. Only the pages of its own transaction are claimed |
| `BootMinibolt` (`minibolt.go`) | its panics never fire, however often the node crashes | the crash relation: unsynced bytes, bytes lost by a failed sync, a file created since boot, a size not yet durable |

A program's claim is about the runs with no environmental failure. The model lets any system
call fail, and a program then stops and returns true (`envFailure`).

**minibolt** is bbolt with one value per transaction. A commit writes a new root page at the
high water mark, remapping and growing the file when needed. It fdatasyncs, then writes the
meta to slot `txid % 2` under `metalock`, then fdatasyncs again. `Get` and `Snapshot` are read
transactions under bbolt's locks. It differs from bbolt in two places, both bbolt bugs:
- **init.** bbolt makes the metas and the pages they point at durable with one `fdatasync`
  (`nonissues/bbolt-init-not-crash-safe.md`). minibolt syncs pages 2–3 first, then the metas, and
  redoes init when neither meta is valid.
- **A failed commit.** After a failed fdatasync, the commit's meta is in the page cache, and so
  in the mapping, without being durable. bbolt goes on serving it (the second consequence of
  `issues/bbolt-commit-meta-error-frees-reader-pages.md`). minibolt marks the handle failed and
  refuses every later transaction.

**The premise of the crash property, P1: no checksum collision on a torn meta (plan D1).** A
meta slot is the 64 bytes at offset 16 of page 0 or 1. At a crash, take a slot some of whose
bytes the crash relation makes arbitrary. If the image's 64 bytes there pass `Validate`
(`magic` and `version` match, and `checksum` is the FNV-64a of the first 56 bytes), then they
equal the meta of the last `WriteAt` to that slot, or the slot's durable bytes.

## What is not exercised

These are bbolt features minibolt leaves out, and the primitives they would add:
- `Options.ReadOnly`'s O_RDONLY open, and `CopyFile`'s O_TRUNC (the same Open rule, other
  flags);
- `Mlock`/`Munlock` (trivial models);
- `WriteTo` with a `WriteFlag` such as O_DIRECT, which the model refuses (stuck).

Outside the file model, one point is still open: the fork's `mmap` sets
`db.data = (*[common.MaxMapSize]byte)(unsafe.Pointer(&b[0]))`, the oversized array view that
Perennial's `unsafememory` replaces by `unsafe.Slice`. minibolt indexes the mapped slice
directly, as the patched form does.

## Go tests

`go test ./bboltfs/...`, from `examples/` and also under `-race`, checks:
- both programs return true on real Linux with no environmental failure, and the concurrent
  one does so 30 times;
- minibolt refuses every transaction after a failed commit, and re-initializes a file whose
  metas are both invalid;
- the boot program survives 30 boots, and SIGKILLs at arbitrary points;
- the Linux facts (`linux_test.go`): a store, or a failing CAS, on a `PROT_READ` mapping, and a
  load past EOF, die of SIGSEGV or SIGBUS as fatal errors, not panics; and a `WriteAt` is
  visible through a MAP_SHARED mapping without a sync.

Crashes cannot be tested in Go. A killed process loses nothing, because the page cache
survives, so the crash property is about the model only.
