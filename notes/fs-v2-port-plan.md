# Plan: porting the program logic and the clients to the file extension v2

**Date:** 2026-11-06. **Status:** in progress. The semantics is `GooseLang/Ext/Fs/{Paths,Tree,Impl}.lean`
(`notes/fs-semantics-v2.md`); the trusted Go models call it (`TrustedCode/{os,syscall}.lean`,
`TrustedCode/golang_org/x/sys/unix.lean`). The first version's program logic and its clients are in
`old/osfs-v1/` (not built), to be ported here, file by file, under `GooseLang/Ext/Fs/` and the
original client paths.

## Done first (the risks)

- **Closed-set crashes.** A crash keeps a set of log entries closed under `Follows`, not a prefix.
  For a program whose metadata calls never overlap, every entry's call began when the log held the
  entries before it (`Sequential`), and a closed set is a prefix (`Crash.lean`, `crash_seq`): the
  prefix reasoning of the first version carries over. Every client so far is sequential.
- **Sectors.** The program logic keeps its per-byte ghost resources; a byte every version of its
  sector holds, and no change in flight may change, is what every crash leaves (`Bridge.lean`,
  `crash_keeps_clean`).

## Module map (old → new, `GooseLang/Ext/Fs/`)

`Ghost` (and `Cells`, `Facts`, `Heap`, `SemCongr`) → same names; `Specs`, `Write`, `Truncate`,
`TruncateShrink`, `Falloc` → same; `Crash`, `CrashTok`, `CrashQT`, `CrashP1`, `Adequacy` →
`CrashFiles`, `CrashTok`, `CrashQT`, `CrashP1`, `Adequacy`; `NsGhost`, `NsView`, `NsLemmas`, `NsMove`,
`NsSpecs*` → `TreeGhost`, `TreeView`, `TreeLemmas`, `TreeSpecs*` (`NsMove` is gone: a directory's
rename moves one entry); `CrashNs` → `CrashTree`; `Tests`, `TestsNs` → `Tests` (the semantics' own
tests stay) and `TestsSpecs`. The prelude `Proof/OsFsPrelude.lean` → `Proof/FsPrelude.lean`.

## The ghost state

- **Keys.** Files, bytes and metadata by inode (`Ino`), not by path; fds by number, holding an
  inode; directory fds by number, holding a directory inode.
- **`OsMeta`.** Drops `named` (whether a name survives is the tree's question) and `durHi`. Keeps the
  size, the crash bounds of the size `lo`/`hi`, `ok` (no sector is lost: none is clean with more than
  one version), the mappings, and `dur` (known durable bytes): `dur[b] = some d` means every version
  of `b`'s sector holds `d` at `b` (so a crash leaves `d` there, `Bridge.lean`).
- **Clean bytes** (`CleanPhys f b`): `b < f.sizeLo` and every version of `b`'s sector holds the page
  cache's byte at `b` (`HoldsAt`, and `∀ v ∈ vers`). A sync makes every dirty, idle sector clean.
- **The tree.** One ghost element, the history `V = (treeDur, metaLog)` (log entries with their
  starts), held as `osTree dq V`; a directory's view by inode, `dview V j : DirG` (its entries in
  `treeDur` and the entry operations on it along the log: `create j b i` puts `b`, `mkdir j b j'`
  puts `b`, `remove j b _` deletes `b`, a rename moves within `j` or deletes/puts across), with
  `osDir j dq g`. No `AllDir`: a directory's entries are its inode's. A path's resolution is a pure
  fact about `V` (`OsState.lookup` over `replay`).
- **Calls.** `CallBegin` gives a token `osCall t start`; a metadata step's spec takes the whole
  history and a token whose `start` is the history's length, so the log stays `Sequential` (the
  ghost coherence records it), and a crash keeps a prefix.
- **Directory fds** hold a fraction of the history from open to close (as in the first version), so
  the holder of the whole history knows none is open; they are no longer needed for that
  (a rename or rmdir with an fd open is allowed), but the read's view needs the directory unchanged
  while it is read, so keep it.

## Order

1. `Ghost` and its satellites (the state interpretation, `OsWf`/`OsCoh` by inode, the tree history,
   tokens, init). Everything depends on it.
2. In parallel: the data path (`Specs`, `Write`, `Truncate*`, `Falloc`), the tree (`Tree*`).
3. The crash interpretation and adequacy (`CrashFiles`, `CrashTok`, `CrashQT`, `CrashP1`,
   `CrashTree`, `Adequacy`).
4. The `os`, `syscall` and `unix` specs (`Proof/os`, ...), then the clients (bbolt, crashlog, segdir,
   seglog, dirswap). Their theorem statements' diffs go to the user before they are committed.
5. Gates (`gen-init`, links, TCB baseline, collections), `notes/STATUS.md`.
