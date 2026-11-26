# S5 (egos): etcd-grove `os`, `syscall`, `x/sys/unix`, `examples/lib/durable` — DRAFT (proofs not finished)

Branch `go-models-rest/2026-11-24` (etcd-grove), head bb9a798186. Not complete: the Proof/os port is in
progress (gmr-egos/resume.md); no tcb-report / #print axioms / review-trusted yet.

## What changed
- `os`: `file` (Go's layout plus the model's `off`) and the real `fileStat` are translated; `OpenFile`,
  `Close`, `ReadAt`, `WriteAt`, `Seek`, `Write`, `Read`, `Stat`, `Truncate`, `Sync`, `Rename`,
  `Readdirnames`, `Stat`/`Lstat`, `RemoveAll`, `copyFileRange` are Go models (models/os/model.go, a
  `MODEL:` comment each) over 19 primitive stubs (models/os/stubs.go; `.impl`s in TrustedCode/os.lean,
  one extension op each). Real Go now: `File.Fd`/`fd`, `readFrom`, `spliceToFile`, `rawConn.*`,
  `MkdirAll`, `Mkdir`, `Remove`. TrustedCode/os.lean 1539 -> 202 lines; syscall 293 -> 144.
- `syscall`: models of `errnoErr`, `Errno.Error` (arbitrary string), `init.0`, `Fdatasync`, `Flock`,
  `Fallocate`, `FcntlFlock`, new `Mkdir`/`Unlink`/`Rmdir`; egnet's `Errno.Timeout/Temporary` and the
  errno constants translated (merged 7979b955cc).
- `durable`: `Read`/`Write` one-line models over the durable extension's stubs.
- Premises removed: `[os.file.FieldAssumptions] [os.fileStat.FieldAssumptions]` from every statement
  (169 files, incl. the top-level etcd/k8s/bboltfs/walfs/kvnet results) and from bbolt's `FsCtx`.
  No new axiom, premise or translator change.

## Decisions taken in the port (pre-approved class: untrusted proofs, no new premise)
- `os.ownFile` gains `nonblock ↦□ false` (the real `File.fd()` reads it).
- `internal/filepathlite`'s lexical functions get precondition-free lemmas (`Lexical.lean`,
  `<F>.wp_lex`), since the package's fact is `True` and the os specs carry no `isPkgInit`; the
  specs are unchanged and `Base.wp_proof` is derived from `Base.wp_lex`.
- `supportsCreateWithStickyBit` added to os's `translate` list: it was `opaque` (a stuck `!` in Go's
  `Mkdir`); now the constant `true` (sticky_notbsd.go).
- Go's `ignoringEINTR` gets one lemma (`os.wp_ignoringEINTR`); `os.Mkdir` is proved once below a
  root for any per-attempt resource (`os.Mkdir.wp_tree`) and once at a root or above (`wp_notTree`).

## x/sys/unix stays hand-written Lean (167 lines)
A Go model was drafted (gmr-egos/unix-model-attempt/) and not adopted: `x/sys/unix` is not a standard
package, so it cannot import `internal/gomodel` (each Stuck/Choose would need a per-package stub with
gomodel's `.impl`); `Mmap`'s result is the extension's mapping base, which a Go stub would have to
return as an `unsafe.Pointer` (a gc body converting mmap's uintptr, which vet flags) for
`unsafe.Slice` to build the slice as the Lean model does; and `Munmap`'s registry is the skipped
package variable `mapper`. The Lean models stay (Mmap, Munmap, Madvise, Fallocate, FcntlFlock), as
reviewed before. Open item.

## GODEBUG (the lead's decision)
`Setenv`/`Unsetenv`/`Clearenv` (and os's) are neither translated nor modelled in these configurations;
a note in models/syscall/model.go says a future model must be stuck on key "GODEBUG".

## Evidence
- `etc/model-tests.sh os syscall durable` (go1.27.3, Perennial pgmR-xtools 78d6ef937): all ok.
  os row: the plan's tests (ReadAt, WriteAt, Seek, Truncate, MkdirAll, Remove, RemoveAll, Rename, Stat,
  Readdirnames). Left out, each with its reason in etc/gomodels.py: Stuck (O_APPEND, Readdirnames(n>0));
  mode-bit choices (gc 0); pipes, symlinks, PATH_MAX paths, a strace child (outside the extension, where
  the stubs' gc bodies differ from Go); concurrent Write (the model updates `off` without Go's lock:
  more outcomes, documented); fsLstatDir's gc body answers EEXIST only (TestRenameNotExisting).
  The earlier RemoveAll "hangs" were not model loops: failing tests printed through the model's
  File.Write on a pipe (pwrite: ESPIPE, then the offset unknown, then Stuck); fsPWrite's gc body now
  falls back to write(2) on ESPIPE (gc only; the GooseLang model is unchanged).
- Builds: syscall Base/PkgInit/ErrorOk/FileOps/Flock/Fdatasync/FallocateAu, os PkgInit, durable
  Read/Write build (build6); the rest of Proof/os pending.
