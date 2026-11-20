# Brief: `wal-fsfix`, the WAL's file-model fixes and no-error proofs (follow-up of L3)

Split from `wal-link` by the user's decision of 2026-11-19 (via etcd-grove-03): L3 lands with `rnNewStorageOk`
kept as the premise it is, and with no new trusted file-model text; this branch carries the rest.

- **Branch** `wal-fsfix`, off `wal-link` e6a0c0a811; head 9017eb196d (F1 (a), A2, A3, measurements). Rebase or
  merge onto `lean` once L3 has landed (L3 reverted 3778c95957's and a50580df93's code on `wal-link`: re-apply
  them here, `git revert` of `wal-link`'s revert commit, or cherry-pick 3778c95957 and a50580df93's code).
- **Read first:** `notes/wal-units/noioerr.md` (sessions 4-6: option (a), item 3/`PathErrno`, the attacks F1, F2,
  A1-A3, the bbolt check), questions.md entries of 2026-11-19 (the user's approvals; 03's decisions).

## In order

1. **F1 (priority: a soundness bug in the existing trusted semantics, on `lean` today).** A lock outlives its fd's
   `close` while a mapping made through the fd is live; `lean`'s `Close` releases it, so the model excludes Linux's
   `EAGAIN`. Fix approved (option (a)): `MapDesc` in `Impl.lean`, done in 9017eb196d, `GooseLang/Ext/Fs/*` builds.
   Left: rebuild bbolt's and the WAL's proofs over it (STOP if one breaks non-mechanically); the independent attack
   launched 2026-11-19 (programs `/shared/tmp/wallink-attack3/`, its read-only checkout `/shared/tmp/wallink-fsfix-ro`)
   — read its result, fix what it finds, re-attack if trusted text changes. Open lead: Go's `poll.FD` defers
   `close(2)` while another goroutine is inside a syscall on the same file (a second way a description outlives the
   model's `Close`).
2. **A2** (C's permissions: search/write, no sticky, immutable, append-only or LSM denial): done in 9017eb196d
   (texts + `TestNoIoErrPermissions`); covered by the same attack.
3. **A1** (ENAMETOOLONG): the approved "stuck" form puts a length premise on every path WP spec and every caller;
   NOT implemented. Ask the coordinator/user whether to take the cheaper sound form: such paths are not covered by
   `IoCovers` (nor `PathErrno`); only the no-error specs then need a WAL-dir length premise. Measurement written
   (`TestNoIoErrNameTooLong`).
4. **NoIoErr (a) and `PathErrno`** (3778c95957, a50580df93: approved; `PathErrno`'s guarded form accepted by 03):
   re-apply after L3; their attack is done (noioerr.md).
5. **The configuration-C run** of every new measurement, by the user, from a named commit:
   `examples/osfs/semantics/run-models-on-c.sh -run 'TestLocksMmapKeepsDescription|TestNoIoErrLocks|TestNoIoErrReaddir|TestNoIoErrPathErrno|TestNoIoErrPermissions|TestNoIoErrPermHelper|TestNoIoErrNameTooLong|TestLocks'`
   (as root, so that the permission contrast runs).
6. **`WAL.cut.specNoErr`** (flag-parametrized proof; callee NE specs: Truncate, sync.specCut, fp.Open, Rename, dir
   Fsync, Close, LockFile — its no-conflict now also needs "no held description of the inode", Seek), then
   **`Create.specNoErr`** (renameWAL's `RemoveAll` via `noIoErr_pathErrno`), then **`rnNewStorageOk_holds`**
   (hand-linked; tcb-report must see it linked) and `rnNewStorageOk` out of `etcdstart.premises` and its copies
   (leaseexpiry/auth/putget3/OneMember): a closed-statement change, STOP with old → new.

## The attack on 9017eb196d (2026-11-19, read-only subagent, axiom skill; programs `/shared/tmp/wallink-attack3/`)

- **(1) MapDesc: holds as far as it goes** (`TestLocksMmapKeepsDescription` 3/3; partial and failed `munmap` match;
  Go's `poll.FD` deferred close cannot reach a proved program: `wp_osClose` needs the whole `osFd`). **Refutation,
  pre-existing on `lean` too:** another process reading `/proc/<pid>/fdinfo/<fd>` (also `readlink /proc/<pid>/fd/N`,
  `pidfd_getfd`, ptrace; lsof, monitoring agents) holds a short reference to the description (`fs/proc/fd.c`
  `seq_show`: `get_file`/`fput`), so its locks outlive `close(2)`: a non-blocking re-lock gets `EAGAIN` with no
  conflict in the model (`procrace/main.go`, 200 000 rounds: OFD 837 + 6261, flock 3312 + 18583 EAGAINs with the
  reader, 0 without). False: `LockStep`'s "EAGAIN only on a conflict", `locks_close_crash.go`'s "Excluded",
  MapDesc's/header's "otherwise the description and its locks go". etcd's `wal.Open` uses `TryLockFile`
  (non-blocking). Proposed fix: an environment clause (no other process takes a reference to the process's open
  files: no `/proc/<pid>/{fd,fdinfo,map_files}` reads, `pidfd_getfd`, ptrace), or let a non-blocking request fail
  with `EAGAIN` without a conflict (weakens NoIoErr's lock clause). A decision for the user.
- **(2) Permissions: gaps.** Search permission on the roots' ancestors (measured: EACCES as nobody under a 0700
  ancestor) and `fs.protected_symlinks` on a symlinked ancestor; `EOVERFLOW` from `may_create` for unmapped ids on an
  idmapped mount (measured here); file permissions for opens for write; `fs.protected_regular`; seccomp filters;
  fanotify permission events. Proposed: extend the sentence with each (or require no sticky covered directory).
  Test comments "may not write" → "may not search or write" (the child's EACCES is a search failure).
- **(3) A3's new wording is FALSE:** `os.Remove` returns unlink's ENOENT when rmdir says ENOTDIR, so `RemoveAll`
  returns nil at once (go1.27.3 `file_unix.go:357-388`, `removeall_at.go`). The old sentence was right; proposed:
  "returns nil at once exactly when `Remove`'s error is ENOENT: rmdir's ENOENT, or rmdir's ENOTDIR after unlink's
  ENOENT; with any other errno it opens the parent and goes on, which may end in nil or not."

## Rules

Common rules (`/shared/tmp/coord-81/common-rules.md`); CLAUDE.md's extension rules (every trusted decision has a
Go example in `examples/osfs/semantics/`, indexed in `doc.go`; configuration C only). Trusted text: STOP for the
coordinator before any proof uses it, after an independent attack.
