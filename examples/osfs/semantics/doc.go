// Package semantics explains, by small Go programs, each decision of the Linux
// file extension's trusted semantics (GooseLang/Ext/Fs/{Impl,Tree,Paths}.lean,
// with the trusted models TrustedCode/{os,syscall}.lean and
// TrustedCode/golang_org/x/sys/unix.lean) and of the client premises a theorem
// may state beyond it (GooseLang/Ext/Fs/Premises.lean).
//
// Each file is one decision: its doc comment says what the model does, the
// Lean names that encode it, the outcome it allows or excludes, and why
// (measured, documented with a citation, or assumed), and which client needs
// it; then a function shows the scenario, with "crash here" and the outcomes.
// The functions are illustrations: nothing calls them, and no Goose
// translation or proof covers this package (models_test.go runs the
// measurements the model_*.go files cite). Every claim is about the target
// configuration C (env_config.go); the measurements cited were made on C with
// the scripts in notes/axiom-review/fs-config/ (and fs-v2-f3/, fs-v2-r4/,
// fs-v2-r6/).
//
// The rule (CLAUDE.md): every change to the trusted semantics adds or updates
// the file of the decision it changes, in the same commit.
//
// Environment assumptions (hypotheses of the adequacy statement):
//
//	env_config.go                 the target configuration C         Impl.lean header, pageIn
//	env_device_no_garbage.go      a device write leaves old or new   CrashFile (candidates only)
//	env_no_failed_writeback.go    no failed writeback (F1)           Fsync (failure: no change), ReadSees
//	env_durable_at_first_start.go durable at first start (F2)        FsInit (fs_semantics.initLocal)
//	env_fresh_process.go          a first start has nothing open      FsInit (proc = ProcState.empty), fs_semantics.initLocal
//	env_restarts.go               restarts are machine crashes       OsCrash := MachineCrash
//	env_journal_order.go          metadata in journal order          Follows, Closed, MachineCrash, DirSync
//	env_roots_only.go             only the roots' trees              TreeName, TreePath, AtOrAboveRoot, CanonBelow, RootsOk
//	env_no_close_during_lock.go   no close of an fd while a lock     Impl.lean header ("Environment", "Locks"),
//	                              call on it is in flight            LockStep, Close; NoIoErr ("Fds and locks")
//	                              (2026-11-19)
//
// File contents and sizes:
//
//	data_crash_candidates.go      each byte any of its candidates    OsFile.cache/cand, announce, synced, CrashFile
//	data_torn_source_page.go      a write torn at a source page (A)  CrashFile (measured)
//	data_mixed_writeback.go       a rewrite during writeback (B)     CrashFile (measured)
//	data_failed_fsync.go          a failed fsync changes nothing     Fsync
//	data_sizes_since_sync.go      any size in [sizeLo, sizeHi]       OsFile.sizeLo/sizeHi, CrashFile
//	data_resize_chunks.go         partial resize (F5)                CrashFile (targets), FallocFinish
//	data_durable_zeros.go         pages past a durable size: zeros   diskByte, OsFile.ofDisk, OsFile.synced
//	data_append_old_block.go      the end's block is not ordered     diskByte (the end's page), CrashFile
//	data_writeback_tail_zeros.go  writeback zeroes the end's tail    CrashFile (zero at or past sizeLo)
//	data_truncate_tail_zeros.go   ftruncate zeroes the end's page    OsChange.ofResize (pageEnd), pageEnd
//	data_extension_zeros.go       extensions read zeros (F3 refuted) OsFile.resized, OsFile.written
//	data_keep_size.go             FALLOC_FL_KEEP_SIZE: no change     FallocKeep
//	data_short_io.go              short and failed pread/pwrite      PRead, PWriteFinish
//	data_inflight_changes.go      changes in flight (one per file)   OsChange, announce, land, BusyAt, osHole
//	data_resize_stamps.go         resize stamps (bookkeeping only)   OsFile.rzs, OsChangeKind.isResize, announce
//	data_maxbytes.go              no byte at or past s_maxbytes      maxBytes, PWriteFinish, FtruncateFinish,
//	                              (pending review)                   FallocFinish, CrashFile, FsInit, OsWf.sizes
//
// The directory tree and metadata calls:
//
//	meta_inodes_hidden.go         inodes, internal                   Ino, FsState.files, Named, MachineCrash
//	meta_dir_fds.go               directory fds by inode             OsDirFd, DirSync, TreeWf
//	meta_overlapping_calls.go     overlapping metadata calls         CallBegin, LogEntry.start, Follows
//	meta_dir_rename_stuck.go      directory rename vs path walks     Rename (stuck clause), CallBegin, SameRoot
//	meta_rename_cross_root.go     a rename across roots (approved)   SameRoot, Rename
//	meta_file_fsync.go            a file fsync commits no name       Fsync, DirSync
//	meta_wal_create.go            wal.Create's directory swap        DirSync, Follows
//	meta_readdir.go               readdir racing changes             OsDirRead, DirReadNext
//	meta_enoent.go                ENOENT only for a missing path     ENOENT, Open, DirReadNext (pending review)
//	                              or a removed directory
//
// link(2), which the semantics does not model (no Link step): the assumptions
// of the trust-boundary axiom snap.Snapshotter.SaveDBFrom.wp_proof and of
// snapDirInvH (branch etcd-safe-crash-delta-now/2026-11-27; 2026-11-28;
// meta_link_test.go holds the live measurements, notes/axiom-review/fs-link/
// the crash harness; both run on C, notes/axiom-review/fs-link/results.md):
//
//	meta_link_no_replace.go       link never replaces: EEXIST,       SaveDBFrom.wp_proof (the keep), snapDirBody
//	                              atomic with the creation (i)       (fileFreeDur → snapFileAt)
//	meta_link_crash.go            crash before the dir fsync: the    backend.fileAtPend, pendNamed, snapFileAt,
//	                              name absent or the synced file (ii) snapDir_crash_law_holds
//	meta_link_shared_inode.go     crash between link and unlink:     snap.snapDirOwn (tmp* names, no inode)
//	                              tmp and fn, one inode (iii)
//
// File locks (2026-11-15, the user's approval of lock state; pending review,
// notes/wal-units/locks.md; locks_test.go holds their measurements):
//
//	locks_ofd.go                  OFD locks per description          OsFd.ofd, LockConflict, LockStep, OfdLock
//	locks_flock.go                flock locks per description        OsFd.flk, LockStep, flockReq, Flock
//	locks_flock_vs_ofd.go         the two kinds are independent      LockKind, OsFd.lk, LockConflict
//	locks_blocking.go             blocking requests wait (a step     LockStep (nb, self), ErrnoZero "OfdLock",
//	                              to itself, 2026-11-20) or fail     MapLockOk "Flock"
//	locks_spurious_eagain.go      EAGAIN with no conflict in the     LockStep (failure arm), Close's comment;
//	                              model, non-blocking (2026-11-19)   Premises.lean: IoCovers (blocking OFD only),
//	                                                                 MapLockOk "Flock" (2026-11-20)
//	locks_close_crash.go          released at close and at a crash   Close, MachineCrash, FsInit
//	locks_mmap_close.go           a mapping keeps them past close    MapDesc, ProcState.mapDesc, Close,
//	                              until its munmap (2026-11-19)      Mmap, Munmap, LockConflict
//	locks_posix_not_modelled.go   F_SETLK/F_SETLKW: not modelled     syscall.lean, unix.lean: FcntlFlock.impl
//
// Mappings:
//
//	map_mmap_no_room.go           no room in (0, maxAddr]: mmap      MmapRoom, MmapStall, FsStep, FsStepV
//	                              does not return, as an allocation  (Specs.lean: wp_osMmapG)
//	                              (pending review, 2026-11-17)
//	map_madvise.go                madvise (a paging hint): a step,   Madvise (IsFsStep), unix.lean: Madvise.impl
//	                              no change, any errno               (Madvise.lean: wp_osMadvise)
//	                              (pending review, 2026-11-17)
//
// Trusted models of the Go wrappers (drafts of 2026-11-13, pending review;
// models_test.go holds their measurements, run on C by run-models-on-c.sh):
//
//	model_syscall_fallocate.go    syscall.Fallocate as unix's        syscall.lean: Fallocate.impl
//	model_syscall_fcntlflock.go   OFD commands; F_OFD_GETLK on any   syscall.lean: FcntlFlock.impl
//	model_os_close_nil.go         nil *File Close: ErrInvalid        os.lean: File.Close.impl
//	model_os_close_twice.go       closed *File Close: ErrClosed      os.lean: File.Close.impl
//	model_os_stat.go              Stat/Lstat as open+fstat+close     os.lean: model.stat, arbitraryMode
//	model_os_mkdirall.go          MkdirAll: Go's body over models    os.lean: MkdirAll.impl
//	model_os_mkdirall_above.go    MkdirAll at or above a root        Impl.lean: PathKind; os.lean: mkdirAllAbove
//	model_os_stat_above.go        Stat/Lstat above a root, no step   Impl.lean: PathKind, AboveRoot; os.lean: statAbove
//	model_os_open_above.go        Open/Sync/Close above a root       Impl.lean: Open (OpenOutside), OutSync, OutClose
//	model_os_filestat_name.go     fileStat.Name: base of the path    os.lean: fileStat, model.base; os.toml
//	model_os_removeall.go         RemoveAll over paths, rename-free  os.lean: RemoveAll.impl, removeAllFrom
//	model_os_writefile.go         WriteFile; an empty Write          os.lean: File.Write.impl; WriteFile
//	model_os_dir_offset.go        a directory's offset: not modelled models/os/model.go: Readdirnames, Seek
//	model_os_readdirnames_len.go  Readdirnames: under 2^44 names     os.lean: File.Readdirnames.impl (assume)
//	model_os_copy_file_range.go   io.Copy of files: copy_file_range  os.lean: model.copyFileRangeRound,
//	                              as PRead + PWrite (pending review) pollCopyFileRange, File.copyFileRange.impl
//
// Client premises (not part of the semantics; a theorem states them):
//
//	premise_sector_whole.go       WAL sectors come back whole        SectorWhole, valAt (a known limitation)
//	premise_p1.go                 no torn meta validates (minibolt)  P1 (bboltfs/BootP1.lean), valAt
//	premise_no_io_err.go          no I/O error on chosen files       NoIoErr, IoSet, IoCovers, ErrnoZero
//	                              (assumed; user, 2026-11-15)        (NoIoErr.lean: noIoErr_keeps)
//	                              + OFD lock requests, dir reads     IoCovers "OfdLock"/"DirReadNext",
//	                              (assumed, measured as support:     ErrnoZero "DirReadNext" (ENOENT kept)
//	                              premise_no_io_err_test.go; user,
//	                              2026-11-19)
//	                              + errnos of a failing unlink/rmdir PathErrno (ENOENT, EISDIR, ENOTEMPTY;
//	                              (assumed, measured as support:     NoIoErr.lean: noIoErr_good)
//	                              TestNoIoErrPathErrno; user,
//	                              2026-11-19)
//	                              + errno of a failing open of an    PathErrno "Open" (ENOENT, with a free fd;
//	                              absent name, no O_CREAT            NoIoErr.lean: noIoErr_good;
//	                              (assumed, measured as support:     NoMapLockErr.lean:
//	                              TestNoIoErrOpenAbsent; user,       noIoErr_noMapLockErr_keeps)
//	                              2026-11-23, claim #34)
//	                              + C's permissions: search (also    NoIoErr's docstring, Impl.lean's
//	                              of ancestors)/write, file write,   "Environment" (env_config.go)
//	                              no sticky, immutable, append-only,
//	                              protected_symlinks/regular,
//	                              unmapped idmapped ids, LSM,
//	                              seccomp or fanotify denial
//	                              (assumed; contrasts: TestNoIoErrPerm*,
//	                              TestNoIoErrProtected*; user, 2026-11-19)
//	                              - non-blocking lock requests and   IoCovers "OfdLock" (blocking only),
//	                              paths that do not fit (user,       PathFits
//	                              2026-11-19; TestLocksProcReaderEagain,
//	                              TestNoIoErrNameTooLong)
//	                              + C's fd limits: no EMFILE/ENFILE  NoIoErr's docstring, Impl.lean's
//	                              (assumed; contrast:                "Environment" (env_config.go)
//	                              TestNoIoErrEmfile; user, 2026-11-19)
//	                              - flock (NoMapLockErr's: one       IoCovers (no "Flock")
//	                              premise per call; user, 2026-11-20)
//	premise_no_map_lock_err.go    no flock/mmap/munmap/madvise error NoMapLockErr, MapLockCovers, MapLockOk
//	                              on chosen files (mmap: a mapping,  (NoMapLockErr.lean: noMapLockErr_keeps,
//	                              or no return with no room left);   isFsStep_open_eintr)
//	                              open with no free fd does not
//	                              return (EINTR, retried)
//	                              (assumed; pending review)
package semantics
