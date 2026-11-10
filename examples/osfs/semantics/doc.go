// Package semantics explains, by small Go programs, each decision of the Linux
// file extension's trusted semantics (GooseLang/Ext/Fs/{Impl,Tree,Paths}.lean,
// with the trusted models TrustedCode/{os,syscall}.lean and
// TrustedCode/golang_org/x/sys/unix.lean) and of the trace-level NoTear
// assumption (GooseLang/Ext/Fs/NoTear.lean).
//
// Each file is one decision: its doc comment says what the model does, the
// Lean names that encode it, the outcome it allows or excludes, and why
// (measured, documented with a citation, or assumed), and which client needs
// it; then a function shows the scenario, with "crash here" and the outcomes.
// The functions are illustrations: nothing calls them, and no Goose
// translation or proof covers this package. Every claim is about the target
// configuration C (env_config.go); the measurements cited were made on C with
// the scripts in notes/axiom-review/fs-config/ (and fs-v2-f3/, fs-v2-r4/).
//
// The rule (CLAUDE.md): every change to the trusted semantics adds or updates
// the file of the decision it changes, in the same commit.
//
// Environment assumptions (hypotheses of the adequacy statement):
//
//	env_config.go                 the target configuration C         Impl.lean header, pageIn
//	env_sector_atomicity.go       512-byte sector atomicity          Sector, SecBytes, CrashFile
//	env_no_mixed_writeback.go     no mixed writeback                 Sector.vers (whole versions)
//	env_no_failed_writeback.go    no failed writeback (F1)           OsFile.syncFailed, ReadSees
//	env_durable_at_first_start.go durable at first start (F2)        FsInit
//	env_restarts.go               restarts are machine crashes       OsCrash := MachineCrash
//	env_journal_order.go          metadata in journal order          Follows, Closed, MachineCrash, DirSync
//	env_roots_only.go             only the roots' trees              TreeName, TreePath, CanonBelow, RootsOk
//
// File contents and sizes:
//
//	data_sector_versions.go       versions since the last sync       Sector, OsFile.change, OsFile.synced, SecCand
//	data_failed_fsync.go          failed fsync: lost sectors         Sector.dirty, OsFile.syncFailed, Fsync
//	data_sizes_since_sync.go      any size in [sizeLo, sizeHi]       OsFile.sizeLo/sizeHi, CrashFile
//	data_resize_chunks.go         partial resize (F5)                Landed.trunc, FallocFinish
//	data_durable_zeros.go         pages past a durable size: zeros   diskSec, OsFile.ofDisk, OsFile.synced
//	data_append_old_block.go      the end's block is not ordered     diskSec (the end's page), CrashFile
//	data_extension_zeros.go       extensions read zeros (F3 refuted) OsFile.resized, OsFile.written
//	data_keep_size.go             FALLOC_FL_KEEP_SIZE: no change     FallocKeep
//	data_short_io.go              short and failed pread/pwrite      PRead, PWriteFinish
//	data_inflight_changes.go      changes in flight, mappings        OsChange, inflight, Landed, osHole
//
// The directory tree and metadata calls:
//
//	meta_inodes_hidden.go         inodes, internal                   Ino, FsState.files, Named, MachineCrash
//	meta_dir_fds.go               directory fds by inode             OsDirFd, DirSync, TreeWf
//	meta_overlapping_calls.go     overlapping metadata calls         CallBegin, LogEntry.start, Follows
//	meta_dir_rename_stuck.go      directory rename vs path walks     Rename (stuck clause), CallBegin
//	meta_file_fsync.go            a file fsync commits no name       Fsync, DirSync
//	meta_wal_create.go            wal.Create's directory swap        DirSync, Follows
//	meta_readdir.go               readdir racing changes             OsDirRead, DirReadNext
//
// Trace-level assumption (not part of the semantics):
//
//	notear.go                     a partial pwrite stops at a page   PageCut, NoTearStep, NoTearCrash
package semantics
