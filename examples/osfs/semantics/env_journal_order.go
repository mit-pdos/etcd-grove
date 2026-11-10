//go:build linux

package semantics

import (
	"os"
)

// Metadata operations reach disk in journal order (environment assumption).
//
// Decision: create, mkdir, unlink, rmdir and rename are logged (metaLog); a
// crash keeps a set of them closed under the journal's order and replays it.
// An operation must be kept with every operation that took effect before its
// call began; nothing else orders them. A successful directory fsync makes
// every logged operation durable.
//
// Lean: Tree.lean: MetaOp, LogEntry, Follows, Closed, keptOps; Impl.lean:
// MachineCrash (the kept set S), DirSync (commitAll); the header's journal
// sentence; Tests.lean: dirsync_new_dir.
//
// Allowed: after the crash below, {} or {a} or {a, b}.
// Excluded: {b} without {a}: b's create began after a's returned, so the
// journal has a before b.
//
// Why: on configuration C, ext4's jbd2 commits whole transactions in order,
// and a metadata syscall joins a transaction no earlier than those of the
// calls that returned before it began (measured on C:
// notes/axiom-review/fs-v2-r5.md, B1, 163 crash images of the clients' exact
// sequences, dm-log-writes). An fsync of a directory commits the whole
// journal (ext4_force_commit for a file that is not regular, fs/ext4/fsync.c).
// Linux also orders calls that lock a common directory, or two renames across
// directories; the model does not, which only allows more crashes. This is
// stronger than POSIX (where only an fsync of each directory makes its entries
// durable), and etcd's WAL relies on it: see meta_wal_create.go.
func JournalOrder(dir string) {
	os.Mkdir(dir+"/x", 0o755)
	os.Mkdir(dir+"/y", 0o755)
	a, _ := os.Create(dir + "/x/a")
	a.Close()
	b, _ := os.Create(dir + "/y/b") // began after a's create returned
	b.Close()
	// crash here
	// allowed:  neither, x/a only, both
	// excluded: y/b without x/a
}
