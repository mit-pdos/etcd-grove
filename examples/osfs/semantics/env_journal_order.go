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
// call began, every earlier one that locks a common directory, and (for a
// rename across directories) every earlier such rename. A directory fsync
// makes the directory's last logged change durable with everything it
// follows.
//
// Lean: Tree.lean: MetaOp, LogEntry, Follows, Closed, Needed, keptOps,
// lastTouch; Impl.lean: MachineCrash (the kept set S), DirSync
// (commitThrough of lastTouch); the header's journal paragraph.
//
// Allowed: after the crash below, {} or {a} or {a, b}.
// Excluded: {b} without {a}: b's create began after a's returned, so the
// journal has a before b.
//
// Why: ext4's jbd2 and xfs's log commit whole transactions in order, and a
// metadata syscall joins a transaction no earlier than those of the calls that
// returned before it began (assumed from the jbd2/xfs CIL design; the audit's
// "Attacks the model survived"). This is stronger than POSIX (where only an
// fsync of each directory makes its entries durable), and etcd's WAL relies
// on it: see meta_wal_create.go.
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
