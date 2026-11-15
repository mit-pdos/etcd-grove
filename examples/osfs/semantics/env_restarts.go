//go:build linux

package semantics

import (
	"os"
)

// Restarts are machine crashes (environment assumption).
//
// Decision: the program restarts only after a machine restart, or after the
// previous process has exited and a sync(2) made what it left durable (a
// supervisor runs `sync` first, e.g. systemd's ExecStartPre=/bin/sync). The
// model has machine crashes only.
//
// Lean: Impl.lean header ("Restarts"); OsCrash := MachineCrash;
// notes/fs-semantics-v2.md, "Restarts are machine crashes";
// notes/restart-vs-crash.md.
//
// Excluded (under the assumption): generation 2 below reading dirty data of
// generation 1 from the page cache, acting on it as durable, and a later
// power loss removing it.
//
// Why: a process restart without the sync keeps the page cache: the next
// process reads what is not on disk. notes/restart-vs-crash.md found that etcd
// does act on such data (a follower acks entries read from the page cache
// without syncing; the purge loop trusts an unsynced snapshot record; bbolt
// reuses pages freed by an unsynced commit): nonissues/etcd-wal-restart-*,
// nonissues/bbolt-restart-*.
func RestartWithoutSync(dir string) {
	// generation 1
	f, _ := os.Create(dir + "/log")
	f.WriteAt([]byte("entry 5"), 0) // never synced
	// the process is killed here; no machine crash, no sync

	// generation 2 (same machine, page cache intact)
	g, _ := os.Open(dir + "/log")
	buf := make([]byte, 7)
	g.ReadAt(buf, 0) // reads "entry 5" from the page cache
	// ... acks entry 5 to a peer, without syncing (it "already has" it) ...
	// power loss here: entry 5 is gone, though it was acked
	// With `sync` before generation 2 starts, entry 5 is durable when acked.
}
