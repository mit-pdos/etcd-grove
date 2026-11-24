//go:build linux

package semantics

import (
	"os"
)

// Durable at first start (environment assumption, audit F2).
//
// Decision: when the program first starts, the roots' trees and every file in
// them are durable: nothing has changed them since their last successful
// sync, syncfs or fsync.
//
// Lean: FsInit (every file `OsFile.ofDisk`: one candidate per byte;
// `metaLog = []`), the semantics' initial local state (fs_semantics's
// initLocal, since 2026-11-22, and fsSemWithS's, the semantics restricted by a
// client's premises, since 2026-11-24, etcd-dist D4a: a theorem's premise
// through Robust's extsInitLocal; before, only the ghost state's initP assumed
// it, and a theorem over fsSemWithS stated FsInit itself).
//
// Excluded (under the assumption): the scenario below, where a crash after
// the first start loses a file the program saw at start.
//
// Why: assumed; a deployment property. Without it the first start would need
// the same "maybe not durable" state a crash leaves, and every program would
// have to sync what it found before trusting it. The installer (or the
// operator) is assumed to have synced.
func DurableAtFirstStart(dir string) {
	// Before the program starts: someone ran `echo x > dir/f` with no sync.
	f, err := os.Open(dir + "/f")
	if err == nil {
		// the program saw dir/f ...
		f.Close()
	}
	// crash here
	// Linux: dir/f may be gone or empty after the crash
	// model: FsInit made dir/f durable, so it is still there
}
