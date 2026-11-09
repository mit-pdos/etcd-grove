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
// Lean: FsInit (every file `OsFile.ofDisk`: one version per sector, clean;
// `metaLog = []`).
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
