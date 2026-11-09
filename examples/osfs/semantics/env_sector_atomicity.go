//go:build linux

package semantics

import (
	"os"
)

// Sector atomicity (environment assumption).
//
// Decision: a crash leaves each 512-byte sector of a write entirely old or
// entirely as sent. Sectors are independent: one write's sectors can come back
// in any mix of old and new.
//
// Lean: Impl.lean header ("The device ... writes each 512-byte sector
// atomically"); Sector, SecBytes, CrashFile (each sector `n` gets one whole
// version `vs n`).
//
// Allowed: after the crash below, bytes [0,512) are all A or all B, and so are
// bytes [512,1024), chosen independently (A B, B A, ...).
// Excluded: a sector holding some A bytes and some B bytes.
//
// Why: assumed. It holds for 512n and 4Kn devices that write a logical block
// atomically (a 4096-byte-atomic device's crash states are 512-byte-atomic
// ones). It excludes devices whose write can damage sectors it does not
// write (512e drives without power-loss protection). etcd's WAL relies on it:
// its torn-write check (`isTornEntry`) looks for a 512-byte chunk of zeros.
func SectorAtomicity(dir string) {
	f, _ := os.Create(dir + "/f")
	f.WriteAt(fill(1024, 'A'), 0)
	f.Sync()
	f.WriteAt(fill(1024, 'B'), 0)
	// crash here
	// allowed:  [AAAA|AAAA], [BBBB|BBBB], [AAAA|BBBB], [BBBB|AAAA] (per sector)
	// excluded: [AABB|....] (a sector mixing A and B)
}
