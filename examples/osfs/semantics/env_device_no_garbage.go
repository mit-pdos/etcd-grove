//go:build linux

package semantics

import (
	"os"
)

// The device never returns garbage (environment assumption).
//
// Decision: a write the device was doing when the power went leaves each byte
// with its old or its new value; it never damages bytes it was not writing,
// and never leaves a byte with a third value. Nothing is assumed about which
// bytes of a sector were written (no sector atomicity).
//
// Lean: Impl.lean header ("The device ... never returns garbage"); CrashFile
// (every byte one of its candidates: values the program wrote, or the synced
// one).
//
// Allowed: after the crash below, each byte of [0,512) A or B.
// Excluded: a byte that is neither (an error-correcting code's all-zeros or
// all-ones read of a half-written sector), and a change to [512,1024).
//
// Why: assumed. It is SQLite's documented model of a power loss during a
// sector write ("linear": part of the sector modified, the rest unchanged;
// https://www.sqlite.org/atomiccommit.html), weaker than sector atomicity. The
// configuration's devices honour cache flushes and have no media errors; a
// device that may read back garbage after a power loss (SQLite's "powersafe
// overwrite" absent, https://www.sqlite.org/psow.html) is outside it.
func DeviceNoGarbage(dir string) {
	f, _ := os.Create(dir + "/f")
	f.WriteAt(append(fill(512, 'A'), fill(512, 'X')...), 0)
	f.Sync()
	f.WriteAt(fill(512, 'B'), 0)
	// crash here
	// allowed:  each byte of [0,512) A or B; [512,1024) X
	// excluded: any other value
}
