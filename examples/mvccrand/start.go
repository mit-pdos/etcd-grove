package mvccrand

import (
	"errors"
	"os"
)

// dirFits reports whether the directory r leaves room below it: it is shorter than 3800 bytes and
// every 256 consecutive bytes of it hold a '/' (no component is longer than 255 bytes).
func dirFits(r string) bool {
	if len(r) >= 3800 {
		return false
	}
	run := 0 // the bytes since the last '/'
	for i := 0; i < len(r); i++ {
		if r[i] == '/' {
			run = 0
		} else {
			run++
			if run >= 256 {
				return false
			}
		}
	}
	return true
}

// absent reports whether nothing is at the path p.
func absent(p string) bool {
	_, err := os.Lstat(p)
	return err != nil && errors.Is(err, os.ErrNotExist)
}

// MainAt is Main with its files in the directory r. It runs only if r fits (dirFits) and none of the
// files the run may create is there yet; otherwise it returns without doing anything.
func MainAt(r string) {
	if !dirFits(r) {
		return
	}
	p := r + "/mvccrand.db"
	if !absent(p) {
		return
	}
	Run(Config{Path: p, Seed: 1, Ops: 1000, Readers: 4, Reads: 200, Watchers: 8})
}
