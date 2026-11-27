package mvccfull

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

// MainAt is the tester with its files in the directory r and a Config drawn at random (drawConfig):
// it runs only if r fits (dirFits), the Config is in the range the proof covers (inScope), and none
// of the files the run may create is there yet; otherwise it returns without doing anything.
func MainAt(r string) {
	if !dirFits(r) {
		return
	}
	cfg := drawConfig(r + "/mvccfull")
	if !inScope(cfg) {
		return
	}
	for _, p := range FilePaths(cfg) {
		if !absent(p) {
			return
		}
	}
	Run(cfg)
}
