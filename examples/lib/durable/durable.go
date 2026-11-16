// Package durable is a node's durable state: named files, each read and written whole.
//
// It has two Lean sides. In the main tree it is the Go side of the GooseLang extension durableExt
// (GooseLang/Ext/Durable/Impl.lean): its functions are trusted, modeled by the extension's
// operations (TrustedCode/github_com/mit_pdos/etcd_grove/examples/lib/durable.lean) instead of
// translated. In the part LinuxFs/ it is translated with its bodies, over the part's os (the Linux
// file extension fsExt), and its specs are proved (LinuxFs/Proof/github_com/mit_pdos/etcd_grove/
// examples/lib/durable/).
//
// The model makes each operation one atomic step that cannot fail, and a written file durable
// (a crash keeps every file as the last Write left it). The implementation provides that with
// the operating system's file API alone:
//   - mu serializes the operations, so that no Read sees a Write's contents before they are
//     durable;
//   - a Write goes to a temporary file in the same directory (the file's name with ".durable-" in
//     front, truncated first), which is written, synced, renamed over the file, and the directory
//     synced: a crash leaves the file either as it was or as written, never partly written;
//   - an operation that fails (an I/O error) is retried forever instead of reported, so the
//     program never sees a failure (it may not return, which the model, a safety model,
//     allows). A Read of a file that does not exist is not a failure: it returns ok false.
//
// A file's directory must exist: the package never creates one. A name must not be that of
// another file's temporary (its last element must not start with ".durable-"), and a file must
// hold at most 1 GiB.
package durable

import (
	"errors"
	"os"
	"path/filepath"
	"sync"
)

var mu sync.Mutex

// Read returns the entire contents of the file name and true, or "" and false if there is no
// such file.
func Read(name string) (string, bool) {
	mu.Lock()
	defer mu.Unlock()
	for {
		s, ok, done := tryRead(name)
		if done {
			return s, ok
		}
	}
}

// tryRead makes one attempt at Read: done is false if it failed.
func tryRead(name string) (s string, ok bool, done bool) {
	f, err := os.Open(name)
	if err != nil {
		return "", false, errors.Is(err, os.ErrNotExist)
	}
	defer f.Close()
	fi, err := f.Stat()
	if err != nil {
		return "", false, false
	}
	b := make([]byte, fi.Size())
	if _, err := f.ReadAt(b, 0); err != nil {
		return "", false, false
	}
	return string(b), true, true
}

// Write replaces the entire contents of the file name by data, creating it if needed,
// atomically and durably.
func Write(name string, data string) {
	mu.Lock()
	defer mu.Unlock()
	for !tryWrite(name, data) {
	}
}

// tryWrite makes one attempt at Write. It changes nothing a Read can see unless the rename
// succeeds, and then the file holds data; it returns true once that is durable.
func tryWrite(name string, data string) bool {
	dir := filepath.Dir(name)
	tmp := filepath.Join(dir, ".durable-"+filepath.Base(name))
	f, err := os.OpenFile(tmp, os.O_RDWR|os.O_CREATE|os.O_TRUNC, 0o600)
	if err != nil {
		return false
	}
	if len(data) > 0 {
		_, err = f.WriteAt([]byte(data), 0)
	}
	if err == nil {
		err = f.Sync()
	}
	if err2 := f.Close(); err == nil {
		err = err2
	}
	if err == nil {
		err = os.Rename(tmp, name)
	}
	if err != nil {
		return false
	}
	d, err := os.Open(dir)
	if err != nil {
		return false
	}
	err = d.Sync()
	d.Close()
	return err == nil
}
