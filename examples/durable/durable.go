// Package durable is a node's durable state: named files, each read and written whole. It is
// the Go side of the GooseLang extension durableExt (GooseLang/Ext/Durable/Impl.lean): its
// functions are trusted, modeled by the extension's operations
// (TrustedCode/github_com/mit_pdos/etcd_grove/examples/durable.lean) instead of translated.
//
// The model makes each operation one atomic step that cannot fail, and a written file durable
// (a crash keeps every file as the last Write left it). The implementation provides that with
// the operating system's file API alone:
//   - mu serializes the operations, so that no Read sees a Write's contents before they are
//     durable;
//   - a Write goes to a fresh temporary file in the same directory, which is synced, renamed
//     over the file, and the directory synced: a crash leaves the file either as it was or as
//     written, never partly written;
//   - an operation that fails (an I/O error) is retried forever instead of reported, so the
//     program never sees a failure (it may not return, which the model, a safety model,
//     allows). A Read of a file that does not exist is not a failure: it returns ok false.
//
// A file's directory must exist: the package never creates one.
package durable

import (
	"errors"
	"io/fs"
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
		b, err := os.ReadFile(name)
		if err == nil {
			return string(b), true
		}
		if errors.Is(err, fs.ErrNotExist) {
			return "", false
		}
	}
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
	f, err := os.CreateTemp(dir, ".durable-*")
	if err != nil {
		return false
	}
	tmp := f.Name()
	_, err = f.WriteString(data)
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
		os.Remove(tmp)
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
