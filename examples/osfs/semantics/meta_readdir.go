//go:build linux

package semantics

import (
	"os"
	"sync"
)

// Readdir racing changes to the directory (model decision).
//
// Decision: a read of a directory's names returns, one at a time, names the
// directory had at some point since the read began, each at most once since
// it was last touched; it ends only once it has returned every name the
// directory had when the read began, still has, and that no operation touched
// since. A name added or removed meanwhile may or may not be returned.
//
// Lean: Impl.lean: OsDirRead, OsDirFd.note, OsDirRead.cur, the DirReadNext
// step.
//
// Allowed: the listing below includes or omits b; always includes a.
// Excluded: a missing; a name the directory never had.
//
// Why: documented (POSIX readdir: "If a file is removed from or added to the
// directory after the most recent call to opendir() or rewinddir(), whether a
// subsequent call to readdir() returns an entry for that file is
// unspecified"). etcd lists the WAL directory (fileutil.ReadDir) at open and
// purge.
func ReaddirRace(dir string) {
	os.Mkdir(dir+"/d", 0o755)
	a, _ := os.Create(dir + "/d/a")
	a.Close()
	d, _ := os.Open(dir + "/d")
	var wg sync.WaitGroup
	wg.Add(1)
	go func() { b, _ := os.Create(dir + "/d/b"); b.Close(); wg.Done() }()
	names, _ := d.Readdirnames(-1)
	// allowed: [a], [a b], [b a]
	_ = names
	wg.Wait()
	d.Close()
}
