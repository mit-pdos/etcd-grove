// Package walarea prepares the members' WAL areas for the examples' Go tests. It is not translated
// (no Goose project lists it): only tests import it.
//
// Since wal-link P2 every member started through examples/lib/etcdstart keeps its WAL in the
// dedicated WAL directory etcdstart.WALBase + "/" + name + ".etcd" + "/wal", an absolute path, alone
// in the member's area etcdstart.WALBase + "/" + name + ".etcd". The closed theorems assume each
// member's area exists and holds no WAL when the program starts (their premise etcdWalAreasInit).
// Since 2026-11-19 the data directory is absolute too, etcdstart.DataBase + "/" + name + ".etcd", a
// root that exists, empty, at start (the same premise). A test that starts members afresh resets
// their areas and data directories first, so that no WAL or backend an earlier run left is found
// (etcd would then restart the member from it) and both are as the premise says. They are left when
// the test ends: a member a test leaves running still writes there.
package walarea

import (
	"os"
	"path/filepath"
	"testing"

	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
)

// Area is the WAL area of the member named name.
func Area(name string) string {
	return filepath.Join(etcdstart.WALBase, name+".etcd")
}

// DataDir is the data directory of the member named name.
func DataDir(name string) string {
	return filepath.Join(etcdstart.DataBase, name+".etcd")
}

// Reset removes the WAL area and the data directory of each member of names and creates each
// empty.
func Reset(t testing.TB, names ...string) {
	t.Helper()
	for _, n := range names {
		for _, a := range []string{Area(n), DataDir(n)} {
			if err := os.RemoveAll(a); err != nil {
				t.Fatal(err)
			}
			if err := os.MkdirAll(a, 0o700); err != nil {
				t.Fatal(err)
			}
		}
	}
}

// ResetMembers is Reset for the members ms.
func ResetMembers(t testing.TB, ms []etcdstart.Member) {
	t.Helper()
	for _, m := range ms {
		Reset(t, m.Name)
	}
}

// ResetFamily removes the WAL areas and the data directories of every member named pfx + "-" +
// anything, for each pfx of pfxs (etcdstart.Members' names, when the test does not know how many it
// starts): they are then absent, and wal.Create and bootstrap make each (TouchDirAll).
func ResetFamily(t testing.TB, pfxs ...string) {
	t.Helper()
	for _, pfx := range pfxs {
		for _, base := range []string{etcdstart.WALBase, etcdstart.DataBase} {
			ms, err := filepath.Glob(filepath.Join(base, pfx+"-*.etcd"))
			if err != nil {
				t.Fatal(err)
			}
			for _, a := range ms {
				if err := os.RemoveAll(a); err != nil {
					t.Fatal(err)
				}
			}
		}
	}
}
