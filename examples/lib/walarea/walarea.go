// Package walarea prepares the members' WAL areas for the examples' Go tests. It is not translated
// (no Goose project lists it): only tests import it.
//
// Since wal-link P2 every member started through examples/lib/etcdstart keeps its WAL in the
// dedicated WAL directory etcdstart.WALBase + "/" + name + ".etcd" + "/wal", an absolute path, alone
// in the member's area etcdstart.WALBase + "/" + name + ".etcd". The closed theorems assume each
// member's area exists and holds no WAL when the program starts (their premise etcdWalAreasInit);
// the data directory stays relative (the tests run in a fresh t.TempDir()). A test that starts
// members afresh resets their areas first, so that no WAL an earlier run left is found (etcd would
// then restart the member from it) and the areas are as the premise says. The areas are left when
// the test ends: a member a test leaves running still writes its WAL there.
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

// Reset removes the WAL area of each member of names and creates it empty.
func Reset(t testing.TB, names ...string) {
	t.Helper()
	for _, n := range names {
		a := Area(n)
		if err := os.RemoveAll(a); err != nil {
			t.Fatal(err)
		}
		if err := os.MkdirAll(a, 0o700); err != nil {
			t.Fatal(err)
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

// ResetFamily removes the WAL areas of every member named pfx + "-" + anything, for each pfx of
// pfxs (etcdstart.Members' names, when the test does not know how many it starts): their areas are
// then absent, and wal.Create makes each (TouchDirAll of the WAL directory's parent).
func ResetFamily(t testing.TB, pfxs ...string) {
	t.Helper()
	for _, pfx := range pfxs {
		ms, err := filepath.Glob(filepath.Join(etcdstart.WALBase, pfx+"-*.etcd"))
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
