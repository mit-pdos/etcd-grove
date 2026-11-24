package node

import (
	"testing"
)

// backfillLatest fills n.latest with the newest committed version of each key
// ("latest: Latest version of a given key"): the store may hold several
// committed versions of a key, in any order (it took the last one).
func TestBackfillNewest(t *testing.T) {
	_, c, ns := newNet("a")
	n := ns[0]
	n.store.Write("k", []byte("two"), 2)
	n.store.Commit("k", 2)
	n.store.Write("k", []byte("one"), 1)
	n.store.Commit("k", 1)
	start(t, c, n)
	if _, v, err := n.LatestVersion("k"); err != nil || v != 2 {
		t.Errorf("LatestVersion(k) = %d, %v after backfill; want 2", v, err)
	}
}

