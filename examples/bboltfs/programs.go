package bboltfs

import (
	"sync"
	"sync/atomic"
)

// The programs to verify over minibolt, besides its boot program
// (BootMinibolt): each returns true in every run, {{ True }} f(dir) {{ RET true }},
// and its assertions (minibolt's panics) never fire.
//
// The model lets any operation fail with an arbitrary errno and no effect (an
// environmental failure). A program's claim is about the runs where nothing
// fails: on a failure it stops and returns true, through envFailure.

// envErrors counts the environmental failures the programs met. The model
// does not read it; the Go tests check that real Linux never fails here.
var envErrors uint64

func envFailure() bool {
	atomic.AddUint64(&envErrors, 1)
	return true
}

// commits is how many transactions the programs commit: 40 pages from 4 is
// past the 32 KiB first mapping, so the writer remaps (32 -> 64 KiB) and grows
// the file (Truncate and Sync).
const commits = 40

// valueOk is what a transaction may see: init's transactions hold no value,
// and transaction t >= 2 holds t.
func valueOk(txid, v uint64, has bool) bool {
	if txid <= 1 {
		return !has
	}
	return has && v == txid
}

// testMinibolt: a fresh database, commits that remap and grow, each visible to
// Get and Snapshot, then Close and Open (which reads the page size with ReadAt)
// and the last commit still there.
func testMinibolt(dir string) bool {
	db, err := Open(dir + "/db")
	if err != nil {
		return envFailure()
	}
	txid, _, has, err := db.Get()
	if err != nil {
		db.Close()
		return envFailure()
	}
	ok := txid == 1 && !has
	for v := uint64(2); v <= commits; v++ {
		if err := db.Commit(v); err != nil {
			db.Close()
			return envFailure()
		}
		txid, got, has, err := db.Get()
		if err != nil {
			db.Close()
			return envFailure()
		}
		stxid, sgot, shas, err := db.Snapshot()
		if err != nil {
			db.Close()
			return envFailure()
		}
		ok = ok && txid == v && has && got == v && stxid == v && shas && sgot == v
	}
	db.Close()
	db, err = Open(dir + "/db")
	if err != nil {
		return envFailure()
	}
	txid, got, has, err := db.Get()
	db.Close()
	if err != nil {
		return envFailure()
	}
	return ok && txid == commits && has && got == commits
}

// testMiniboltConcurrent: two readers, one calling Get and one Snapshot, while
// the writer commits. Each reader sees a committed value, and never an older
// transaction than one it saw before. The mapped loads are disjoint from the
// writer's in-flight changes (the new page past the high water mark, and the
// meta under metalock); the Snapshot's ReadAt races them, and only the pages of
// its own transaction are claimed.
func testMiniboltConcurrent(dir string) bool {
	db, err := Open(dir + "/db")
	if err != nil {
		return envFailure()
	}
	var wg sync.WaitGroup
	results := make([]bool, 2)
	for r := 0; r < 2; r++ {
		wg.Add(1)
		go func(r int) {
			defer wg.Done()
			ok := true
			var last uint64
			for i := 0; i < 20; i++ {
				var txid, v uint64
				var has bool
				var err error
				if r == 0 {
					txid, v, has, err = db.Get()
				} else {
					txid, v, has, err = db.Snapshot()
				}
				if err != nil {
					results[r] = envFailure()
					return
				}
				ok = ok && valueOk(txid, v, has) && last <= txid
				last = txid
			}
			results[r] = ok
		}(r)
	}
	writerOk := true
	for v := uint64(2); v <= commits; v++ {
		if err := db.Commit(v); err != nil {
			writerOk = envFailure()
			break
		}
	}
	wg.Wait()
	db.Close()
	return writerOk && results[0] && results[1]
}
