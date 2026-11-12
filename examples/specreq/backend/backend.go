// Package backend holds the requirement snippets of etcd's storage backend
// (go.etcd.io/etcd/server/v3/storage/backend): what its users (mvcc, the lessor, auth, membership,
// alarms, the consistent index and the server's hooks, the server's snapshot, defragmentation and
// shutdown) rely on.
//
// Each snippet is a closed program, an adequacy target: it opens a backend on a new file of its
// own (a relative path in the current directory), uses the API as the callers do, and panics where
// what a caller relies on fails. Its requirement is that it does not panic. ReqBackend is the
// server-shaped tester of the whole API; ReqForceCommitDurable, a crash target, is separate.
//
// Every snippet assumes: no file at its paths when it first starts, and no other process touches
// them; the environment variable ETCD_VERIFY is unset (set, the backend panics on callers it does
// not expect, such as LockInsideApply outside the server's apply). A failure of the file system the
// snippet itself calls ends the snippet without a panic: it is not the backend's.
package backend

import (
	"errors"
	"os"
	"sync"
	"sync/atomic"
	"time"

	"go.uber.org/zap"

	"go.etcd.io/etcd/server/v3/storage/backend"
	"go.etcd.io/etcd/server/v3/storage/schema"
)

const (
	rounds    = 40 // the writer's sessions, 1..rounds
	compactTo = 10 // the compactor deletes the pairs of rounds 1..compactTo
	snapAt    = 25 // the round after which the writer takes a snapshot
)

// pair is the j-th key of round i in Key: the keys increase with the rounds, as mvcc's revisions.
func pair(i byte, j byte) []byte { return []byte{i, j} }

func one(i byte) []byte { return []byte{i} }

// open opens a backend over the file at path, configured as the server does (non-blocking
// defragmentation is the server's default, features.NonBlockingDefrag) but committing on its own
// often (a 1ms interval, and at an Unlock once 3 writes are pending), and creates the buckets, as
// boot does (schema.CreateMetaBucket, ...; also on an existing file).
func open(path string, hooks backend.Hooks) backend.Backend {
	cfg := backend.DefaultBackendConfig(zap.NewNop())
	cfg.Path, cfg.Hooks = path, hooks
	cfg.BatchInterval, cfg.BatchLimit, cfg.NonBlockingDefrag = time.Millisecond, 3, true
	be := backend.New(cfg)
	tx := be.BatchTx()
	tx.LockOutsideApply()
	for _, b := range []backend.Bucket{schema.Key, schema.Meta, schema.Lease, schema.Alarm, schema.AuthRoles} {
		tx.UnsafeCreateBucket(b)
	}
	tx.Unlock()
	return be
}

// get reads k with a single-key read (a nil end) on rt, read-locked: nil if absent. A
// ConcurrentReadTx ends at its RUnlock, so get reads one key of it at most.
func get(rt backend.ReadTx, b backend.Bucket, k []byte) []byte {
	rt.RLock()
	defer rt.RUnlock()
	_, vs := rt.UnsafeRange(b, k, nil, 0)
	if len(vs) > 1 {
		panic("a single-key read returned several entries")
	}
	if len(vs) == 0 {
		return nil
	}
	return append([]byte(nil), vs[0]...)
}

// visit visits b on r, checking each key is visited once; it returns the keys visited, by round.
func visit(r backend.UnsafeReader, b backend.Bucket) map[byte]int {
	seen, n := map[string]bool{}, map[byte]int{}
	if err := r.UnsafeForEach(b, func(k, v []byte) error {
		if seen[string(k)] {
			panic("backend: a visit saw a key twice")
		}
		seen[string(k)] = true
		n[k[0]]++
		return nil
	}); err != nil {
		panic("backend: a visit failed")
	}
	return n
}

// REQ backend/backend: the backend as the server uses it, everything at once, over a backend that
// commits on its own: a write session (the apply loop's) is atomic and its writes are read, after
// its Unlock, by every read transaction begun after it, and by itself before; a read returns a
// key's last write; a delete is visible after the Unlock; a callee writes into its caller's
// session; the post-lock hook runs under every LockInsideApply and reads the shared ReadTx; the
// pre-commit hook's writes are in every commit; the compactor's batches (a limited range, its
// keys deleted) under the safe-range lock, beside a defragmentation, delete exactly what they
// ranged (nothing is copied back); a whole-bucket visit sees each key once, on the batch in key
// order, and stops at the visitor's error; a range of a safe-range bucket is in key order, and
// limited, just after a commit, its first entries; a snapshot taken after a commit streams, while
// the writes go on, a database file of that commit's image; Defrag and Hash may run at any time;
// after Close the shared ReadTx may be read-locked with nothing read and the sizes read; Close
// commits, and a reopened backend reads it all.
// Users: storage/mvcc/kvstore_txn.go:174-259 (the write transaction: LockInsideApply, UnsafeSeqPut,
// Range on the batch, Unlock), :55-60, :126 (Read: a ConcurrentReadTx, single-key ranges),
// storage/schema/cindex.go:39, :55, :89, storage/hooks.go:45-54 (the consistent index, saved at
// each apply and by the pre-commit hook), etcdserver/server.go:409, :1098, :2478-2484 (the post-lock
// hook), lease/lessor.go:343, :359-361 (the lease deleted inside mvcc's transaction),
// storage/schema/alarm.go:52-93, auth_users.go:49-94, auth_roles.go:40-44, :91 (Lock, a whole
// bucket's range on the batch), storage/mvcc/kvstore_compaction.go:28-95 (scheduleCompaction),
// storage/mvcc/hash.go:33 (HashKV: a visit of Key on a ConcurrentReadTx),
// storage/mvcc/kvstore.go:125-129, :160-161, :289, :327-358 (ForceCommit; Hash; restore's limited
// ranges of Key), etcdserver/snapshot_merge.go:36-74, api/snap/db.go:40-76, storage/backend.go:63-71
// (the merged snapshot streamed to a file, opened as a backend), etcdserver/server.go:976 (the
// Defragment RPC, concurrent with the apply loop), :957-961, api/v3compactor/revision.go:81,
// storage/mvcc/kvstore.go:521-527 (after Close: Rev's RLock and RUnlock, the metrics' sizes),
// etcdserver/bootstrap.go:259-266 (the boot's reopen).
func ReqBackend() {
	var ci atomic.Uint64 // the writer's last round: the server's consistent index
	be := open("specreq-backend.db", backend.NewHooks(func(tx backend.UnsafeReadWriter) {
		if i := ci.Load(); i > 0 {
			tx.UnsafePut(schema.Meta, []byte("hook"), one(byte(i)))
		}
	}))
	var wg sync.WaitGroup
	var done atomic.Uint64 // the writer's last unlocked round
	compact, snapped := make(chan struct{}), make(chan bool, 1)

	// The writer: the apply loop.
	wg.Add(1)
	go func() {
		defer wg.Done()
		tx := be.BatchTx()
		be.SetTxPostLockInsideApplyHook(func() {
			if d := byte(done.Load()); d > 0 { // the writer's thread: d is the last session's round
				_, vs := be.ReadTx().UnsafeRange(schema.Meta, []byte("ci"), nil, 0)
				if len(vs) != 1 || vs[0][0] != d {
					panic("backend: the post-lock hook misread the last session's write")
				}
			}
		})
		for i := byte(1); i <= rounds; i++ {
			tx.LockInsideApply()
			ci.Store(uint64(i))
			tx.UnsafeSeqPut(schema.Key, pair(i, 0), one(i))
			tx.UnsafeSeqPut(schema.Key, pair(i, 1), one(i))
			tx.UnsafePut(schema.Meta, []byte("ci"), one(0))
			tx.UnsafePut(schema.Meta, []byte("ci"), one(i))
			tx.UnsafeDelete(schema.Alarm, one(i-1))
			tx.UnsafePut(schema.Alarm, one(i), one(i))
			be.BatchTx().UnsafePut(schema.Lease, one(i), one(i)) // the lessor, in mvcc's session
			if _, vs := tx.UnsafeRange(schema.Key, pair(i, 1), nil, 0); len(vs) != 1 || vs[0][0] != i {
				panic("backend: a session misread its own write")
			}
			tx.Unlock()
			done.Store(uint64(i))
			if get(be.ReadTx(), schema.Meta, []byte("ci"))[0] != i || get(be.ReadTx(), schema.Alarm, one(i-1)) != nil {
				panic("backend: the last write or a delete is not read after the Unlock")
			}
			if i == compactTo {
				close(compact)
			}
			if i == snapAt { // the merged snapshot, streamed while the writes go on
				be.ForceCommit()
				snap := be.Snapshot()
				wg.Add(1)
				go func() {
					defer wg.Done()
					f, err := os.Create("specreq-backend-snap.db")
					if err != nil {
						snap.Close()
						snapped <- false
						return
					}
					size := snap.Size()
					n, err := snap.WriteTo(f)
					if cerr := snap.Close(); err == nil && (n != size || cerr != nil) {
						panic("backend: the snapshot did not stream its Size bytes, or its Close failed")
					}
					ok := err == nil && f.Sync() == nil && f.Close() == nil
					d, err := os.Open(".")
					snapped <- ok && err == nil && d.Sync() == nil && d.Close() == nil
				}()
			}
		}
	}()

	// Readers: mvcc's reads and HashKV's visit, on ConcurrentReadTxs.
	for r := 0; r < 2; r++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			<-compact // the writer is past the compacted rounds
			for n := 0; n < 20; n++ {
				m := byte(done.Load())
				if get(be.ConcurrentReadTx(), schema.Key, pair(m, 1)) == nil {
					panic("backend: a read begun after a session's Unlock missed its write")
				}
				rt := be.ConcurrentReadTx()
				rt.RLock()
				seen := visit(rt, schema.Key)
				rt.RUnlock()
				for i := byte(compactTo + 1); i <= rounds; i++ {
					if seen[i] != 0 && seen[i] != 2 || i <= m && seen[i] != 2 {
						panic("backend: a read saw part of a session, or missed an unlocked one")
					}
				}
			}
		}()
	}

	// The compactor: mvcc's scheduled compaction, in batches of one pair.
	wg.Add(1)
	go func() {
		defer wg.Done()
		<-compact
		tx := be.BatchTx()
		be.LockForSafeRangeDelete()
		for {
			tx.LockOutsideApply()
			ks, _ := tx.UnsafeRange(schema.Key, pair(1, 0), pair(compactTo+1, 0), 2)
			for _, k := range ks {
				tx.UnsafeDelete(schema.Key, k)
			}
			if len(ks) < 2 {
				tx.UnsafePut(schema.Meta, schema.FinishedCompactKeyName, one(compactTo))
				tx.Unlock()
				break
			}
			tx.Unlock()
			be.ForceCommit()
		}
		be.UnlockForSafeRangeDelete()
	}()

	// The Defragment RPC, and the Hash RPC.
	wg.Add(1)
	go func() {
		defer wg.Done()
		for n := 0; n < 3; n++ {
			_ = be.Defrag()
			be.ForceCommit()
			_, _ = be.Hash(schema.DefaultIgnores)
		}
	}()
	wg.Wait()

	// Quiescent: every key as the writer and the compactor left it.
	be.ForceCommit()
	rt := be.ReadTx()
	rt.RLock()
	ks, _ := rt.UnsafeRange(schema.Key, pair(0, 0), pair(rounds+1, 0), 0)
	first, _ := rt.UnsafeRange(schema.Key, pair(0, 0), pair(rounds+1, 0), 2)
	stop := errors.New("stop")
	calls := 0
	err := rt.UnsafeForEach(schema.Lease, func(k, v []byte) error { calls++; return stop })
	lease := visit(rt, schema.Lease)
	rt.RUnlock()
	if len(ks) != 2*(rounds-compactTo) || len(first) != 2 || first[0][0] != compactTo+1 {
		panic("backend: a compacted key came back, a write was lost, or a range is not the first keys")
	}
	for i := 1; i < len(ks); i++ {
		if string(ks[i-1]) >= string(ks[i]) {
			panic("backend: a range is not in key order")
		}
	}
	if err != stop || calls != 1 || len(lease) != rounds {
		panic("backend: a visit did not stop at the visitor's error, or missed a key")
	}
	tx := be.BatchTx()
	tx.Lock()
	tx.UnsafePut(schema.AuthRoles, []byte("r"), one(1))
	_, roles := tx.UnsafeRange(schema.AuthRoles, []byte{0}, []byte{0xff}, -1)
	last, ordered := "", true
	err = tx.UnsafeForEach(schema.Key, func(k, v []byte) error {
		ordered = ordered && last < string(k)
		last = string(k)
		return nil
	})
	tx.Unlock()
	if len(roles) != 1 || err != nil || !ordered {
		panic("backend: a whole-bucket range missed a key, or the batch's visit is not in key order")
	}
	if get(be.ReadTx(), schema.Meta, []byte("hook"))[0] != rounds {
		panic("backend: the pre-commit hook's write is not in the commit")
	}
	if be.Close() != nil {
		panic("backend: Close failed")
	}
	be.ReadTx().RLock()
	be.ReadTx().RUnlock()
	_, _ = be.Size(), be.SizeInUse()

	// The reopened backend, and the snapshot's file opened as one.
	be = open("specreq-backend.db", nil)
	if get(be.ReadTx(), schema.Meta, []byte("ci"))[0] != rounds || get(be.ReadTx(), schema.Key, pair(rounds, 1)) == nil {
		panic("backend: the reopened backend lost a write made before the close")
	}
	be.Close()
	if !<-snapped {
		return
	}
	be = open("specreq-backend-snap.db", nil)
	if ci := get(be.ReadTx(), schema.Meta, []byte("ci")); ci == nil || ci[0] < snapAt || get(be.ReadTx(), schema.Key, pair(snapAt, 1)) == nil {
		panic("backend: the snapshot lost a write committed before it")
	}
	be.Close()
}
