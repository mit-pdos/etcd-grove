package bbolt

import (
	"encoding/binary"
	"sync/atomic"

	bolt "go.etcd.io/bbolt"
)

var bankBucket = []byte("bank")

// acked is the client's durable record of the last transfer an Update acknowledged (in the bank
// test, a witness file; here a value the caller keeps across boots, as a crash-surviving
// invariant would).
var acked atomic.Uint64

func get8(b *bolt.Bucket, k string) uint64 {
	v := b.Get([]byte(k))
	if len(v) != 8 {
		return 0
	}
	return binary.LittleEndian.Uint64(v)
}

func put8(b *bolt.Bucket, k string, x uint64) error {
	v := make([]byte, 8)
	binary.LittleEndian.PutUint64(v, x)
	return b.Put([]byte(k), v)
}

// REQ bbolt/crash-atomic-durable: one boot of a crash-safe client. After any crash, the database
// Open finds is some committed state (a transfer is all or nothing: the two balances sum to 100),
// and holds every transfer whose Update returned nil with NoSync off (its sequence number is at
// least the acknowledged one). A View reads one committed state.
// Users: examples/bbolt/bank/bbolttest.go:216-300 (recoverState, apply, Boot); etcd's restart
// (the backend's last commit, server/etcdserver/bootstrap.go's openBackend, through 4a).
// Assumes: path's file was only ever written by this function (its boltFile and the client's
// boltState in a crash-surviving invariant; fileHolds_alloc at each boot from the crash law's
// fileHolds); acked is crash-surviving and only raised after a nil Update; default options.
// Specs: Open.spec, DB.View.spec, DB.Update.spec, Tx.Bucket.spec, Tx.CreateBucket.spec,
// Bucket.Get.spec, Bucket.Put.spec, DB.Close.spec; laws: boltCrash, fileHolds_alloc,
// boltState_frac, BoltSt.commit/settle (the model).
func ReqCrashAtomicDurable(path string) {
	db, err := bolt.Open(path, 0o600, nil)
	if err != nil {
		return
	}
	defer db.Close()
	var a, b, seq uint64
	var exists bool
	if err := db.View(func(tx *bolt.Tx) error {
		bk := tx.Bucket(bankBucket)
		if bk == nil {
			return nil
		}
		exists = true
		a, b, seq = get8(bk, "a"), get8(bk, "b"), get8(bk, "seq")
		return nil
	}); err != nil {
		return
	}
	if !exists {
		if acked.Load() != 0 {
			panic("crash: an acknowledged transfer is lost (the bank is gone)")
		}
		if err := db.Update(func(tx *bolt.Tx) error {
			bk, err := tx.CreateBucket(bankBucket)
			if err != nil {
				return err
			}
			return put8(bk, "a", 100)
		}); err != nil {
			return
		}
		a, b, seq = 100, 0, 0
	} else {
		if a+b != 100 {
			panic("crash: a torn transfer")
		}
		if seq < acked.Load() {
			panic("crash: an acknowledged transfer is lost")
		}
	}
	// one transfer of 1 from a to b
	err = db.Update(func(tx *bolt.Tx) error {
		bk := tx.Bucket(bankBucket)
		if bk == nil {
			panic("crash: the bank vanished")
		}
		x, y, s := get8(bk, "a"), get8(bk, "b"), get8(bk, "seq")
		if x == 0 {
			return nil
		}
		if err := put8(bk, "a", x-1); err != nil {
			return err
		}
		if err := put8(bk, "b", y+1); err != nil {
			return err
		}
		seq = s + 1
		return put8(bk, "seq", seq)
	})
	if err == nil {
		acked.Store(seq) // durable: the Update synced its commit
	}
}
