// Package bboltnan is a counterexample to the bbolt key-value axioms (Spec/go_etcd_io/bbolt/,
// notes/axiom-review/bbolt.md): Run meets every premise of the axioms it calls, which say it
// returns, yet on amd64 its Commit panics ("inode overflow").
//
// A NaN FillPercent passes bbolt's clamp (node.splitTwo compares it with < and >), and
// int(pageSize * NaN) is MinInt64 on amd64, which splitIndex reads as the uintptr 2^63: a leaf
// is split only into its last 3 entries and the rest, and node.write panics on a page of 65535
// entries or more.
package bboltnan

import bolt "go.etcd.io/bbolt"

// Run opens a database at path (a new file), creates bucket "b", sets its FillPercent to NaN,
// puts 70000 keys with empty values and commits.
func Run(path string) {
	db, err := bolt.Open(path, 0600, &bolt.Options{})
	if err != nil {
		return
	}
	tx, err := db.Begin(true)
	if err != nil {
		return
	}
	b, err := tx.CreateBucketIfNotExists([]byte("b"))
	if err != nil {
		return
	}
	z := 0.0
	b.FillPercent = z / z
	for i := uint64(0); i < 70000; i++ {
		k := []byte{byte(i >> 16), byte(i >> 8), byte(i)}
		if err := b.Put(k, []byte{}); err != nil {
			return
		}
	}
	tx.Commit()
}
