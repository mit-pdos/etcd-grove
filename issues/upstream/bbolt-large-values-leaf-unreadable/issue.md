Title: Get panics on values committed together whose sizes add up to more than 2 GiB

On `main` (a4ef197), go1.26.9 linux/amd64, default options, two values that `Put` accepts and `Commit` stores cannot be read back:

1. A write transaction creates a bucket, puts two values of 1073741823 bytes (1 GiB − 1) under the keys `a` and `b`, and commits without error.
2. A read transaction gets `b` from the bucket, and `Get` panics:

```
--- FAIL: TestDB_HugeValues (7.66s)
panic: runtime error: slice bounds out of range [::2147483664] with length 2147483647 [recovered, repanicked]
...
go.etcd.io/bbolt/internal/common.(*leafPageElement).Value(...)
go.etcd.io/bbolt.(*Cursor).keyValue(0x3be964cc7c90?)
go.etcd.io/bbolt.(*Cursor).seek(0x3be964cc7c90, {0x3be964cc7d04?, 0x5e51ca?, 0x7361e0?})
go.etcd.io/bbolt.(*Bucket).Get(0x736fa8?, {0x3be964cc7d04, 0x1, 0x71dae4?})
```

The same happens whenever bbolt writes values adding up to more than 2 GiB to one page, as it does for the values of a bucket of up to four keys: the values are committed, and reading them panics. `Get` should return each value committed in step 1.

The test above (about 5 GB of memory), in `db_test.go`:

<details>

```go
func TestDB_HugeValues(t *testing.T) {
	dbPath := filepath.Join(t.TempDir(), "db")
	db, err := bolt.Open(dbPath, 0600, nil)
	require.NoError(t, err)
	defer func() {
		require.NoError(t, db.Close())
	}()

	keys := []string{"a", "b"}
	values := make([][]byte, len(keys))
	for i := range values {
		values[i] = make([]byte, common.MaxAllocSize/2)
		values[i][len(values[i])-1] = keys[i][0]
	}

	err = db.Update(func(tx *bolt.Tx) error {
		b, err := tx.CreateBucket([]byte("data"))
		require.NoError(t, err)
		for i, key := range keys {
			require.NoError(t, b.Put([]byte(key), values[i]))
		}
		return nil
	})
	require.NoError(t, err)

	err = db.View(func(tx *bolt.Tx) error {
		b := tx.Bucket([]byte("data"))
		for i, key := range keys {
			require.Truef(t, bytes.Equal(values[i], b.Get([]byte(key))), "unexpected value for key %q", key)
		}
		return nil
	})
	require.NoError(t, err)
}
```

</details>

Without the memory, [`TestNode_split_MaxAllocSize`](https://github.com/upamanyus/bbolt/blob/fix/bbolt-large-values-leaf-unreadable/node_test.go#L171-L188) (branch [`fix/bbolt-large-values-leaf-unreadable`](https://github.com/upamanyus/bbolt/tree/fix/bbolt-large-values-leaf-unreadable)) checks that the leaf holding these two values is split into pages of at most 2147483647 bytes, the largest page `Get` can read. On `main` it fails:

```
    node_test.go:185: exp<=2147483647; got=2147483710
--- FAIL: TestNode_split_MaxAllocSize (0.01s)
```

Found while formally verifying etcd. Written with the assistance of generative AI; I reproduced the bug and reviewed the report.
