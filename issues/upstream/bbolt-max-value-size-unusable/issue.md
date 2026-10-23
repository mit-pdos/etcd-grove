Title: Put accepts a value of MaxValueSize bytes that Commit or Get then panics on

On `main` (a4ef197), go1.26.9 linux/amd64, default options, `Bucket.Put` accepts a value of `MaxValueSize` bytes, but the entry cannot be stored:

1. With a 2-byte key (`b.Put([]byte("ab"), make([]byte, bolt.MaxValueSize))`), `Put` returns nil and the transaction's `Commit` panics:

   ```
   panic: runtime error: slice bounds out of range [::2147483648] with length 2147483647
   ```

2. With a 1-byte key (`b.Put([]byte("a"), ...)`), `Put` and `Commit` return nil, and a later `Get` of the key panics:

   ```
   panic: runtime error: slice bounds out of range [::2147483663] with length 2147483647
   ```

The same happens for any key and value whose lengths add up to more than 2147483631 bytes (2 GiB − 17), although each is within `MaxKeySize` and `MaxValueSize`. `Put` should return `ErrValueTooLarge` for a key and value that bbolt cannot store, as it does for a value longer than `MaxValueSize`.

[`TestBucket_Put_MaxValueSizeWithKey`](https://github.com/upamanyus/bbolt/blob/fix/bbolt-max-value-size-unusable/bucket_test.go#L1231-L1251) (branch [`fix/bbolt-max-value-size-unusable`](https://github.com/upamanyus/bbolt/tree/fix/bbolt-max-value-size-unusable)) runs both cases; on `main` each fails (run one at a time with `-run 'TestBucket_Put_MaxValueSizeWithKey/^a$'` and `/^ab$`, output trimmed):

```
--- FAIL: TestBucket_Put_MaxValueSizeWithKey/ab (3.34s)
panic: runtime error: slice bounds out of range [::2147483648] with length 2147483647 [recovered, repanicked]
...
go.etcd.io/bbolt.(*Tx).Commit(0x225d9014e2c0)
```

```
    bucket_test.go:1248: 
        	Error:      	Expected error with "value too large" in chain but got nil.
        	Test:       	TestBucket_Put_MaxValueSizeWithKey/a
consistency check failed (1 errors)
runtime error: slice bounds out of range [::2147483663] with length 2147483647
```

A database left by the second case keeps the committed entry, and both `Get` and `Tx.Check` panic on it. Keeping a key and value under 2 GiB − 32 bytes in total avoids this.

Found while formally verifying etcd. Written with the assistance of generative AI; I reproduced the bug and reviewed the report.
