Title: bucket: reject a value too large to be stored with its key

[`Put`](https://github.com/etcd-io/bbolt/blob/a4ef19710eb7ddc41fd1155336baf331b5c57ba8/bucket.go#L540-L546) checks the key against `MaxKeySize` and the value against `MaxValueSize` separately, but a page holding the entry must fit in `MaxAllocSize` (2 GiB − 1 on 64-bit platforms): [`WriteInodeToPage`](https://github.com/etcd-io/bbolt/blob/a4ef19710eb7ddc41fd1155336baf331b5c57ba8/internal/common/inode.go#L80-L81) and [`leafPageElement.Value`](https://github.com/etcd-io/bbolt/blob/a4ef19710eb7ddc41fd1155336baf331b5c57ba8/internal/common/page.go#L317-L321) slice the entry out of a `[MaxAllocSize]byte` array. This PR makes `Put` return `ErrValueTooLarge` when a page holding only the key and value would be larger than `MaxAllocSize`.

Fixes #<issue>

The first commit adds a test of the issue's example, which fails on `main`; the second, the fix, makes it pass.

Written with the assistance of generative AI; I reviewed and tested every change.
