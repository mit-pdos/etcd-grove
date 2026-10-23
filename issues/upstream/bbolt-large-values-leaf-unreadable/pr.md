Title: node: split a node too large to be read back from one page

[`splitTwo`](https://github.com/etcd-io/bbolt/blob/a4ef19710eb7ddc41fd1155336baf331b5c57ba8/node.go#L229-L234) never splits a node of at most four inodes, and [`splitIndex`](https://github.com/etcd-io/bbolt/blob/a4ef19710eb7ddc41fd1155336baf331b5c57ba8/node.go#L271-L291) always puts at least two inodes on a page, however large they are. [`leafPageElement.Value`](https://github.com/etcd-io/bbolt/blob/a4ef19710eb7ddc41fd1155336baf331b5c57ba8/internal/common/page.go#L317-L321) slices from the element's address through a `[MaxAllocSize]byte` array, so on a page larger than `MaxAllocSize` the later values cannot be read. This PR also splits a node that would be larger than `MaxAllocSize`, down to one inode per page if needed.

Fixes #<issue>

The first commit adds a test of how the issue's example is split into pages, which fails on `main`; the second, the fix, makes it pass.

Written with the assistance of generative AI; I reviewed and tested every change.
