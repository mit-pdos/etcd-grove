Title: server/auth: reject user and role names longer than the max key size

[`UserAdd`](https://github.com/etcd-io/etcd/blob/3aaab3479b6c4f5fe1b2b8f33437093c2caae88a/server/auth/store.go#L423-L426) and [`RoleAdd`](https://github.com/etcd-io/etcd/blob/3aaab3479b6c4f5fe1b2b8f33437093c2caae88a/server/auth/store.go#L764-L767) check only that the name is not empty, then store it as a bbolt key. bbolt rejects keys longer than `MaxKeySize` (32768 bytes), and the backend treats any [failed write](https://github.com/etcd-io/etcd/blob/3aaab3479b6c4f5fe1b2b8f33437093c2caae88a/server/storage/backend/batch_tx.go#L183-L189) as fatal, so every member exits applying the request. This PR returns an error for such names next to the empty-name check, which also applies an entry already in the log as an error.

Fixes #<issue>

The first commit adds a test of the issue's example, which fails on `main`; the second, the fix, makes it pass.

Written with the assistance of generative AI; I reviewed and tested every change.
