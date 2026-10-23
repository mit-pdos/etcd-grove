Title: tx: keep a failed commit's freed pages pending if its meta is current

When `Commit` fails, [`rollback`](https://github.com/etcd-io/bbolt/blob/a4ef19710eb7ddc41fd1155336baf331b5c57ba8/tx.go#L322-L343) drops the pages the transaction freed from the pending list and reloads the free pages from the current meta, which is right only if that meta is still the one the transaction started from. A [meta page write](https://github.com/etcd-io/bbolt/blob/a4ef19710eb7ddc41fd1155336baf331b5c57ba8/tx.go#L605-L619) that fails in `fdatasync` leaves the transaction's own meta current, so the pages it freed become reusable while open read transactions still see them. This PR leaves the freelist as a successful `Commit` does when the transaction's meta is current.

Fixes #1311.

Written with the assistance of generative AI; I reviewed and tested every change.
