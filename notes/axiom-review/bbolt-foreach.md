# Review: `bbolt.Bucket.ForEach_kvr` / `ForEach_kvw` (auth-schema-srv A2)

Reviewed 2026-11-17 by the `axiom` skill, as an independent reviewer (for etcd-grove-03), on branch
`auth-schema-srv` at `ab063377ca`: the two new trust-boundary statements, the user's choice (B) of
`notes/auth-schema-srv-a2-draft.md` (bbolt's `Bucket.ForEach` reads `b.tx.db`, so it cannot be proved over
the opaque kv contract with a `Cursor.First_kv` alone).

| # | Axiom | Spec file | Verdict |
|---|---|---|---|
| 1 | `bbolt.Bucket.ForEach_kvr.wp_proof` | `Spec/go_etcd_io/bbolt/Bucket__ForEach_kvr.lean` | **survives** |
| 2 | `bbolt.Bucket.ForEach_kvw.wp_proof` | `Spec/go_etcd_io/bbolt/Bucket__ForEach_kvw.lean` | **survives** |

The attacker's report: `bbolt-foreach/attack-report.md` (families tried: client-chosen `I`/`E` and a visitor
touching the transaction or bucket, re-entrant walks, half a `txLive` made whole, persistent `txBytes` over
changing buffers, `es` vs what Go walks (empty leaves), error ordering, a write transaction seeing its own
writes); its Go tests: `bbolt-foreach/fa_test.go.txt` (all pass against the fork `upamanyus/bbolt@ea4cab526797`).

MINORs, all applied before the axioms were added: (1) the citations (fork `bucket.go:586-597`; `first()`
`cursor.go:44-62`, `next()` 215-247); (2) the docstring says where nested buckets are excluded (`Data` cannot
represent one, no kv spec creates one, only `Open_kv`'s `fileHolds` premise could carry one, as for
`Seek_kv`); (3) the attacker's `TestWriteTxEmptyLeaves`/`TestWriteTxAllDeleted` added to
`examples/bbolt/foreachkv/empty_leaves_test.go` (pass). Observation outside these axioms: the kv contract lets
one goroutine commit a growing write transaction while it holds an open read transaction, a deadlock in Go
(`db.go:508`), harmless for partial correctness.
