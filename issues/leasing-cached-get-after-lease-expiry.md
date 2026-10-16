---
upstream: known
checked: 2026-10-16
links:
  - etcd-io/etcd#19091 issue closed: this issue (a cached Get returns a value overwritten after the session lease expired); closed by the stale bot
  - etcd-io/etcd#19092 pr closed: a fix (client-side Lease.Unexpired(), checked by readySession); closed unmerged
  - etcd-io/etcd#21589 pr closed: the same freshness check, bundled with the EvictRange fix (issues/leasing-evictrange-key.md); closed unmerged
---

# leasing: cached reads are stale after the session lease expires, against "linearizable reads"

- **Status**: documentation (the package claims linearizable reads from its cache; they are not,
  for the time between the server's expiry of the session lease and the client noticing it). A
  wrong result for a caller relying on the documentation.
- **Where**: `client/v3/leasing/doc.go:15` ("Package leasing serves linearizable reads from a local
  cache …"; `:32`, "Future linearized read requests using 'lkv' will be served locally for the
  lease's lifetime"); `leasingKV.readySession` (`client/v3/leasing/kv.go:477-489` at the pinned
  revision, `etc/goose.py`, `107edf7e4`), a non-blocking receive on `session.Done()`, which
  `leasingKV.get` (`kv.go:311`) uses to decide whether to serve from the cache. `Done` is closed only
  when the client's lease library closes the keep-alive channel, after its own expiry detection.
- **What happens**: client A gets `k` (cached under its session lease); A is partitioned past the
  lease's TTL; the server revokes the lease and deletes A's lease key; client B writes `k`; A's `Get(k)`
  returns its cached value while its `Done` channel is still open. Reproduction:
  `TestLeasingGetChecksForExpiration`, `upamanyus/etcd` `d065a4a9e`,
  `tests/integration/clientv3/lease/leasing_test.go:419-491` (fails often; not re-run at the pin,
  whose `leasing` code differs only by the Goose rewrite `0fc6f23b1`).
- **Expected**: a read answered from the cache returns etcd's value at some point during the call
  (linearizable), as `doc.go` says.
- **How the proof handles it**: the spec states the weaker truth. A cached `Get` returns etcd's
  record of the key at the entry's acquisition revision, at which the lease key existed
  (`getCached`, `Proof/go_etcd_io/etcd/client/v3/leasing/InvLeasingKV.lean:414-417`), and
  `leasing_cached_get_stable` (`Results.lean:180-188`) carries it to a later state only while the
  lease key keeps its incarnation; `notes/decisions.md`, "The lease-expiry window is excluded by the
  statements, not the premise" ("not linearizable, and not claimed to be"). A linearizable statement
  needs a clock model (the client can only know its lease is live from a local deadline), which
  Perennial lacks. Triage: `notes/bug-triage/etcd-19091.md`.
- **Possible fixes**: check a local lease deadline before serving from the cache (#19092, #21589;
  sound under bounded clock drift, with a margin); or document that cached reads may be stale after
  the session lease expires, until `Done` closes.
- **Found**: by upamanyus upstream (2024-12, #19091); recorded here 2026-10-16, bug triage, against
  the leasing proofs' recorded choice.
