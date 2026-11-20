# Attack on bbolt.Bucket.ForEach_kvr / ForEach_kvw (auth-schema-srv ab063377ca)

Targets: `Spec/go_etcd_io/bbolt/Bucket__ForEach_kv{r,w}.lean` in /shared/etcd-grove-authschema (read only),
against the kv contract of `Proof/go_etcd_io/etcd/server/v3/storage/backend/InvBbolt.lean` and the `_kv`
specs (Begin, Rollback, Commit, Cursor_kvr/kvw, Seek/Next, Tx.Bucket_kvr/kvw, Put/Delete,
CreateBucketIfNotExists, DeleteBucket, Size, DB, Info, Stats, Close).
Go: fork `github.com/upamanyus/bbolt@ea4cab526797` (examples/go.mod); its `cursor.go` is byte-identical to
upstream v1.5.0 and its `ForEach` body identical (fork bucket.go:586-597, upstream 585-596).
Tests: /shared/tmp/foreach-attack/fa/fa_test.go (log run2.log), all PASS.

**Verdict: survives.** No counterexample found; findings are MINOR (text only).

## Claims pinned down
- kvr: pre `rBkt tx b es` (persistent) ∗ `rtxStats tx` (exclusive) ∗ `txLive tx q` ∗ `I 0` ∗ □ visitor
  triple; visitor gets `I i ∗ txLive tx (q/2) ∗ k≠nil ∗ txBytes k e.1 ∗ txBytes v e.2`, must return
  `txLive tx (q/2)`; post returns rtxStats, txLive q, `I |es|` or `E i err`, i < |es|.
- kvw: same over `bktEnts m`, `S.lookup n = some m`, `G n = g` (current handle); walk keeps `ownWTxG`,
  visitor gets `txLive tx (1/2)`.
- Note: no validity law for `txLive` (no `q ≤ 1`), no exclusivity for `ownWTxG`; only `rtxStats_excl`.

## Families
1. **Client-chosen I/E, visitor touching the tx/bucket.** Every mutating or walking op needs a resource
   the walk holds: Put/Delete/Cursor_kvw/Commit/CreateBucketIfNotExists/DeleteBucket/ownWTxG_fill need
   `ownWTxG` (kvw walk holds it; only one per tx, from Begin); Cursor_kvr/Tx.Bucket_kvr/re-entrant
   ForEach_kvr need `rtxStats tx` (walk holds it; `I` cannot also hold it — client can't own two, and
   even then a contradiction only arises client-side). What the visitor CAN do with `txLive` fractions:
   Size, DB, Info, txBytes reads, Seek/Next on an `ownCur` made before the walk (kvr: Cursor_kvr returns
   ownCur without keeping rtxStats; kvw: the ownCur is consumed by Cursor_kvw's wand before ownWTxG can
   be passed to ForEach). Go: a prior cursor used inside the walk is harmless
   (`TestReadVisitorUsesPriorCursor` PASS). `I` holding `ownDB`(+`wrTok`): visitor Begin(read) harmless;
   Close or a growing Commit deadlock on mmaplock/rwlock (partial correctness, not a counterexample —
   my first run deadlocked exactly so: reader open + writer remap, db.go:508). Nil `fn`: the visitor
   triple at i=0 must be proved from a real `I 0` and cannot be (calling nil panics, and no premise
   yields False); empty bucket → vacuous, and Go makes no call. **Blocked.**
2. **Half txLive to a whole.** Total mass per tx is 1 (only Begin_kv/ownWTxG_live produce it; ForEach
   returns exactly what it took). kvr walk keeps q/2, so visitor ≤ 1 − q/2 < 1: Rollback_kv
   (`txLive tx 1 ∗ rtxSnap`) unreachable. kvw: visitor 1/2, rest inside walk's ownWTxG; Rollback_kv also
   needs `rtxSnap`, which write txs never get. Second read tx: different loc, fractions don't combine.
   The visitor cannot park its half in `I` (must return `txLive (q/2)` itself). **Blocked.**
3. **Persistent txBytes over changing buffers.** Reads need `txLive` (`txBytes_acc`), which ends at
   Rollback/Commit. During the tx: node.put/del replace slice headers, never bytes; allocate/remap only
   in Commit; DeleteBucket only marks pages pending; write-tx inline buckets are cloned at openBucket;
   Put values are `↦*□`. Go: stashed visitor slices unchanged after puts, `Delete` with the stashed key
   (Delete_kv own=false), DeleteBucket, recreate + 5000 puts, values 0/10/3000/70000 B (overflow)
   (`TestWriteTxStashSurvivesMutation` PASS); read-tx stash unchanged across 30 concurrent commits
   overwriting/deleting every key (`TestReadTxStashSurvivesCommits` PASS). **Blocked.**
4. **es vs what Go walks.** ForEach uses `First`, which no earlier kv spec covered (Seek_kv/Next_kv do);
   `first()` (cursor.go:44-62) skips an empty leaf via `next()`, which loops over empty leaves
   (cursor.go:239-243). Go: 40 seeds, 30000 keys, write tx deleting prefix/suffix/random ranges up to
   8000 keys (whole leaves and subtrees empty) plus re-puts: walk = sorted model every time
   (`TestWriteTxEmptyLeaves`); all deleted → 0 visits, one put back → 1 (`TestWriteTxAllDeleted`).
   Empty values: write tx gives `v == nil` for Put(k, nil), non-nil empty otherwise; read tx non-nil
   empty — all compatible with `txBytes v ""` (same claim as `curAt`). Nested buckets (v = nil) are
   unrepresentable in `Data` and no kv spec creates one (no Bucket.CreateBucket_kv); only a file
   assumed by `fileHolds` could hold one — the same exposure as Seek_kv/Next_kv, not new. **Blocked.**
5. **Error ordering.** Go returns the visitor's first non-nil error immediately (bucket.go:592-594); the
   only other error, ErrTxClosed, is excluded by `txLive` (`tx.db == nil` only after close). Index of
   the error entry i < |es| holds since the visitor is only called on entries. **Blocked.**
6. **Write tx seeing own writes.** Cursor uses `pageNode` (materialized nodes first); confirmed by
   family-4 tests (re-puts visible, deletes skipped). **Holds.**

## Findings
- MINOR (text): citation. The fork's lines are bucket.go:586-597; the empty-leaf logic that kvw relies
  on is in `first()` cursor.go:44-62 and `next()` 215-247, not 32-42. Fix: "upstream v1.5.0
  bucket.go:585-596 (fork 586-597); cursor.go First/first 35-62, next 215-247 (empty leaves after own
  deletes skipped: tests/... TestWriteTxEmptyLeaves)".
- MINOR (text): the nested-bucket exclusion is stated as "as for Seek_kv (etcd's buckets hold none)";
  say where it is enforced: `Data` cannot represent one and no kv spec creates one, so only the
  `fileHolds` premise of Open_kv carries it.
- MINOR (tests): consider adding an own-deletes-empty-leaves test (mine above) to
  examples/bbolt/foreachkv — the author's TestOrderWriteTxSeesOwnWrites does not empty a leaf, which is
  the one path First adds over Seek.
- Observation (not about these axioms): the kv contract lets one goroutine Commit a growing write tx
  while it holds an open read tx — a deadlock in Go (db.go:508 mmaplock), harmless for partial
  correctness.

## Not tried
- Lean derivations (no build, per brief); the triple reasoning above is by hand.
- Multi-goroutine use of one read tx concurrently with the walk beyond reasoning (txLive fractions in
  forked goroutines doing reads; Go looked read-only/atomic-stats).
- Files written by other bbolt versions/configs (freelist types, 32-bit), page sizes other than default.
