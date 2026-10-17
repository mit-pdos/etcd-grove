---
upstream: known
checked: 2026-10-17
links:
  - etcd-io/etcd#22184 issue open: this bug, with the same analysis and a reproduction
  - etcd-io/etcd#22185 pr open: the fix (reads the revision under `revMu` instead of `s.rev()`), approved; verified on branch `pr-verify/etcd-22185`
---

# `progressIfSync` takes `store.mu` while holding `watchableStore.mu`: a three-way deadlock with a write transaction and `Commit`

- **Status**: bug at the package level (a deadlock reachable through mvcc's API), not found
  reachable in an etcd server: a lock-order inversion. `watchableStore.mu`'s documentation says
  it "should never be locked before locking store.mu"; `progressIfSync` does. The cycle needs a
  write transaction in flight while another goroutine takes `store.mu` exclusively (`Commit`,
  `Compact`, `Restore`); in the server both run on the apply goroutine (below), so they never
  overlap. etcd-io/etcd#22184 says the snapshot path's `Commit` runs "on the snapshot-send
  goroutine", which is not so at this revision or upstream `cb846f6d2`.
- **Where** (`upamanyus/etcd` `goose-lean` `09669450f`, the same code as upstream `main`
  `cb846f6d2`): `server/storage/mvcc/watchable_store.go`, `progressIfSync` (517): `s.mu.RLock()`
  (519), then `rev := s.rev()` (522), which is `s.store.Rev()` (507), a read transaction:
  `store.Read` takes `store.mu.RLock()` (`kvstore_txn.go` 47). The other two parties: a write
  transaction holds `store.mu.RLock()` from `store.Write` until its `End`, and
  `watchableStoreTxnWrite.End` (`watchable_store_txn.go` 43) takes `watchableStore.mu.Lock()`
  before releasing it; `store.Commit` (`kvstore.go` 287, also `Compact`'s and `Restore`'s
  exclusive lock) takes `store.mu.Lock()`.
- **What happens**: write txn W holds `store.mu` (R); `Commit` C queues for `store.mu` (W), which
  (Go's `RWMutex` writer preference) blocks new readers; `progressIfSync` P takes
  `watchableStore.mu` (R) and blocks in `store.mu.RLock()` behind C; W's `End` blocks in
  `watchableStore.mu.Lock()` behind P. None proceeds: the apply loop (W) is wedged, and with it
  the server. In etcd, P is a watch stream's progress request (`RequestProgress`,
  `RequestProgressAll`, and the server's periodic progress notifications), C the snapshot-send
  path's `KV().Commit()` (`createMergedSnapshotMessage`) or the backend's periodic commit.

  Reproduction: `TestProgressIfSyncDeadlock` of etcd-io/etcd#22185
  (as a file of its own: `notes/pr-verify/etcd-22185/watchable_store_progress_deadlock_test.go` on
  branch `pr-verify/etcd-22185`; copy it into `server/storage/mvcc/`): on `goose-lean` `09669450f`,
  `go test ./storage/mvcc/ -run TestProgressIfSyncDeadlock -count=1` from `server/` fails at its 3 s
  deadline ("deadlock: write txn End() blocked on watchable.mu while progressIfSync holds it and
  waits on store.mu"); with the PR's change it passes.
- **Expected**: the documented order (`store.mu` before `watchableStore.mu`) kept; no deadlock.
- **How the proof handles it**: it does not see it. Perennial's specs are partial correctness: a
  weakest precondition says nothing of an execution that blocks forever, and `sync.RWMutex`'s
  `wp_RLock`/`wp_Lock` carry no lock-order obligation. So
  `mvcc.watchableStore.progressIfSync.wp_proof`
  (`Proof/go_etcd_io/etcd/server/v3/storage/mvcc/watchableStore__progressIfSync.lean`) holds of the
  deadlocking code (through `watchableStore.rev.spec`, whose `storeReader` premise is a reader slot
  of `store.mu`, taken while `watchableStore.mu` is held shared). Lock ordering is outside what
  this repository verifies; this finding came from the PR, not the proof.
- **Possible fixes**: read `currentRev` under `s.store.revMu` (shared) instead of `s.rev()`, the
  order `watch`, `syncWatchers` and `moveVictims` already use (`watchableStore.mu` → `revMu`):
  etcd-io/etcd#22185, whose proof on branch `pr-verify/etcd-22185` re-proves the unchanged spec.
  Or read the revision before taking `s.mu` (but then the revision may be stale relative to the
  synced set it is checked against).
- **Found**: 2026-10-17, verifying etcd-io/etcd#22185 (`.claude/skills/etcd-pr-verify`); the
  reproduction is the PR's; the server-level reachability checked by the verification's reviewer.
- **Related, not fixed by #22185**: `watchableStore.Restore` (208–210) also takes
  `watchableStore.mu.Lock` before `store.mu.Lock`; it deadlocks only with a write transaction in
  flight, which in the server runs on the same apply goroutine as `Restore` (`applySnapshot`).
