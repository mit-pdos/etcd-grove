# `EtcdServer.monitorStorageVersion` with the session receipt (H2): survives (2026-11-05)

**Reviewed.**
- The axiom `EtcdServer.monitorStorageVersion.wp_proof`
  (`Proof/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__monitorStorageVersion.lean`), its triple in
  `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__monitorStorageVersion.lean`, as widened by H2
  on branch `r2b3` at `a50f07cd64`:
  ```
  ∀ on s E ρ (γp : WTNames) (r : GName),
  {{ isPkgInit etcdserver ∗ isServerReqM on s E ρ ∗ srvSVRes s E ∗ srvWTPool E γp ∗
     dghostVar γp.reg DFrac.discard (some r) ∗ ownToks r 1 }}
    s.monitorStorageVersion()
  {{ RET #(); ownToks r 1 }}
  ```
  Before H2 the post was `True` and the pre had no register or receipt.
- What it is used with: `srvWTPool` (`InvApplier.lean:1069`; its checked-out case holds a part of
  `E.γbe`, the register fact and `ownToks r 1` or the stop's `goWaited` half), `goAttachInv`/
  `goWaited`/`goWaited_running` (`InvGoAttach.lean`), `stop_monitorRT` (`StopShutdown.lean:162`), and
  the one use of the axiom, `EtcdServer__Start.lean:147-148` (`GoAttach` with the receipt at `γg.run`,
  which `EtcdServer__start.lean:500` puts in the register).
- etcd at the pin of `etc/goose.py` (the fork's `673da07c8`, clone `.lake/goose/etcd`; it differs from
  `.lake/go-src/etcd`'s `249d76bea` only in `applyAll`'s merged-snapshot guard). Line numbers below are
  at `673da07c8`.

**Verdict: survives.** Every backend session of the monitor opens and closes inside one call of
`StorageVersion` or `UpdateStorageVersion`. Each of those calls takes `s.bemu.RLock()` and releases it
with a `defer`. The monitor spawns no goroutine, and the only way it returns is the `stopping` case of
its `select`, between two rounds. The receipt is passed through unchanged, so no client can get two
receipts out of it. No counterexample and no `issues/` finding.

## The claims

1. When the call returns, no read session of the monitor is open: the read token is back in the pool.
   That is what lets the post give back `ownToks r 1`.
2. The post gives back the receipt the pre took. It gives no more than that, and it gives no fact about
   the pool.
3. The old claims, unchanged by H2:
   - no panic;
   - every session runs under `s.bemu`'s read lock;
   - the read token is checked in before `RUnlock`;
   - one write-back token is spent per `Unlock`;
   - `meta/storageVersion` is not a hook's key;
   - the migration may put the key several times in one session.

## Attacks tried

1. **A return with a session open.** `monitorStorageVersion` (`server.go:2264`) loops on a `select`
   whose only `return` is the `<-s.stopping` case (`server.go:2271-2273`). That case is chosen only
   between two rounds, after `monitor.UpdateStorageVersionIfNeeded()` has returned. That function
   (`version/monitor.go:108`) opens a backend session in only two places:
   - `GetStorageVersion` → `s.StorageVersion()` (`server.go:2227`): `s.bemu.RLock(); defer
     s.bemu.RUnlock()`, then `schema.DetectSchemaVersion(s.lg, s.be.ReadTx())`. That function takes
     `tx.RLock(); defer tx.RUnlock()` (`schema.go:85-89`), so the `ReadTx` lock is released before
     the outer `RUnlock`.
   - `UpdateStorageVersion` (`adapters.go:76`): `s.bemu.RLock(); defer s.bemu.RUnlock()`, then
     `tx.LockOutsideApply(); defer tx.Unlock()`. Deferred calls run last-in first-out, so `Unlock`
     (and any commit inside it, `batch_tx.go:328`) runs before `RUnlock`. This is the "checked in
     before `RUnlock`" order the contract describes.

   Neither function returns anything that holds a lock or a transaction. `StorageVersion` returns a
   `*semver.Version` copied from the value it read, and `UpdateStorageVersion` returns an `error`.
   **Blocked.**
2. **A panic with a lock held.** Every lock above is released by a `defer`, so it is released during
   a panic too. A panic still ends the process (there is no `recover` on the path; the only
   `recover`s are in `backend.go:667,759`, the backend's own defrag and commit paths). It would refute
   the old "no panic" claim, not the widened one. The panics on the path:
   - `ValidateCalledOutSideApply` (`verify.go:40`): only with `ETCD_VERIFY` set, and only inside
     `applyAll`'s stack, which the monitor's goroutine is not in.
   - `binary.BigEndian.Uint64` on a `meta/consistent_index` or `meta/term` value shorter than 8
     bytes (`cindex.go:44,49`, through `UnsafeDetectSchemaVersion`): the server writes only 8-byte
     values there. Not tried (below).
   - `storage.MinimalEtcdVersion`'s three `panic(err)` (`storage.go:102-120`): only on the downgrade
     path, and only on WAL I/O errors (point 6).

   **No new panic.**
3. **A session that outlives the call (a spawned goroutine).** `UpdateStorageVersionIfNeeded` calls
   `GetClusterVersion`, `GetStorageVersion`, `UpdateStorageVersion` and `GetDowngradeInfo`, and
   logs. It does not call the adapter's `UpdateClusterVersion`, the one adapter method that
   `GoAttach`es (`adapters.go:44`). `time.After` starts a timer, not a goroutine that touches the
   backend. The backend's own background commit loop is the backend's, not the monitor's: it takes
   the batch lock, not the monitor's read token. **Blocked.**
4. **Two receipts, or a forged pool.** The contract takes `ownToks r 1` and gives back
   `ownToks r 1`. It says nothing about the pool's state at return, so whatever the pool holds is
   still governed by its invariant only. Duplicating a receipt through the axiom would need the
   axiom to return more than it took, and it does not.
   - The register is set-once and persistent. `start` sets it to `γg.run` (`EtcdServer__start.lean:500`).
   - A second pool with another register would need a quarter of `E.γbe` and the read token
     (`srvWTStock`), which the first pool holds.

   So `r` is `γg.run`, and the only `ownToks γg.run 1`s are `GoAttach`'s receipts, which
   `goWaited_running` rules out once `Wait` has returned. **No exploit.**
5. **The stop's use (`stop_monitorRT`), in Go.** `run`'s defer (`server.go:819-835`) runs `close(s.stopping)`,
   then `s.wg.Wait()`, then `s.r.stop()` and `Cleanup`, which takes `s.bemu.Lock()` before
   `s.be.Close()` (`server.go:960-963`). By the time the backend closes, the monitor has run its
   deferred `wg.Done()`, so every one of its sessions is closed. Go's `bemu.Lock` would also wait for
   a session that was still open. The model's argument (no receipt left after `Wait`, so the token is
   in the pool) matches what Go does. `select` may pick `time.After` after `stopping` is closed, and
   the monitor then runs one more round, but it still runs before `Done`. **Blocked.**
6. **Concurrent or repeated calls.** A program could `GoAttach` the monitor twice, each copy with its
   own receipt and its own `srvSVRes`. In Go the two copies' `StorageVersion`s share `readTx`'s read
   lock, and their `UpdateStorageVersion`s are serialized by the batch mutex. Nothing panics. The
   model has only one read token, so a proof of the real code would have to make the second session
   wait, but the triple only claims no panic and a receipt passed through, and both are true. **No
   panic.**

## Old claims (the docstring)

- The text on sessions (the bemu read lock, the read token checked out and back before `RUnlock`, one
  `wbTok` per `Unlock`) matches `adapters.go:76-84` and `server.go:2227-2238`.
- `storageVersion` is a key of the hook bucket `meta` that is not one of the hook's own keys. The
  repeated put is the fixed `issues/etcd-backend-duplicate-put-stale-read.md`.
- One inaccuracy, not part of H2. The header and `notes/audit.md` call the WAL access "reads", and it
  is a reopen. `UnsafeMigrate` calls `w.MinimalEtcdVersion()` on a downgrade (`schema.go:69-71`).
  `storage.MinimalEtcdVersion` (`storage.go:102`) takes `st.mux.Lock()` and closes the WAL. It then
  reopens it (`st.w.Reopen`, `wal.go:268`), reads it all, and stores the new `*WAL` in `st.w`. All of
  this happens under the backend's batch lock. The raft loop's `Save`/`SaveSnap`/`Sync` take
  `st.mux.RLock()`, so Go is synchronized. Still, the monitor writes a field the raft side owns, with
  no resource for it. It happens only when the target is below the storage version, which needs a
  downgrade that no closed theorem's workload enables. It panics only on WAL I/O errors. Suggested
  wording: "the WAL (reopened and read on a downgrade, under `st.mux`)". The contract's statement is
  unchanged.

## Not tried

- No Go test or Lean counterexample: no attack produced a run to test.
- A backend whose `meta/consistent_index` or `meta/term` is shorter than 8 bytes. The server writes
  only 8-byte values, but `isBackend`'s contract might not say so.
- Outside this contract: the untranslated `etcdhttp` `/version` handler (`api/etcdhttp/version.go:37`)
  also calls `s.StorageVersion()`, from a goroutine that is not `GoAttach`ed. Before the backend
  closes, `Cleanup`'s `bemu.Lock` waits for such a session. A request after the close reads a closed
  backend. That is neither this axiom's concern nor the pool's: the handler is not in the verified code.
