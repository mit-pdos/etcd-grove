# Perennial `d0324b842`: an unfinished port (2026-10-12, branch `perennial-d0324-wip`)

**Does not build.** Kept for the next Perennial bump. `lean` pins `a54e1999f` instead (see
`STATUS.md`, "Perennial `a54e1999f`: the proof layout"), because Perennial `d0324b842`
cannot verify etcd's STM: since `3fbe65749` (panics on the exception monad) Perennial's model
does not propagate a panic to the caller, so `stm.fetch`/`commit`'s `panic(stmError{..})`,
recovered by `runSTM`'s goroutine two calls up, is stuck in the model. An axiom for the STM
would contradict the model's own code (stuck there) and could derive `False`. This port waits
for Perennial to propagate panics to the caller's deferred functions.

## Done on this branch

- Pin `d0324b842`, translations regenerated (`etc/goose.py`: 25 files), imports of Perennial's
  new proof layout (`sync_proof.*`, `context_proof.context_init`, `sort_proof.*`,
  `slices_proof.*` -> the package umbrellas).
- `wp_auto` before `wp_with_defer` (defer results, Perennial `6ccfa9d0f`): 53 modules.
- Area A (raft, the standard-library wrappers, register; stopped before its final build):
  `strings.Join` with `JoinFits`; newRaft's voters bound.
- Area B (cache, btree): btree builds (`btree.Link`, `Results`); the cache but four modules
  (the `fmt` calls, now coverable by area A's axioms below, not yet applied).
- Area C (clientv3): `leasing`, `experimental/recipes`, base `client/v3`, `api/**`,
  `google_golang_org/**` build; `concurrency` fails (the STM, 12 modules; `Mutex.tryAcquire`,
  `Election.Campaign`: `fmt.Sprintf("%s%x", pfx, s.Lease())` with the named `LeaseID`, outside
  `ArgsWf` and outside area A's axioms).
- Area D (server, storage, pkg, bbolt, zap, otel): stopped early; mostly unported.

## Trust added on this branch (to remove later)

- **`fmt.Errorf.wp_proof`** (axiom, `Proof/fmt/Errorf.lean`): `fmt.Errorf` for arguments each
  basic (`ArgWf`) or with a "returns some string" spec of `Error()`/`String()`
  (`fmt.argsOk`); assumes no argument implements `fmt.Formatter`. Replaces Perennial's
  `ArgsWf`-only spec for the cache's `%w` errors.
- **`fmt.Printf.wp_proof`** (axiom, `Proof/fmt/Printf.lean`): the same for `Printf`.
- **`time.Duration.String.wp_proof`** (axiom, `Proof/time/Duration__String.lean`): returns
  some string.
- **`fmt.Sprintf.wp_hex`** (axiom, `Proof/fmt/Sprintf.lean`): `Sprintf("%x", n)` of a
  `uint64` has at most 16 bytes (Perennial's model does not format `%x`); for newRaft's
  `strings.Join` of the voters, whose `JoinFits` it discharges.
- **Vacuous specs** (not trust, but proved only vacuously):
  `concurrency.lockerMutex.Lock.spec`, `Unlock.spec` restated in the `shouldPanic` style
  (precondition: a WP of `exceptionDo (panicVal #err)` for every non-nil `err`, equivalent to
  `▷ False` for a caller): unusable until panics propagate.

## Statement changes on this branch

- `newWatcher`: `0 ≤ bufSize < 2^32` (`make(chan T, n)` is stuck where `makechan` may panic,
  Perennial `c3b58b815`); `CfgBounded` and `isCacheFields` likewise; `newCache.spec`, `New.spec`
  inherit it. (Also an issue: `makechan` panics on a huge `PerWatcherBufferSize`, not only a
  negative one; `issues/cache-ready-after-retry.md` mentions only negative values.)
- clientv3 `Op` getters (24) and `OpResponse.Get`: value-receiver specs (the method-value change,
  Perennial `94123213b`).
- `newRaft.spec`: voters `≤ 2^40` (was `≤ 2^62`), for `JoinFits`; `NewRawNode.spec`,
  `RestartNode.spec` inherit it.
- `lockerMutex.Lock`/`Unlock` (above).
