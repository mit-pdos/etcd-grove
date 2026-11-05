# Questions (restart track, R2b-3d stage 5; branch `r2b3`)

## Hub requests

### H1. A stop slot in place of the stop's inline pieces (2026-11-05, requested by the coordinator)

**Status: accepted by the coordinator (etcd-grove-82), 2026-11-05** (convert now; conditions: narrow
eliminations, whole records as arguments, the smallest `memberBuilt` ripple, `StopApi.lean` modelled on
`WalApi.lean`, the `NewServer` edit kept to the one block).

**`memberBuilt`'s ripple (condition 2).** `γk` stays behind `memberBuilt`'s existential (it already
binds `γk`); only the type of its optional `K` gains a `GName` argument. No caller passes `K` but
`memberBuiltS` (`etcdstart/Restart.lean`): `newServer`, `newServerMode`, `NewMember`, `BuildServer`,
`Start` and `restart3`'s `startMember` use the default, and their proofs unfold `memberBuilt` without
naming `K`'s arguments. So no example passes a new argument.

**The hubs.** `NewServer.specG`'s postcondition (`Spec/go_etcd_io/etcd/server/v3/etcdserver/NewServer.lean`)
and `etcdstart.memberBuilt`'s `K` (`Proof/.../examples/lib/etcdstart/Defs.lean`, the starters).

**Today, inline in `specG`'s post** (three commits of R2b-3d):
```
srvTrKeyOf srv γk ∗
srvStopKeep srv γrn (config.walDirOf cfg.DataDir' cfg.DedicatedWALDir') E.s E.γ ∗
□ (⌜on = false⌝ → srvCleanupOwn srv)
```
`srvStopKeep` takes fields (`E.s`, `E.γ`, a computed WAL directory); `srvCleanupOwn`'s mode clause
sits beside it; `srvTrKeyOf` is not threaded to `run` at all yet (`memberBuilt`'s `K` has no `γk`).

**The change, written out.**
1. A new API module `Proof/go_etcd_io/etcd/server/v3/etcdserver/StopApi.lean`, sealed
   (`@[no_expose]` body; the package's proofs `import all`):
   ```
   def srvStop.keep (s : Loc) (cfg : ServerConfig) (E : apply.AEnv GF) (γrn : RNNames) (γk : GName) : IProp GF
     -- body (sealed): srvStopKeep s γrn (walDirOf cfg.DataDir' cfg.DedicatedWALDir') E.s E.γ
     --   ∗ srvTrKeyOf s γk ∗ □ (⌜E.authOn = false⌝ → srvCleanupOwn s)
   ```
   Whole records and the configuration, no fields; the auth mode read from `E.authOn` (the hub's
   post already says `E.authOn = on`), so the slot has no `on` argument.
2. `specG`'s post: the three conjuncts above become one, `srvStop.keep srv cfg E γrn γk`.
3. `memberBuilt`'s `K : RNNames → ServerConfig → apply.AEnv GF → IProp GF` gains the key name:
   `K : RNNames → ServerConfig → apply.AEnv GF → GName → IProp GF` (default `fun _ _ _ _ => True`);
   `memberBuiltS`'s `K` becomes `srvStop.keep s`. (Needed in any case: `run.specStop` needs
   `⌜Er.ST = srvTrStopK γk⌝ ∗ srvTrKeyOf s γk` at the `γk` of `memberBuilt`'s `srvEr`, 5c part 1.)
4. Narrow eliminations, one per consumer, all used only by `run`'s deferred shutdown
   (`run.specStop`'s proof):
   - `srvStop.keep_raftStop`: with the live transport (`srvTrStop s`, from `srvApRes`), the raft
     loop's stop claim and `Er.ST` (given `Er.ST = srvTrStopK γk`): what `raftNode.stop.specStop` takes;
   - `srvStop.keep_cleanup`: the lessor's stop right, the compactor field (`compactorOk`), and with
     auth off the auth store's closer: what `Cleanup.spec` takes besides the apply thread's;
   - `srvStop.keep_census`: the kept store readers (`srvKeepRdN` and the nil compactor's), as the
     `storeRT`s `storeReaders_retire` takes;
   - `srvStop.keep_image`: the storage registry's authority and the WAL directory's equation, what
     `srvDiskImage` takes.
   `srvShutdownPre` and `run.specStop` take `srvStop.keep s cfg E γrn γk` (with the data directory
   equation) in place of `srvStopKeep … ∗ srvCleanupOwn …`.
5. Downstream, the drafts only (`Start_builtS_spec`, `Start_builtR_spec`, `BuildServer.specRestart`):
   the existential `∃ γrn wd st γst, srvStopKeep s γrn wd st γst` becomes `∃ cfg E γrn γk,
   srvStop.keep s cfg E γrn γk`.

**The caller that needs it.** `run.specStop`'s proof (5c/5d) and, through `memberBuiltS`,
`Start`'s stop variant: they need the transport key's `γk` at `memberBuilt`'s own `γk`, which no
current `K` can carry.

**The alternative inside a slot.** Keep the pieces inline and only widen `K` with `γk` (item 3):
the hub's text still changes (a fourth inline stop conjunct already exists), and every later stop
piece (auth on's closer, a lease slot's stop) lands in the hub again.

**Recommendation: convert now.** The hub's text must change anyway for 5d (`γk` into `K`); the
conversion is that change plus wrapping three existing conjuncts, about 30 lines in
`NewServer.lean`'s proof, and it collapses the four-argument existentials of the three drafts.
Conflict with `lease-expiry`: one three-conjunct block of the same postcondition, adjacent to
its lease slot's; either order merges by hand in minutes. Auth on's closer (the apply thread's, not
`NewServer`'s) later changes only `srvStop.keep`'s sealed body.

**Meanwhile (not blocked):** the slot module and its laws, and `run.specStop`'s proof over them,
are written without touching `NewServer`; `NewServer`'s intro of the slot waits for the go
(`sorry -- H1: hub request pending` if anything needs it before).

### H2 (hard stop: a trusted contract). The storage-version monitor's read token at the stop (2026-11-05)

**Status: sent to the coordinator, 2026-11-05; the proof goes on with a marked `sorry`
(`StopShutdown.stop_monitorRT`).**

`Cleanup`'s `backend.Close` needs the whole open token, so the stop's census must collect every
reader's share, including the storage-version monitor's (`mvcc.bkRTx` in `srvWTPool`'s invariant).
That invariant has two cases: the token there, or (the monitor in a session) checked out, a part of
the monitor's share of `E.γbe` deposited in its place. The plan (stage 5c) takes the first case;
nothing excludes the second. `monitorStorageVersion` is a trusted contract (names-only, axiom
`EtcdServer.monitorStorageVersion.wp_proof`) whose post is `True`, and `GoAttach`'s `Done` returns
only a thread token. So after `s.wg.Wait()` the proof cannot tell that the monitor checked the token
back in: under the contract, a monitor that exits mid-session is allowed. In Go it cannot happen
(the session checks the token back in before `RUnlock`, and the goroutine has returned when `Wait`
does). Excluding the second case by fractions of `E.γbe` would need `bemuP`'s half, that is,
`s.bemu`'s write lock, which the shutdown does not take.

**Options.**
1. The monitor's contract returns its session state at exit (for example a session key `svKey γp`
   that the invariant's checked-out case holds and the post gives back), and `GoAttach`/`Wait`
   carry a goroutine's final resource back to the waiter (a `{P} f {Q}` form, with `Q` deposited at
   `Done`). This widens a trusted contract's post: a hard stop.
2. A narrower version of 1: only the `Wait` side is generic, and the monitor's post gives the key.
3. Scope premise on `run.specStop`: no monitor started. `restart3` starts one through `Start`, so
   this does not cover the use.

**Recommendation: 1 (or 2).** The change is the honest contract: the real monitor ends its session
before it returns. Until it is decided, `stop_monitorRT` is a `sorry` with this entry's name.

## Decided by the agent, pending the user

(none yet)
