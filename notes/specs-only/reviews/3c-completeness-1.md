# Review: batch 3c (the lessor), completeness, round 1

Reviewer agent, 2026-11-09, at `a098c18d14` (the 3c draft). Read-only. Targets:
`SpecPlan/Spec/go_etcd_io/etcd/server/v3/lease/` (the API files; the internal helpers only where a caller
reaches them) and `examples/specreq/lease/lessor.go`. Go: `.lake/src/server` (= the pinned
`a4d2bb17`). I formed the findings below before reading `batch-3c.md`; what that report changes is
noted at the end.

## The users, by pattern

Every importer of `go.etcd.io/etcd/server/v3/lease` in the pinned server (non-test), the examples
(`examples/mvccrand`, a translated Goose project, and the untranslated tests under
`examples/etcd/lease*`, `examples/axiomcx/*`), and the hand-offs in
`req/go_etcd_io_etcd_server_v3_lease.md` (2c, 2d, 2e; 3a's and 3b's needs are in their own req files
and in the `txn/` specs, which already consume `lessorState`). No Kubernetes code imports the
package.

| # | pattern (what the caller relies on) | call sites | spec | snippet |
|---|---|---|---|---|
| A | **Grant at the writer**: the three errors, else live with `max ttl minTTL`; `l.ID`, `l.TTL()` | `apply/backend.go:84`; `mvccrand.go:503` | `Grant`, `TTL`, `lessorAt_obj`, `leaseObj_id` | `ReqGrantLookup` |
| A' | **the post-lock hook runs inside Grant's (and Checkpoint's) lock** | `mvccrand.go:504` (`checkHook`, a panic guard); 2d's consistent index (`server.go:404`, hook saved per `LockInsideApply`) | none (F2) | none |
| B | **Revoke at the writer through mvcc's deleter**: the lease's keys deleted in one transaction, sorted; lease gone | `apply/backend.go:95`, `apply/auth.go:190-195`; `mvccrand.go:528` | `Revoke`, `rdOk` | `ReqRevokeDeletes` |
| B' | **Revoke after a snapshot**: the deleter is then the server's closure `s.kv.Write(...)` (`server.go:1087`), not mvcc's | `apply/backend.go:95` after `applySnapshot` | `Revoke` (general), but no one owes `rdOk` for it (F3) | none |
| C | **Checkpoint**: never fails, readers see nothing change | `apply/backend.go:101` | `Checkpoint` | `ReqCheckpointNoop` |
| D | **Lookup/Keys at the writer** (exact state) | `txn/put.go:83`, `apply/auth.go:199,214`; `mvccrand.go:548-550` | `Lookup`, `Keys`, `lessorState_le` | `ReqGrantLookup`, `ReqAttachDetach` |
| E | **mvcc's GetLease/Attach/Detach** (put panics on an Attach error; restore logs it) | `kvstore_txn.go:233,273,285,335-338`, `kvstore.go:398`; `mvccrand.go:545` | `GetLease`, `Attach`, `Detach` | `ReqAttachDetach` |
| F | **SetRangeDeleter at construction** (twice: store, then watchable store) | `kvstore.go:117`, `watchable_store.go:107` | `SetRangeDeleter` | `ReqRevokeDeletes` |
| G | **readers with a lower bound**: Lookup, Keys of a possibly revoked object, `TTL()`, `Remaining()`, `Demoted()`, `l.ID` | `v3_server.go:512,592-595,624-627,645-662,738`, `leasehttp/http.go:91,124-150` (the leader's handler, `server.go:643`) | `Lookup`, `Keys`, `TTL`, `Remaining`, `Demoted` | `ReqReaderLowerBound` (Lookup, Keys only) |
| H | **Leases**: each live id once | `v3_server.go:738` | `Leases` | `ReqLeasesList` |
| I | **Renew on the leader**: TTL, `ErrLeaseNotFound`, `ErrNotPrimary` (forward), nothing else | `v3_server.go:528`, `leasehttp/http.go:91` | `Renew`, `ckptOk` | `ReqRenew` |
| J | **Promote / Demote**: no panic, no model change | `server.go:1990` (apply thread), `server.go:769` (raft loop) | `Promote`, `Demote` | none |
| K | **Recover then mvcc Restore** | `server.go:1087-1093` | `Recover` | `ReqRecover` |
| L | **expiry channel** | `server.go:835-845,855-890` | `ExpiredLeasesC`, `expiredCh_recv`, `expiredSl` | `ReqExpiredChannel` |
| M | **NewLessor** with a real logger, the server's backend (fresh or a restart's), its cluster | `server.go:344`; `mvccrand.go:810` (`zap.NewNop()`, `noCluster{}`) | `NewLessor` | none (F5) |
| N | **SetCheckpointer** with the server's closure | `server.go:395-404` | `SetCheckpointer`, `ckptOk` | none (F1) |
| O | **Stop once, methods still answer; then close the backend** | `server.go:947`; `mvccrand.go:797-798` | `Stop`, `lessorState_bkt` | `ReqStop` |
| P | **the errors as map keys** (`togRPCError`) | `api/v3rpc/util.go:71-73` | `init` | none (minor, F8) |

Tests' `&lease.FakeLessor{}` (mvcc and server tests) are out of scope (no spec of `FakeLessor`, fine:
mvcc's specs take `lessorIface le` of a real lessor).

## What is good

- **One writer, readers on a monotone history** fits the users well: every writer call site (A-F,
  K) is on the apply thread or at bootstrap, where the token is held, and every reader (G, H, I)
  has a natural lower bound from 2d (`waitAppliedIndex`, the handler's `ApplyWaitCommit`). The
  writer's exactness through `lessorState_le` + `lessorAt_agree` serves `checkLease`, the auth
  applier and mvcc with the same reader spec: checked at `txn/put.go:83` and `apply/auth.go:199`.
- **The steps are the code's** (`attach`/`detach` over two maps, `remove` keeping the object's item
  set), which is exactly what mvcc's `putLs`/`delLs`/`RestoreLs` (3e's `Api.lean:120-140`) already
  build on. Dropping the old `Attach`/`Detach`/`Grant` premises is right: no caller needs them.
- **Grant's errors are disjuncts the caller sees**, in the code's order (id 0 before the TTL check,
  `lessor.go:282-289`), and Revoke's only premise (`ls.rd ≠ nil`) is a real one with a nonissue.
- **`rdOk` with caller-chosen `D`/`Q`** lets 3a pin the intermediate lessor states (its `D` can carry
  `ls' = delsLs ls ks`), so Revoke's post is sufficient for `State.revoke` under the attachment
  invariant. The `DeleteRange` triple lending `lessorState` matches the code: `Revoke` releases
  `le.mu` before the deletes (`lessor.go:337`), and mvcc's delete re-enters through `Detach`
  (`kvstore_txn.go:338`).
- **The expiry channel** gives 2d exactly what it asked: objects with readable `ID`
  (`server.go:888`, via `expiredSl`'s `leaseObj` and `leaseObj_id`) and `c.expiry = true` per receive.
- **Renew's error set** is what `v3_server.go:528-535` and `leasehttp/http.go:91-100` branch on.
- Snippets compile (`go vet ./specreq/lease/`: clean) and their panic guards are the callers' real
  reliances where they exist.

## First tier

### F1. `ckptOk` cannot be established for the server's checkpointer (pattern N)

- **Principle**: every premise has a source the caller sees; the pre must be establishable with
  the values the caller actually passes.
- **Evidence**: `SetCheckpointer.spec` takes `ckptOk cp`, a persistent triple for *any* call at
  *any* time (`Api.lean:282-288`). The server installs its closure in `NewServer`
  (`server.go:395`), before `start()`. The closure calls `srv.ensureLeadership()`
  (`server.go:912-937`), which, unless `isActive()` (false before the first tick), does
  `context.WithTimeout(s.ctx, ...)` and `s.read.LinearizableReadNotify(ctx)`; `s.ctx` and `s.read`
  are only set in `start()` (`server.go:572-573`). Called before `start`, the closure panics
  (`WithTimeout` of a nil parent; a nil `*read` receiver). So the server cannot prove `ckptOk` of
  its closure at `SetCheckpointer` time. The lessor in fact only calls `cp` when primary: `Renew`
  after `isPrimary()` (`lessor.go:398-433`), the run loop via `findDueScheduledCheckpoints` under
  `isPrimary()` (`lessor.go:675-680`), and primary only after `Promote` (`lessor.go:483`), which
  only the apply thread calls (`server.go:1990`), after `start`.
- **Caller affected**: 2e's `NewServer` (and through it 2c's `LeaseRenew`, which needs `Renew`'s
  error set). No other batch's spec mentions `ckptOk` or `SetCheckpointer` yet (grep of `Spec/`).
- **Fix**: gate the contract on what the lessor holds when it calls `cp`: e.g. `ckptOk cp R` with a
  persistent `R` chosen at `SetCheckpointer` (`□ (R -∗ {{ ctxOk ∗ msgAt }} cp ctx lc {{ ... }})`),
  and `Promote.spec` takes `R` (the lessor keeps it in its invariant beside `demotec`; a primary
  lessor has it). The server passes `R := srvStarted s γ id` (or whatever 2d calls it), which it
  has at `applyEntryNormal`. Add a snippet: `SetCheckpointer` with a closure that panics unless a
  started flag is set, `Promote`, then `Renew`.

### F2. Grant and Checkpoint lose the post-lock hook's effect (pattern A')

- **Principle**: the post gives what the user needs next; relaxing the old spec must not drop a
  reliance.
- **Evidence**: `Grant`/`Checkpoint` take and return an opaque `beApplyTok ls.be`
  (`lessor__Grant.lean`, `lessor__Checkpoint.lean`); `persistTo` locks with `LockInsideApply`
  (`lease.go:57-58`), which runs the backend's post-lock hook. Nothing in the post says the hook ran,
  nor lets the caller pass the hook's contract. Users that rely on it:
  - `examples/mvccrand` (a translated Goose project): after `w.le.Grant(...)` it checks
    `w.saved.Load() == i`, "the post-lock hook did not run in the write's lock"
    (`mvccrand.go:503-504`, `364-366`; hook installed at `:812-816`): a panic guard unprovable from
    `Grant.spec`.
  - 2d: the apply thread's hook (`getTxPostLockInsideApplyHook`, installed at `server.go:404`) saves
    the consistent index inside every `LockInsideApply`, so a grant's bucket record is committed
    with the index of its entry; 2d's durable-image argument (which entries the backend reflects)
    needs that, as it does for mvcc's writes.
  The old specs carried it (`specs-ref`: `lessor__Grant.lean:55`, `lessor__Checkpoint.lean:36`,
  `Lease__persistTo.lean:35`: `csContractA P f Pre Q Post`), and mvcc's new vocabulary has it for the
  same backend (`ApiStorage.lean:230` `hookRun Pk f Pre Q`, `hookIs B f`; `mvccDeleter` in
  `mvcc/Api.lean:197-210`). 3c's hand-off to 4a (`req/..._storage_backend.md`, "from 3c", item 2)
  asks for a bare token.
- **Caller affected**: mvccrand's writer, 2d (apply of `LeaseGrant`/`LeaseCheckpoint` entries), 3a.
- **Fix**: take the hook's contract as mvcc's write path does: `Grant`/`Checkpoint` (and
  `persistTo`) take `hookIs ls.be f ∗ Pre ∗ hookRun Pk f Pre Q` (or 4a's eventual equivalent) and
  return `Q` (in `Checkpoint`, `Q` only in the persisting branch, or `Pre ∨ Q` if the branch is
  hidden). Coordinate the names with 3e/4a instead of a separate `beApplyTok`. Add a snippet
  (`ReqGrantHook`: a hook that records a counter, a grant, a panic unless it ran).

### F3. Nobody owes `rdOk` for the deleter `Recover` installs (pattern B')

- **Principle**: every premise has a source; each pattern has a snippet relying on the same thing.
- **Evidence**: `applySnapshot` calls `s.lessor.Recover(newbe, func() lease.TxnDelete { return
  s.kv.Write(traceutil.TODO()) })` (`server.go:1087`); mvcc's `Restore` does not call
  `SetRangeDeleter` again (`kvstore.go:292-` has no call). From then on `ls.rd` is the *server's*
  closure, and every later `LeaseRevoke` (`apply/backend.go:95`) needs `rdOk γ ls.rd n ls P D Q` for
  it. The hand-offs say the deleter is mvcc's: 3a's `req/..._etcdserver_apply.md:78-79` ("mvcc's
  `NewStore` sets it ... mvcc's, 3e"), mvcc's `req` item 3 (only the store's own closures), and
  2d's `req/..._etcdserver.md` "from 3c" item 5 asks for `Recover`'s pre but not for the deleter's
  contract. `ReqRecover` takes `rd` and never revokes after it ("rd is the KV store's deleter":
  not what etcd passes).
- **Caller affected**: 2d (`applySnapshot`) and 3a (the first revoke after a snapshot); every
  member that ever receives a snapshot.
- **Fix**: add to the 2d hand-off: the server proves `rdOk` for its closure from `s.kv`'s
  `KV.Write.contract` (the same conversion 3e gives for its closures; ideally one law of 3e's,
  `mvccDeleter`-like, stated for any closure that calls `Write` on an `isMvcc` handle), and keeps
  "`rdOk` holds of the current `ls.rd`" in the apply thread's invariant. Fix 3a's req text. Extend
  `ReqRecover` (or a new `ReqRecoverRevoke`): Recover with a wrapping closure, re-attach, Revoke, the
  same checks as `ReqRevokeDeletes`.

## Second tier

### F4. Patterns with no snippet (J, N, and part of G)

- **Promote/Demote** (J): no snippet calls them; `Promote` is the only path by which `Renew`'s
  checkpointer call and the run loop's sends happen, and the header's "renew and the primary" is
  not a snippet. A call-only snippet (`Promote(d)` on the apply thread, `Demote()` concurrently from
  another goroutine, then `Lookup`) checks the pres (`isLessor` only) are met; with F1 it becomes the
  checkpointer snippet.
- **SetCheckpointer** (N): see F1.
- **Reader-held objects** (G): `Remaining()`, `Demoted()`, `TTL()` on an object a reader got from
  `Lookup` and that may be revoked or recovered over since (`v3_server.go:652-662`,
  `leasehttp/http.go:136-150`): only `TTL()` at the writer is covered (`ReqGrantLookup`).
  `ReqReaderLowerBound` assumes the lease is never revoked; a variant where the writer revokes
  concurrently and the reader calls `Keys`, `TTL`, `Remaining`, `Demoted` on its old object would
  cover what `checkLeaseRenew`/`leaseTimeToLive` do.

### F5. `NewLessor` has no snippet, and the header says otherwise (pattern M)

`NewLessor.lean` says "Snippet `lessor.go` (every `Req*` starts from it)", but every snippet takes
`le lease.Lessor` as a parameter; none calls `NewLessor`. The brief's "a real logger" is exactly
what is not exercised. Add `ReqNewLessor`: `lease.NewLessor(zap.NewNop(), be, cl, LessorConfig{
MinLeaseTTL: m})` over a backend whose bucket holds a lease (a restart), then `mvcc.New`-style
`SetRangeDeleter`, `Lookup` of the loaded lease with the raised TTL, `Stop`. Real call site check:
`server.go:344` passes `srv.Logger()` (2e must give `Zap.isLogger`; the zap API lists the
constructors, `SpecPlan/Spec/go_uber_org/zap/Api.lean:12-19`), `srv.be` with its bucket (2e's
`OpenBackend`), `srv.cluster` (`clusterOk`, provisional, 2e's membership): establishable given those
hand-offs. mvccrand's `noCluster{}` (`mvccrand.go:790`) meets `clusterOk` (its `Version` returns
`nil`).

### F6. Revoke's crash atomicity is not visible (uncertain; depends on 4a/4b)

Revoke deletes the bucket record under the deleter's open transaction (`lessor.go:356-359`; the
code's comment: "lease deletion needs to be in the same backend transaction with the kv deletion"),
which is why a restart never finds a key whose record names a revoked lease (`restore`'s `Attach`
would fail and only log, `kvstore.go:398-403`, leaving the key forever). The spec states the bucket
change in the token (`lessorState γ (n'+1) (ls'.remove id)`) and lends `beTxHeld` inside `D`, but
`beLeases` is "the last commit with the pending writes" (`Api.lean:253-258`), which cannot say the
two land in one commit. 2e's restart (`NewLessor` over the last commit's bucket, then mvcc's
restore) needs that agreement. Ask 4a/4b (backend `req`, "from 3c" item 4) for a crash image that
keeps writes made under one lock hold together, and say in `Revoke`'s margin that the bucket delete
is inside the deleter's transaction (it is in the sketch only).

### F7. Integration risks to record (not 3c's files)

- 3e's `NewStore.lean:13,75` still speaks the old vocabulary (`rdSlot γl rd0`, `leaseItems γl L`),
  not `lessorState`/`SetRangeDeleter.spec`; and 3e exports `mvccDeleter` (a `Write`-shaped triple),
  not `rdOk`, and no law giving `beTxHeld` out of an open write transaction (`rdOk`'s third
  conjunct). The mvcc `req` asks for it; until 3e answers, `Revoke`'s pre has no source in the
  written specs.
- `Revoke`'s and `Recover`'s `ls.be` versus mvcc's `MvccStorage` `B`: the two batches name one
  backend differently; the `rdOk` conjunct `beTxHeld ls.be` needs a law equating them.

### F8. `init.spec`'s docstring promises more than it states

The docstring says "none of rpctypes'"; the statement gives only distinctness among the four and
non-nil (`Api.lean:399-407`). 2a's `togRPCError` (`api/v3rpc/util.go:71-73`) is a map keyed by
error values from several packages; it needs the lease errors distinct from the others in the map.
Either drop the phrase or state it as the cross-package fact 2a will need (the error values are
distinct allocations: `globalAddr` of different variables).

## Real call sites checked (establishable, sufficient)

| pattern | site | pre | post |
|---|---|---|---|
| A | `apply/backend.go:84` | token (apply thread), `beApplyTok` (3a's req) | yes for the model; no for the hook (F2) |
| B | `apply/backend.go:95` | token, `ls.rd ≠ nil` (mvcc's `NewStore`), `rdOk` (3e, pending F7) | yes: `ks` exact, sorted; `Q`; `remove` |
| B' | same, after `server.go:1087` | `rdOk` for the server's closure: no source (F3) | n/a |
| C | `apply/backend.go:101` | as A | yes (both branches keep `leases`) |
| D | `txn/put.go:83` | `lessorAt γ n ls` from the token | `j = n`, exact |
| E | `kvstore_txn.go:285` | token; lease live via `checkLease` at the same `ls` | the `nil` branch; mvcc's panic excluded |
| G | `v3_server.go:592-595` | `lessorLb` from 2d's `srvApplied` | yes (any state `≥ i`; keys mid-entry: the nonissue) |
| I | `v3_server.go:528` | `lessorLb` | the three answers; `ckptOk`'s errors (F1 for its source) |
| J | `server.go:769`, `:1990` | `isLessor` | `True` suffices |
| K | `server.go:1087` | token, `beOk newbe`, `beLeases newbe B` (2e's opener) | loaded state; old bucket back |
| L | `server.go:835`, `:888` | `isLessor` | `expiredSl` with `leaseObj` (`l.ID`), `c.expiry = true` |
| M | `server.go:344` | `isLogger`, `beOk`, `beLeases`, `clusterOk`, `exp` choice (2e) | token at 0, `lessorStop`, `isLessor` |
| N | `server.go:395` | `ckptOk`: **not establishable** (F1) | — |
| O | `server.go:947` | `lessorStop` once | `True`; bucket via `lessorState_bkt` |

## Ranking (need of revision)

1. `Api.lean`'s `ckptOk` with `lessor__SetCheckpointer.lean`/`lessor__Promote.lean` (F1).
2. `lessor__Grant.lean`, `lessor__Checkpoint.lean`, `Lease__persistTo.lean` and the provisional
   `beApplyTok` (F2).
3. The `Recover`/`Revoke` hand-offs (2d's and 3a's req text) and `ReqRecover` (F3).
4. `examples/specreq/lease/lessor.go` (F4, F5) and `NewLessor.lean`'s Users line.
5. `lessor__Revoke.lean`'s margin and the backend req (F6); `init.spec`'s docstring (F8).
6. The rest (Lookup, Leases, GetLease, Attach, Detach, Keys, TTL, Renew, Demote, ExpiredLeasesC,
   Stop): no change needed for completeness.

## After reading `batch-3c.md`

The report does not mention `examples/mvccrand` (F2's evidence) or the server's closure as
`Recover`'s deleter (F3); its decision 2 discusses `ckptOk`'s error set but not when the closure may
be called (F1). Its "Left out" says the HTTP handlers have no translated caller: right for a spec of
`leasehttp`, but the handler's uses of `Renew`/`Lookup`/`Keys`/`Remaining`/`Demoted`
(`leasehttp/http.go:91-150`) are the same reader pattern G and are served by the same specs.

No Go bug found (the closure's panic before `start` is unreachable in etcd: the lessor is never
primary then).

## Verdict

Not complete yet: three first-tier findings. F1 (the checkpointer's contract is unprovable for the
server's closure) and F2 (Grant/Checkpoint drop the post-lock hook's effect that mvccrand and 2d
rely on) need spec changes; F3 is a hand-off and snippet gap (a revocation after a snapshot uses a
deleter nobody owes a contract for). The rest of the API covers its users well; a second round
after the repairs.
