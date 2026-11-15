# Batch 3c: etcd's lessor (report)

Author agent, 2026-11-09. Everything builds (`etc/specs-build.sh --dir
SpecPlan/Spec/go_etcd_io/etcd/server/v3/lease`: OK, 46 modules); snippets: `cd examples && go vet
./specreq/lease/` clean, `gofmt -l` clean.

## Files

`SpecPlan/Spec/go_etcd_io/etcd/server/v3/lease/` (namespace `Lease`):
- `Api.lean`: the vocabulary (below). `Internal.lean`: the internal helpers' vocabulary (no client
  imports it).
- The API (full care): `NewLessor`, `lessor__{Grant, Revoke, Checkpoint, Lookup, Leases, GetLease,
  Attach, Detach, SetRangeDeleter, SetCheckpointer, Renew, Promote, Demote, ExpiredLeasesC,
  Recover, Stop}`, `Lease__{Keys, TTL, Remaining, Demoted}`.
- Internal helpers (mirroring the code, two-line comments): `NewLease`, `Lease__{persistTo,
  getRemainingTTL, refresh, forever}`, `leasesByExpiry__{Len, Less, Swap}`, `LeaseQueue__{Len, Less,
  Swap, Push}`, `LeaseExpiredNotifier__{Init, RegisterOrUpdate}`, `newLeaseExpiredNotifier`,
  `greaterOrEqual`, `lessor__{isPrimary, unsafeLeases, shouldPersistCheckpoints,
  scheduleCheckpointIfNeeded, initAndRecover, clearScheduledLeasesCheckpoints,
  clearLeaseExpiredNotifier}`.

Names-only (assumed) among them: `NewLessor`, `Renew`, `Promote`, `Stop`, `SetCheckpointer`,
`scheduleCheckpointIfNeeded`, `Lease.Demoted` (time, floats, the run loop); each comment says why
it is true of the code.

Snippets: `examples/specreq/lease/lessor.go`: `ReqGrantLookup`, `ReqAttachDetach`,
`ReqRevokeDeletes` (with a range deleter in mvcc's shape), `ReqLeasesList`, `ReqReaderLowerBound`,
`ReqRenew`, `ReqCheckpointNoop`, `ReqRecover`, `ReqExpiredChannel`, `ReqStop`.

New non-issue: `nonissues/etcd-lease-keys-mid-apply.md` (`blocks-proof: yes`; `nonissues/INDEX.md`
needs `etc/issues-status.py --index`, not run: outside my paths).

## Exported vocabulary (`Api.lean`)

Model (transparent):
- `Cfg` (`minTTL`, `expiry`), `grantTTL c ttl = max ttl c.minTTL`.
- `LeaseEnt` (`obj : Loc`, `ttl`); `LessorState` (`leases : Int → Option LeaseEnt` = `leaseMap`;
  `items : Key → Int` = `itemMap`; `keys : Loc → Key → Prop`, every object's item set, live or not;
  `bkt : Int → Option Int`, the lease bucket; `be`; `rd`); `LessorState.table` (to W0's lease
  table); the steps `grant`, `attach`, `detach`, `persist`, `remove`, `loaded`.
- `leasesOutliveRun : Prop` (opaque): the trusted deployment premise about time (W0's
  `EnvCfg.leaseExpiry = false`).

Resources:
- `isLessor le γ c` (persistent): the lessor, its lock, logger (`Zap.isLogger`), cluster,
  checkpointer, expiry channel, run loop.
- `lessorState γ n ls` (exclusive, timeless): the writer's token: the state is `ls`, the `n`-th of the
  lessor's history (holds the lease bucket).
- `lessorAt γ n ls` (persistent): the history; `lessorLb γ n` (transparent: `∃ ls, lessorAt γ n ls`).
- `leaseObj γ l id ttl` (persistent): a `*Lease` of this lessor.
- `lessorStop le` (exclusive), `expiredCh γ c ch` (persistent), `lessorIface le` (transparent),
  `errIs g e` (transparent).
- Callback contracts (transparent): `ckptOk cp` (the checkpointer: `nil` or `ErrNotPrimary`),
  `rdOk γ rd n ls P D Q` (the range deleter, for one revocation), `expiredSl γ sl ids` (an expiry
  receive's payload, persistent).
- Provisional (other batches'): `beOk be`, `beApplyTok be`, `beTxHeld be` (4a), `beLeases be B`
  (4b), `clusterOk cl` (2e's membership).

Laws: `persistent`, `timeless`, `exclusive`; `lessorState_at` (snapshot), `lessorAt_agree`,
`lessorState_le` (the current state is the last), `lessorAt_obj` (a live lease's object),
`leaseObj_id` (`ID ↦□`, int64 ranges), `leaseObj_live`, `leaseObj_agree`, `lessorState_bkt` (lend the
bucket), `expiredCh_recv` (gated by `c.expiry`), `init` (the four errors distinct, non-nil).

## The design, and the main changes from the old specs

- **One writer, readers on a history.** All of the lessor's state changes happen on the apply thread
  (grant, revoke, checkpoint, mvcc's attach/detach, recover, the deleter): they take the writer's
  token `lessorState` and are plain (non-atomic) specs, exact on the model. Readers on any
  goroutine (`Lookup`, `Leases`, `GetLease`, `Keys`, `Renew`) take a lower bound `lessorLb γ i` and
  answer from a state `j ≥ i` of the lessor's persistent history (`lessorAt`), which they return. A
  writer passing its own state gets that state exactly (`lessorState_le`, `lessorAt_agree`): one
  spec per reader. Why not TaDa updates over a client-owned state: `Revoke` is several steps, with the
  range deleter calling back into the lessor (mvcc's delete detaches) between them; and the readers
  need only "at or after the member's applied point", which a monotone history gives with no
  update to build.
- **Over the lessor's own state** (`LessorState`), replacing the old owner's live list `L`, item
  map `I`, `leaseRevokers`, the grant guard (`leaseGranted`, `GA`), `leaseEver`, `leaseLiveFrom`,
  `leaseReqIs`, the monotone mode, `lessorCfg`/`lessorInv` and mvcc's `rdIs`/`rdOwn`.
- **Premises dropped**: `Grant`'s grant guard and "new id unless monotone" (the code accepts any id);
  `Attach`'s "items on no other lease" and `Detach`'s "items on this lease" (the model says what the
  code does with them: two maps); `NewLessor`'s empty lease bucket and tracked-bucket shapes (a
  restart's bucket loads), `ckptEffectsOk` (now the checkpointer's contract at `SetCheckpointer`).
- **Premises kept or added, with their reasons**: `Revoke` needs `ls.rd ≠ func.nil` (a second revoke
  without a deleter panics: `nonissues/etcd-lease-revoke-twice-no-range-deleter.md`); `NewLessor`
  needs `Zap.isLogger lg` (the zero logger panics: `specs-ref`'s axiom sweep B3-2, the fix it
  proposed, now in the statement); `Stop` needs `lessorStop` (twice panics); the expiry mode
  `false` needs `leasesOutliveRun`.
- **The range deleter** is a callback contract in the lessor's terms (`rdOk`), which mvcc proves
  for its `s.Write` closure and the applier passes to `Revoke`; the lessor no longer says what the
  deletes do to the store.
- **The backend** through four provisional names (4a/4b): the bucket's image `beLeases be B`
  (id to TTL), the apply-side lock right `beApplyTok`, the held lock `beTxHeld`, `beOk`.
- **No time model.** Expiry, remaining TTL, checkpoints, the primary flag are not modelled:
  `Remaining()`/`Demoted()` return any value; `Renew` may answer `ErrNotPrimary` any time;
  `Checkpoint` changes at most the bucket's TTL of a recovered lease; `Promote`/`Demote` change
  nothing. **No caller needs one**: W0's `TimeToLive` and keep-alive allow any TTL.
- **The expiry channel** delivers objects of leases the lessor had (`expiredSl`, persistent), only
  with the expiry mode on; replaces 2d's provisional `expiredLeases`.

## Left out (no old spec, no translated caller, or nothing to state)

`newLessor` (covered by `NewLessor`), `lessor.runLoop`, `lessor.revokeExpiredLeases`,
`checkpointScheduledLeases`, `expireExists`, `findExpiredLeases`, `findDueScheduledCheckpoints`
(untranslated; their behavior is `NewLessor`'s and `expiredCh_recv`'s assumed part), `Lease.expired`,
`Lease.SetLeaseItem` (no caller in etcd), `LeaseQueue.Pop`, `LeaseExpiredNotifier.{Unregister, Peek,
Len}` (callers untranslated), `FakeLessor.*`, `FakeTxnDelete.*` (tests), the metrics.
**`lease/leasehttp`**: batch 2e already wrote `SpecPlan/Spec/.../lease/leasehttp/{Api,RenewHTTP}.lean`
(names-only); I left them as they are (2e's files). `TimeToLiveHTTP` and the HTTP handlers have no
translated caller (2c's `leaseTimeToLive` is untranslated), so no spec.

## Decisions for the user

1. **`LeaseTimeToLive`'s keys are not linearizable in etcd** (`nonissues/etcd-lease-keys-mid-apply.md`):
   on the leader, the key set is read while the apply thread may be between two detaches of a
   revocation (or two attaches of a transaction's puts), so the answer can be a set no revision had
   (`{b}` while revoking a lease holding `a`, `b`). W0's step says "exactly the keys at some
   revision": false. Options: weaken W0's step to "between the attachments of two consecutive
   revisions" (asked in `req/go_etcd_io_etcd_api_v3.md`, "from 3c"), or a premise on 2c's spec, or
   a fork fix. My spec of `Keys` states what the code does.
2. **The checkpointer's contract restricts its errors** (`ckptOk`: `nil` or `ErrNotPrimary`), which
   the code does not need, so that `Renew`'s errors are exactly `ErrLeaseNotFound`/`ErrNotPrimary`
   (2c's need). The server's closure meets it. The alternative is `Renew` returning "any error" in
   one more disjunct.
3. **The range deleter's contract** (`rdOk`) carries the caller's predicates `P`, `D`, `Q` (a
   callback's contract, a spec-level parameter, not a library predicate's parameter): a departure
   from "TaDa, not HoCAP" in letter if not in spirit; the alternative is to state `Revoke` over
   mvcc's vocabulary (coupling to 3e).
4. **Readers' history (`lessorAt`) is a new abstraction** beside the writer's token; the server (2d)
   must record which lessor state each applied entry ends at (`req/..._etcdserver.md`, "from 3c",
   item 4).

## Open questions

- Perennial's `sort` specs: `Revoke` sorts the keys (a size bound of Perennial's sort spec would
  come from the map's size); `Leases`' `sort.Sort` uses a time-dependent `Less` (inconsistent order:
  Go's sort stays in bounds; Perennial's spec may want a consistent order). Proof matters, no
  premise stated.
- 4a's design will say whether `beApplyTok`/`beTxHeld` are one token or two, and whether the bucket
  ownership lives in the lessor (as here) or in the batch transaction's lock invariant.

## `req/` sections written (`## from 3c`)

`go_etcd_io_etcd_server_v3_storage_mvcc.md` (thread the writer's token; the attachment invariant;
the deleter's `rdOk`), `..._storage_backend.md` (`beOk`, `beApplyTok`, `beTxHeld`),
`..._storage_schema.md` (`beLeases`, the lease bucket's functions; `semver`),
`..._etcdserver_api_membership.md` (`clusterOk`), `..._etcdserver_apply.md` (grant, revoke,
checkpoint, `checkLeasePuts`), `..._etcdserver_txn.md` (`checkLease`), `..._etcdserver.md` (2c's
reads and the mid-entry keys; 2d's expiry channel, the history tie, `Recover`; 2e's `NewLessor`,
`leaseBootRes`, `SetCheckpointer`, `Cleanup`, leasehttp), `go_etcd_io_etcd_api_v3.md` (W0: the
keys, no time model, per-member TTL).

## Round 1 repairs (2026-11-09)

Reviews: `reviews/3c-provability-1.md`, `reviews/3c-completeness-1.md`. Rebuilt: `etc/specs-build.sh
--dir SpecPlan/Spec/sort SpecPlan/Spec/go_etcd_io/etcd/server/v3/lease` OK (48 modules); mvcc's and txn's `Api.lean`
(importers of `lease/Api.lean`) OK; `go vet ./specreq/lease/`, `gofmt -l` clean.

First tier:
- **P1** (`rdOk` admitted a nested `Revoke`/`Recover`): `rdOk`'s `DeleteRange` post keeps `leases`,
  `bkt`, `be`, `rd` (only `items`/`keys` move; mvcc's `delsLs` meets it); `Revoke`'s sketch takes the
  `revokec` close right at the second lock; `End` "may only block".
- **P2** (`SetCheckpointer` twice or `nil` races/panics): a once token `lessorCkptTok le` from
  `NewLessor`; new `nonissues/etcd-lease-setcheckpointer-once.md`.
- **P3**: `NewLessor` premise `0 ≤ sint.Z cfg.leaseRevokeRate'`.
- **C-F1** (the server's closure panics before `start`): `ckptOk cp R` gated on `R`;
  `SetCheckpointer` gives `ckptGate le R`; `Promote` takes `ckptGate le R ∗ □ R` (server: `R :=
  srvStarted`); `lessorCkptTok_gate` for no checkpointer.
- **C-F2** (the post-lock hook's effect): `beApplyTok` replaced by `beHook be Pk f` (provisional, 4a's)
  with mvcc's `Mvcc.hookRun Pk f Pre Q` and `(Q ={⊤}=∗ Pk ∗ Post)` on `Grant`, `Checkpoint`,
  `persistTo` (`Pre` back when the lock is not taken); snippet `ReqGrantHook`. `lease/Api.lean` now
  imports `storage/mvcc/ApiStorage.lean` (no cycle: it does not import the lessor).
- **C-F3** (who owes `rdOk` after `Recover`): 2d, for the server's closure
  (`req/..._etcdserver.md`, "from 3c (round 1)", item 1; 3a's and mvcc's req corrected); snippet
  `ReqRecoverRevoke`.

Second tier:
- Sort specs restored as trust-boundary specs, `SpecPlan/Spec/sort/SortAnyLess.lean` (`GoSort.sorterAny`,
  `GoSort.Sort.anyLessSpec`: any `Less`, a permutation, no order) and
  `SpecPlan/Spec/sort/StringSlice__Sort.lean`; cited by `Leases`, `Revoke`. Their `2^62` bound: open (below).
- Law `lessorAt_minTTL` (every state's TTLs `≥ c.minTTL`), for `0 < GrantedTTL` with 2e's
  `0 < c.minTTL`.
- Realization header: the bucket and one reader token in the writer's token (not the lock); the
  notifier owned by the write-lock holder or the run loop's reader section; `le.cp` frozen once set.
- Restore window: `Demoted` left without content (a primary lessor's `Renew` refreshes a loaded
  object during `Restore`, so content would not close it); the window added to
  `nonissues/etcd-lease-keys-mid-apply.md` and asked of W0.
- Snippets: `Assumes` (distinct ids; no `Recover` meanwhile; reader tokens); new `ReqNewLessor`
  (`zap.NewNop()`), `ReqPromoteCheckpointer` (SetCheckpointer once, `Promote`, concurrent `Demote`,
  `Renew`), `ReqGrantHook`, `ReqRecoverRevoke`.
- `leasesOutliveRun`'s docstring: what the run loop tests. `init`'s docstring no longer claims
  distinctness from rpctypes'.
- **Reader tokens** (the 2026-11-07 decision, as mvcc's): `lessorReaders γ n` (counted, splits),
  `lessorTokN` (sealed) from `NewLessor`; `Lookup`, `Leases`, `GetLease`, `Renew`, `Keys`,
  `Remaining`, `Demoted` take one and give it back; the writer borrows one (`lessorState_reader`).

New vocabulary: `lessorReaders`, `lessorTokN`, `lessorCkptTok`, `ckptGate`, `beHook` (replacing
`beApplyTok`); laws `lessorAt_minTTL`, `lessorState_reader`, `lessorReaders_split`,
`lessorCkptTok_gate`; `LessorState.persist` (round 0's late fix: `Checkpoint` may rewrite a recovered
lease's raised TTL into the bucket).

Open after round 1: the `2^62` bound of Perennial's sort at `Revoke` and `Leases` (a Go slice of
pointers or strings cannot exceed it in a 64-bit address space, but Perennial's slice model does not
say so; no premise added); 4a's identification of `beHook`/`beTxHeld` with mvcc's
`mvccBackend`/`hookIs`/`kbHeld`; `nonissues/INDEX.md` needs regenerating.
