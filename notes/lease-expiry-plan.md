# Lease expiry (2026-11-03; branch `lease-expiry`)

The stage after `notes/lease-grant-plan.md`: drop the deployment premise `lease.leasesNoExpiry`, so
that a server that grants leases also expires them, and convert the lease subsystem to hub slots
(`notes/spec-first-plan.md`, "Hubs", "Incremental adoption" step 4). `notes/leases-plan.md`'s L5
(Q1 (a), "last"). Lean-first.

## Scope

### What Go does (the pin, `249d76bea7`)

- The lessor's `runLoop` (`server/lease/lessor.go:620`, not translated; `NewLessor` an axiom) every
  500 ms: `revokeExpiredLeases` (`:640`) sends a non-empty slice of the primary lessor's expired
  leases on `expiredC` (at most `leaseRevokeRate/2`; a non-blocking send, dropped when the receiver is
  busy), and `checkpointScheduledLeases` proposes checkpoints through the checkpointer.
- `EtcdServer.run` (`server/etcdserver/server.go:848`): `case leases := <-expiredLeaseC:
  s.revokeExpiredLeases(leases)`.
- `EtcdServer.revokeExpiredLeases` (`:860`, translated, no spec): `GoAttach` of a goroutine that
  returns unless `ensureLeadership()` (an axiom), then for each lease takes a slot of a
  `maxPendingRevokes` channel (or returns on `s.stopping`) and `GoAttach`es
  `s.LeaseRevoke(s.authStore.WithRoot(s.ctx), &LeaseRevokeRequest{ID: lid})`, logging an error.
- `EtcdServer.LeaseRevoke` (`v3_server.go`, translated, no spec): `raftRequestOnce` of the
  revocation, the response's type assertion.

### What the proof has (`lean` `8366afa266`)

- **The premise.** `lease.leasesNoExpiry` (opaque, `LessorBackend.lean`), in `%Hslg : ρ.rd.kv.lg =
  true → leasesNoExpiry ∧ runSnapLgOk` (`NewServer`, `isServerRun`), a hypothesis of
  `etcd_leasegrant_safe`. `NewLessor`'s `lessorExpiredC` gives a slice on `expiredC` `⌜¬
  leasesNoExpiry⌝ ∗ ∃ id, GA id`; `lessorOk`'s `ExpiredLeasesC` payload is `False`
  (`InvApplier.lean`, `srvGrantGuard lg on := ⌜leasesNoExpiry ∧ lg ∧ on = false⌝`); `run`'s expiry
  arm is dead (`srvGrantGuard_expired`).
- **The apply side of a revocation is done** (`notes/lease-revoke-plan.md`, frozen and proved):
  `chain_revoke` (`apply/Results.lean`), `backendStep .leaseRevoke` (`revokeLog`: the lease's keys
  deleted), `isApplyLessor`'s `revokeClause` of the real `lessor.Revoke`, `reqLeaseClass`.
- **The server's workload excludes it.** `rqOk lg log rq` is `False` at `.leaseRevoke` (and
  `.leaseCheckpoint`) whatever `lg` (`apply/Chain.lean:282`); `plainCover` admits no revocation and
  no leased put (`KVModelDefs.lean:72`: `op.leaseID = 0`); `kvInv`'s `plainLogM γk.cmp γk.lg` has
  grants, no revocations. The KV model has `KVOp.leaseRevoke` (unit T3) but the table is not tied to
  the lessor (lease-grant's S1 (a), narrow).
- **The read side.** `leaseTTLOut`'s not-found arm (`TTL = -1`, `InvLeaseRead.lean:153`) states no
  fact of the lessor's history; `leaseLeasesOut` gives `leaseIdsAt γl i ids` at `i ≥ m`; the
  lessor's history (`lessorRdInv`) is a monotone list of snapshots, a revocation one more.
- **Hubs** (lease-grant's "Hubs touched"): `%Hslg`, `on = true → lg = false` and `KVNames.lg`/
  `AEnv.lg` inline in `NewServer.specG`, `bootOk`, `isServerRun`; per the hub plan's step 4 they
  become `lease.Names`/`lease.bootCfg`/`lease.srvInv` here.

### What admitting expiry breaks (lease-grant's rule: every place that rules the case out)

1. `lessorOk`'s `ExpiredLeasesC` payload `False` and `run`'s dead arm: the arm becomes live, and
   `revokeExpiredLeases`, `LeaseRevoke` need specs (and `GoAttach`'s wait group, the
   `maxPendingRevokes` channel, `s.stopping`, `ensureLeadership`, `WithRoot`).
2. `rqOk .leaseRevoke = False`, `plainCover`, `reqPropOkW`, `kvInv`'s `plainLogM`: a revocation
   proposed by the server itself (no client asked) must be admitted into the request path and the
   KV invariant; a revocation's KV step (`revokeLog`) with no leased keys deletes nothing.
3. The monotone "granted, still live" reading of `lessorGrantOkG`'s `G` and of the listing: a lease
   granted at `i` may be gone at `j > i`. `leasegrant`'s `Main` (panics unless `Leases` lists the
   grant) is then **not provable** without a timing premise: its check is the premise's.
4. `srvGrantOpen` (sorry `srvGrantOpen_open`, the snapshot's `Recover`): unaffected in statement
   (a snapshot's lessor may now have fewer leases), to recheck in Draft.
5. The checkpoints (`ckptEffectsOk`, opaque) are unchanged: expiry adds none.

## Scope questions (for the user)

- **Q1. What the result says.**
  (a) *Server-side expiry, a new expiry-robust example* (recommended): the server admits its own
  revocations (items 1-2; leased puts stay out, so a revocation deletes no key); `leasesNoExpiry`
  leaves the server's statements; a new example `etcd/leaseexpiry` grants a short lease (the minimum
  TTL), polls `TimeToLive` until it answers not found, then panics if `Leases` still lists it. Not
  found is `TTL = -1 ∧ GrantedTTL = 0`: `TTL = -1` alone is also the answer for a lease still in the
  lessor but overdue by a second or more (`int64(le.Remaining().Seconds())`, `v3_server.go:650`;
  `Remaining` goes negative), which `Leases` still lists, so a check on `TTL` alone is false. That
  needs `leaseTTLOut`'s not-found arm to state the lease's absence at an index (a restated
  trust-boundary `leaseTimeToLive`, for Freeze) and "no other grant of that id" (the example grants
  once). `leasegrant` keeps its check under `leasesNoExpiry`, now a premise of that example only.
  (b) *Full L5*: also leased puts and the KV table tied to the lessor (L3b), the example puts a key
  with the lease and checks it is gone after expiry. Several stages' worth; (a) is its first half.
  (c) *Server only*: (a) without the new example; `leasegrant` as in (a).
- **Q2. The hub conversion.** Convert lease to slots first (`lease.Names` from `KVNames.lg` and the
  lessor's names, `lease.bootCfg`, `lease.srvInv` holding `%Hslg`'s remainder), as its own
  mechanical commits before the expiry change, so the expiry change lands inside the sealed bodies
  (recommended); or the expiry change inline and the conversion after.
**Decided (the user, 2026-11-03):** Q1 (a), the server's expiry and the example `etcd/leaseexpiry`;
Q2, convert first. **Snapshots in scope** (the user, 2026-11-03, after the design's first draft):
restoring a snapshot in a lease-granting cluster is proved here (Part S), closing `srvGrantOpen_open`.

- **Q3. Auth.** Off, as lease-grant (`on = true → lg = false`): `WithRoot`'s context then carries no
  token that matters.

## Draft: the design (2026-11-03, before any site is threaded)

Per `notes/spec-first-plan.md`'s "Design before plumbing": each changed statement old → new, and
what it is proved from. Review checks this text before plumbing.

### Part C: the lease subsystem into hub slots (no statement stronger or weaker)

The lease clauses inline in the hub today:

| where | clause |
|---|---|
| `NewServer.specG`, premise | `(on = true → ρ.rd.kv.lg = false)` (auth/lease coupling, lease-grant 2.13) |
| `NewServer.specG`, pre | `"%Hslg" ∷ ⌜ρ.rd.kv.lg = true → lease.leasesNoExpiry ∧ srvGrantOpen⌝` |
| `NewServer.specG`, pre | `"%Hckok" ∷ ⌜ckptEffectsOk⌝` (the lessor's checkpointer; `NewLessor`'s premise) |
| `NewServer.specG`, post | `□ (⌜on = true⌝ → srvLessorNil srv)`, `srvPeerRt srv ∗ srvLessorRd srv E.γ.leases`, `lease.lessorRdPool E.γ.leases` |
| `bootOk`/`isServerRun` (`InvBuild.lean:323`) | `%Hslg` again |

- **C1. `etcdserver/LeaseApi.lean`** (as `WalApi.lean`, `RaftNodeApi.lean`; on the importable list),
  sealed (`@[no_expose]`):
  - `lease.bootCfg (lg on : Bool) : Prop := (on = true → lg = false) ∧ (lg = true →
    lease.leasesNoExpiry ∧ srvGrantOpen) ∧ ckptEffectsOk` (the three premises above). Laws:
    `lease.bootCfg_off : lg = false → ckptEffectsOk → lease.bootCfg lg on` (every non-granting
    example), `lease.bootCfg_of` (leasegrant's), and the narrow eliminations the server's proof uses
    (`_auth : bootCfg lg true → lg = false`, `_ckpt`, `_open : bootCfg true on → srvGrantOpen`,
    `_noExpiry`).
  - `lease.srvInv (on : Bool) (s : Loc) (γl : GName) : IProp := □ (⌜on = true⌝ → srvLessorNil s) ∗
    srvPeerRt s ∗ srvLessorRd s γl ∗ lease.lessorRdPool γl`, with eliminations into what its
    consumers take (`StartOn`'s `srvLessorNil`; v3rpc's `srvPeerRt`/`srvLessorRd`/pool for the lease
    service; `LeaseSrc`).
  - `bootOk`'s and `isServerRun`'s `%Hslg` become `lease.bootCfg γr.kv.lg on` (or its needed half).
- **C2. Names: deferred.** `lg` stays `KVNames.lg`/`AEnv.lg` and the lessor's name `E.γ.leases`
  (`ApplyNames`): the slots take them as arguments, as `rafthttp.bootCfg dir` takes a field before
  its subsystem has a `Names` (the convention's "Follow-up"). Why: `lg` is a mode the KV invariant
  reads (`plainLogM γk.cmp γk.lg`, about 190 sites); a `lease.Names` sub-record renames them all
  and moves no hub text. Converted when lease next adds a name. (A deviation from step 4's "the
  name records a field group at a time with their subsystem": for review.)
- **C3. Callers**: `examples/lib/etcdstart`'s `newServerMode`/`startServer`, authkv's, leasegrant's
  `Alloc`/`Defs`, the server's `Results`/`Link`, v3rpc's consumers of the post: each passes or uses
  the slot through its laws.

After C, the expiry change below edits `lease.bootCfg`'s and `lease.srvInv`'s bodies, the lessor's
contracts and the request path, not `NewServer.specG`'s text.

### Part X: expiry in the server

- **X1. The grant guard** (`InvApplier.lean:490`): `srvGrantGuard lg on := ⌜leasesNoExpiry ∧ lg ∧ on =
  false⌝` → `⌜lg ∧ on = false⌝`. `srvGrantGuard_expired` goes.
- **X2. The lessor's mode** (`NewLessor`'s `mono`, from `γk.lg` today). A granting cluster's lessor is
  now revocable unless no lease expires. Proposed: `mono := lg && decide leasesNoExpiry`
  (classical). Under the premise (leasegrant), the lessor stays monotone and leasegrant's proof is
  unchanged; without it, the lessor is revocable (`Revoke` applies, and `Recover`'s
  `lessorRevocable` holds: to recheck whether that closes part of `srvGrantOpen`).
- **X3. `expiredC`'s payload** (the trusted `lessorExpiredC`, `NewLessor`'s post): today `⌜¬
  leasesNoExpiry⌝ ∗ ∃ id, GA id` per slice, which says nothing of the slice's elements;
  `revokeExpiredLeases` reads each element's `ID` (`curLease.ID`). Restated: a slice `ls` of
  non-null `*Lease` with `ID` readable (`↦□`), each `GA id`, and `⌜¬ leasesNoExpiry⌝`. A trusted
  restatement: the `axiom` skill before Freeze.
- **X4. `lessorOk`'s `ExpiredLeasesC`** (`InvApplier.lean`): payload `False` → X3's payload.
- **X5. `EtcdServer.revokeExpiredLeases.spec`** (new, proved): from `isServerRun`'s facts (the wait
  group's `srvGoRes`, `ensureLeadership`'s contract, the auth store's `WithRoot`, `s.stopping`,
  `LeaseRevoke`'s pre) and X3's slice, returns. `run`'s expiry arm calls it (was dead).
- **X6. `EtcdServer.LeaseRevoke.spec`** (new, proved): `raftRequestOnce` of `LeaseRevokeRequest{ID}`
  with the server's own revocation update (below), the response's assertion; post: an error or the
  revocation applied at some index (`chain_revoke`'s outcome).
- **X7. The workload admits the server's revocations.** `rqOk lg` at `.leaseRevoke`: `False` → `lg =
  true ∧ ¬ leasesNoExpiry` (a revocation exists only when a lease expired); `reqPropOkW`/the grant
  disjunct's sibling for a revocation; `kvInv`'s `plainLogM γk.cmp γk.lg` admits a revocation entry
  whose KV step is the identity: with no leased put (`plainCover`'s `op.leaseID = 0`) no key is
  attached, so `revokeLog log id = log` (a lemma from the plain log's lease-free keys; a revocation
  with no items commits no revision, `storeTxnWrite.End`). The client-visible model: a revocation
  is no KV step (`KVOp.leaseRevoke` stays out of the clients' histories).
- **X8. Leasegrant.** Its `Main.spec` keeps `leasesNoExpiry` (its check is the premise's); under it
  X2 keeps the lessor monotone and X7 refutes every revocation, so its proof changes only where the
  slot conversion and X1 touch it.

### Part E: the example `etcd/leaseexpiry`

- **E1. Go.** `Main` starts one member, serves it, connects; `cli.Grant(ctx, minTTL)`; polls
  `cli.TimeToLive(ctx, id)` (bounded, sleeping between) until `TTL = -1 ∧ GrantedTTL = 0`; then
  `cli.Leases(ctx)`, panics if `id` is listed. A Go test runs it (the expiry takes a few seconds).
- **E2. The not-found answer's fact.** `leaseTTLOut`'s `TTL = -1` arm, down to the trusted
  `EtcdServer.leaseTimeToLive`: today no fact; restated `GrantedTTL = 0 → lease.leaseAbsentAt γl i
  id` at some `i ≥ m` (the lessor's history at `i` has no `id`). True of Go on the local path (the
  lessor's `Lookup` returned nil); on the forwarded path (`leasehttp.TimeToLiveHTTP` at the leader)
  only if the leader's lessor history is the same as this member's, which a one-member cluster
  makes trivial. A trusted restatement (`axiom` skill).
- **E3. Absent stays absent.** The listing at `j ≥ i` must not contain `id`: needs that `id` is not
  granted again after its revocation. Go allows it (a client may grant an explicit `ID` once the old
  lease is gone; the server's own ids are unique, `reqIDGen`). Options for review: (a) the example's
  workload, by a ghost "grant once" token per id handed out by the KV model's grant record
  (`restGrantT`'s ids); (b) a weaker check (`TimeToLive` twice). Recommended: (a).

### Open design points (for Review)

- **P1. Thread tokens for the expiry goroutines.** `revokeExpiredLeases` `GoAttach`es one goroutine
  per round and one per lease, and `run` loops forever: each needs a `threadTok`
  (`InvGoAttach.lean`: `srvGoRes`), returned only to the wait group. Where `run` gets a token per
  round, and how they come back, must follow `notes/bounds-plan.md` (a pool in `run`'s resources,
  the `maxPendingRevokes` channel as the inner pool's bound); no token out of nothing (lease-ex's D1).
- **P2. Who may propose a revocation.** X7's `¬ leasesNoExpiry` makes a client's `LeaseRevoke`
  provable only under that premise too; client revocations are outside Scope, so
  `LeaseRevoke.spec` takes it as a premise (the server's expiry path has it from X3).
- **P3. `srvGrantOpen`.** Now Part S.

### Part S: snapshots in a lease-granting cluster (in scope, the user's, 2026-11-03)

Today a granting cluster's snapshot job is the open premise `srvGrantOpen` (`runSnapLgOkBody`,
`InvRun.lean:446`; `sorry srvGrantOpen_open`, reached by `etcd_leasegrant_safe` only). It is open for
three reasons: the lessor is monotone there and `Recover` takes a revocable one; `Recover`'s trusted
spec takes an empty lease bucket (`⌜(r.lookup "lease").getD ∅ = ∅⌝`) and gives an empty lessor;
and the snapshot path's image fact `hlease` (`SnapRecvOn.lean:296`, `image_leaseAlarmNA`) says the
image's lease bucket is empty, false once a grant is applied. A snapshot is received only in a
multi-member cluster (a lagging follower, `raft.go`'s `maybeSendSnapshot`), but `run`'s proof is
generic over clusters, so the case is not vacuous.

What Go does: `lessor.Recover(b, rd)` (`lessor.go:600`) under `le.mu` stores `b` and `rd`, fresh
`leaseMap`/`itemMap`, and `initAndRecover` (`:808`) reads every record of the new backend's `lease`
bucket (`schema.MustUnsafeGetAllLeases`) into the map: TTL raised to the minimum, expiry forever
(refreshed at `Promote`), empty item sets (mvcc's restore re-attaches the leased keys: none here,
no leased put), then `ForceCommit`.

- **S1. `lease.lessor.Recover`: translate and prove, or restate.** (a) *Translate and prove*
  (recommended): `Recover` and `initAndRecover` get bodies (the lease package's configuration),
  proved over the trust-boundary specs of `schema.UnsafeCreateLeaseBucket`/`MustUnsafeGetAllLeases`
  (the latter read-only over the bucket's records) and the backend's `ForceCommit`; the axiom
  leaves the trust base, and the audit's open frame finding (`le.rd` not returned, `notes/audit.md`)
  is fixed by the proof's statement (`rdOwn γl rd0` in, `rdOwn γl rd` out). (b) *Restate the
  axiom*: a non-empty bucket, the post's `leaseOwn γl L' ∅` with `L'` the bucket's ids, and the
  frame fix; the `axiom` skill before Freeze. The new spec, either way: the history gets the
  snapshot `(L' ↦ leases, ∅)`; in the monotone mode only if every live lease is in `L'` (premise
  `⌜L ⊆ L'⌝`), else `lessorRevocable`.
  **Decided (the user, 2026-11-03): (a), translate and prove `Recover`.**
  What it takes (survey, 2026-11-03): bodies for `lessor.Recover`, `lessor.initAndRecover` and
  `LeaseExpiredNotifier.Init` (`lease_queue.go:75`); callees `BatchTx`, `LockOutsideApply`/`Unlock`,
  `ForceCommit` (the backend's specs), `schema.UnsafeCreateLeaseBucket` (`UnsafeCreateBucket`),
  `heap.Init` (Perennial's `Spec/container/heap/Init_`), and `schema.MustUnsafeGetAllLeases`, a
  trust-boundary axiom like `MustUnsafePutLease` (its body is `UnsafeForEach` and `proto.Unmarshal`,
  and it **panics on a record that does not unmarshal**: its spec takes the bucket's records to be
  `MustUnsafePutLease`'s encodings, which the rest model's lease bucket must then say). Two things
  the proof must face: (i) `LeaseExpiredNotifier.Init` does **not** empty the queue (`heap.Init` of
  the old queue, then `m` rebuilt from it), so after `Recover` the expiry notifier still holds the
  old leases' entries (Go's `findExpiredLeases` drops an entry whose lease is not in `leaseMap`):
  the lessor model's notifier invariant (`notifierAt`) must admit stale entries; (ii) each recovered
  lease is a new `Lease` object, so `isLeaseObj` (its lock, the reader-slot pool, the expiry halves)
  is allocated per record.
- **S2. The mode question, settled by S1.** With S1's monotone case, the monotone lessor (X2:
  `mono := lg && leasesNoExpiry`) can be restored too: under `leasesNoExpiry` no revocation is ever
  applied (X7), so a snapshot at index `j` above the member's applied index has every lease the
  member has. That fact comes from the image (S3).
- **S3. The image's lease bucket.** `hlease` (empty) → the image's `lease` bucket is the lease
  records of the log up to the snapshot's index (the grants' records minus the revoked ones:
  `bkRestAtL`'s lease ids, lease-grant's `appliedTable`/`grantRest`, `revokeLog`'s `restRevoke`), in
  `specSnap`/`specSnapM` and the walk (`SnapApplyWalk.lean`, `SnapRecvOn.lean`'s
  `image_leaseAlarmNA` split: alarm still empty). The KV model's table stays untied to the lessor
  (narrow): only the rest model's lease bucket and the lessor's history are related.
- **S4. `srvGrantOpen` discharged.** `run_job_snap` at `lg = true` proved from S1-S3;
  `runSnapLgOkBody` proved, `srvGrantOpen` and its sorry gone, `lease.bootCfg` (Part C) loses its
  `lg = true → srvGrantOpen` conjunct. `etcd_leasegrant_safe` loses the `sorry`.
- **Open item (S3/S4, from the axiom review `axiom/leasettl` `d07861dbbf`,
  `notes/axiom-review/lease-ttl-row.md`, 2026-11-05):** Go treats a start with a fresh WAL
  directory over an old db holding leases as a *first start*: `StartNode` runs, and `NewLessor`
  recovers the db's leases before the first election. Today the fresh-data-directory bootstrap
  assumption excludes that case, not the lease-TTL row's `lessorAt γl 0 (∅, ∅, ∅)`. Once restarts
  (or such starts) recover leases, the row must say "the lessor is empty until this member's
  leadership", not "the history begins empty".
- **S5. Test.** A Go test of a three-member granting cluster in which a follower is cut off, the
  others grant leases (and let one expire) and compact past the follower's index, the follower is
  reconnected and restored from a snapshot, then lists (`Leases` at that member) the live leases
  and not the expired one, and later expires the restored leases once it leads (expiry forever
  until `Promote`). Built on `leasegrant_cluster_test.go`'s cluster.

Order: C, then X, then S (S needs X2's mode and X7's revocations in the image), then E.

## Review round 1 (2026-11-04, a fresh `spec-reviewer` on `7a22a6c177`)

Requirements (each checked against the code; R1's and R2's premises re-verified by hand):
- **R1. X2 breaks every grant in `leaseexpiry`.** The grant path assumes a monotone lessor whenever
  `lg = true` (`srvGrantable`, `InvRest.lean:621`: `lessorModeIs … true`; `grantPermRq`/`grantPre`,
  `apply/Chain.lean:1576-1610`; `leaseGrantedAt`, `InvLessor.lean:453`), so with X2's mode `false`
  no grant is provable; `srvRest_revocable` ("revocable ⇒ `lg = false`", `InvRest.lean:648`) stops
  describing reachable states; and `decide leasesNoExpiry` keeps the premise inside the server.
- **R2. E2 is false on the forwarded path.** A follower forwards `TimeToLive` to the leader; the
  examples' peer listeners serve only the raft handler (`etcdstart/common.go:170`), so
  `/leases/internal` answers 404, which `TimeToLiveHTTP` reads as `ErrLeaseNotFound` for a live lease
  (`leaseTimeToLive.spec`'s docstring records it). Also: E2 is at the wrong level (the server returns
  the error; the gRPC handler builds `TTL = -1, GrantedTTL = 0`, `v3rpc/lease.go:67-73`), and
  `GrantedTTL ≠ 0` on the found arm needs `MinLeaseTTL ≥ 1` (false at `ElectionTicks = 0`).
- **R3. P1 is a blocker.** `GoAttach.spec` gives `f` only `P` and takes back `True`; the expiry
  goroutines need a token, `wgMu`'s and the logger's and read loop's reader slots per round, and
  rounds are unbounded (an unrevoked lease is re-sent each retry interval).
- **R4. X6.** Go's `LeaseRevoke` is `requireAuthInfo`, a span, `raftRequest` (not
  `raftRequestOnce`), and a type assertion that panics unless the response is a
  `*LeaseRevokeResponse`. P2's `¬ leasesNoExpiry` premise is unneeded. v3rpc's `lessorRevokeOk`
  (`InvLease.lean:156`, no premise) is still an undischarged premise of client results; X6
  discharges only a mode-gated version.
- **R5. X3** also needs the slice itself read-only (`ls ↦*□`).
- **R6. Part S.** `MustUnsafeGetAllLeases` needs a premise that every record decodes as a
  `leasepb.Lease` whose ID is its key (it keys the map by the decoded ID, `lessor.go:816`), which
  S3's image fact supplies (`persistTo` → `MustUnsafePutLease`), and a `proto.Unmarshal` law for
  `leasepb`; S3 relates lease **ids** only (TTLs differ between members: `MinLeaseTTL` is per
  member, checkpoints rewrite `RemainingTTL`); the image's KV keys lease-free is a fact S3 states
  (`kv.Restore` calls `Attach` for leased keys, `kvstore.go:396-398`).

Preferences: C's inventory misses `%Hslg` in `InvStart`, `ServerOn`, `RunOn`, `StartOn`,
`etcdstart/Defs`, `Alloc`, and `srvPeerRt` in `InvRestart`; C1's `on` argument is a coupling lease
owns (say so), `_noExpiry` stays internal; `hlease` is in the twins `SnapImageFacts`/
`SnapImageFactsOn` of hub 3 (`applySnapshot.specSnap`/`specSnapM`): collapse them or put the image's
lease fact behind a sealed `lease.imageOk`; lease-id masking (`& (2^63-1)`) can make two members'
ids collide (an `ErrLeaseExists`, not a wrong result).

## Draft, revision 2 (2026-11-04, the round-1 repairs)

- **C2 reversed for the mode: `lease.Names`** (`LeaseApi.lean`) with `mode : lease.Mode` (`none |
  mono | revocable`, chosen by the caller as `lg` is) and the lessor's name (`E.γ.leases`).
  `KVNames.lg` stays (C2's 190-site argument stands for it; `lg = (mode ≠ none)`, a law).
  `lease.bootCfg γl on := (on = true → γl.mode = none) ∧ (γl.mode = mono → leasesNoExpiry) ∧
  ckptEffectsOk` (until S4 also `γl.mode ≠ none → srvGrantOpen`). The premise appears only
  there; `mono` is how `leasegrant` keeps its proof; `leaseexpiry` takes `revocable`.
- **X2 (replaced).** `NewLessor`'s mode from `γl.mode`; `srvGrantable`, `grantPermRq`, `grantPre`
  generalized to `lessorModeIs E.γ.leases m`; a mode-free grant fact (`leaseLiveAt γl i id`) for the
  grant's reply, `leaseGrantedAt` its monotone strengthening; `srvRest_revocable` restated
  (revocable ⇒ `mode ≠ mono`).
- **X1/X4.** The guard `⌜mode ≠ none ∧ on = false⌝`; in mode `mono`, `expiredC`'s `¬ leasesNoExpiry`
  makes `run`'s arm dead (as now), in `revocable` the arm is X5.
- **X3** adds `ls ↦*□` (R5). The `axiom` skill before Freeze.
- **X5 with R3's fix: lend the token.** `GoAttach.spec` generalized (proved): `f` gets the counted
  `threadTok` (`{P ∗ threadTok} f {threadTok}`), the wait group holding a loan receipt
  (`notes/bounds-plan.md` B2, `ownThreadLoan`); with it the outer goroutine borrows `wgMu`'s, the
  logger's and the read loop's reader slots from server-owned pools; `run` needs nothing per round.
  `GoAttach`'s callers re-checked (the spec is a generalization).
- **X6 (R4).** `LeaseRevoke.spec` over `requireAuthInfo`, the span, `raftRequest`, and the response's
  type (`chain_revoke`'s answer a `*LeaseRevokeResponse`); premise `mode = revocable`; v3rpc's
  `lessorRevokeOk` discharged mode-gated, the ungated one stays a premise of the client results
  (said in its docstring).
- **X7.** `rqOk` at `.leaseRevoke`: `mode = revocable` (no `leasesNoExpiry`).
- **E2 (replaced).** At the handler: `leaseTTLOut`'s not-found arm gives `lease.leaseAbsentAt γl i
  id ∗ lessorLb γl i` **under a single-voter row** (`□ (⌜single voter⌝ → …)`, the forwarded path the
  margin), the found arm `GrantedTTL ≠ 0` from a configuration fact (`ElectionTicks ≥ 1` with the
  heartbeat, carried by `lessorCfg`). Trusted where it rests on `leaseTimeToLive` (`axiom` skill).
  The example is single-member, so the row applies.
- **E3 (a), reshaped.** An exclusive "granted at most once" right per id, handed out with the fresh
  id the server's generator claims (after the mask), and required by a grant with an explicit `ID`
  (the admin-history pattern); absence at `i` then lasts.
- **S1** with R6: `MustUnsafeGetAllLeases`'s spec takes every record to decode as a lease whose ID
  is its key; check Perennial's `proto` specs for `leasepb`'s `Unmarshal`.
- **S3** behind a sealed `lease.imageOk D ids` (ids only, TTLs existential; records decodable; KV keys
  lease-free), one conjunct in each of `SnapImageFacts`/`SnapImageFactsOn` (no collapse of hub 3's
  twins in this stage; `lease.imageOk` keeps the next lease change out of them).
- **Hubs touched**: the boot hub (C), the name records (`lease.Names`), hub 3 (`specSnap`/
  `specSnapM`, one sealed conjunct), the examples' entry points (`leaseexpiry`).

Round 2: a fresh reviewer on this revision, hardest on R1-R3's repairs.

## Review round 2 (2026-11-04, a fresh `spec-reviewer` on `a8b45a46ba`)

- **R3's repair is not provable** (re-verified by hand): `fork` makes one token (`wp_fork_tok`,
  Perennial `Lifting.lean:1806`) and `GoAttach`'s `Add` deposits the caller's in the wait group's
  invariant (`wp_goAttach_Add`, `InvGoAttach.lean:171-192`), which the counter bound needs; so
  lending `f` a counted token needs three tokens for two threads, and no goroutine started by
  `GoAttach` holds a token, so the outer expiry goroutine can neither `GoAttach` nor call
  `ensureLeadership` (which takes `threadTok`) under any pool design. Borrowing `wgMu`'s slot
  contradicts `notes/bounds-plan.md` (`wgMu` stays counted). The inner goroutine also needs
  `IsAuthEnabled`'s lock (`WithRoot`, `auth/store.go:1176`), `E.RD`, `srvLeadTimeReader`,
  `srvAuthAt`. The reviewer's fix: bounds-plan's D2(b), thread tokens split by level
  (`threadTok ⊣⊢ [∗ l] levelTok l`), a Perennial change proposed on its own. **For the user (P1).**
- **R2's condition is wrong.** A single voter forwards too, before its first election (`waitLeader`
  returns itself; its own peer URL answers 404), and a learner forwards to another member. Still
  true, because no lease is applied before `r.lead` is stored (`raft.go:190-202`) and a sole voter
  never loses leadership: that argument goes in the trusted statement's docstring. Fix: the row is
  "this member is the cluster's only member, no membership change admitted". `GrantedTTL ≠ 0` on the
  forwarded path is the leader's `MinLeaseTTL`, so it also needs the row; the configuration fact
  bounds `ElectionTicks·TickMs` against `Duration` overflow (`server.go:344`); `lessorCfg`
  (`InvLessor.lean:742`) gains `1 ≤ minLeaseTTL`.
- **R1, the couplings.** `lg = (mode ≠ none)` must be stated (`rqOk lg`'s grant arm; `srvSnapRO`'s
  `lessorModeIs E.γ.leases γr.kv.lg`, `SnapRO.lean:447`; `ApplyAllSnap.lean:104-106, 185`,
  `ApplyAllSnapOn.lean:145`), and `γl.leases = E.γ.leases`. The generalized grant path has no `m`
  in scope (`AEnv` has no mode); `lessor.Grant.spec` needs no mode (its post is `leaseLiveFrom`).
- **E3's right is duplicated across members** (each member's generator mints it; the mask merges
  prefixes): one cluster authority, or the right under the single-member row only.
- Preferences: pin the image's records as `leaseEnc id t r` under `u64Be id` (what `Grant.spec`
  writes); say the `mono` arm's death comes from `bootCfg`'s `_noExpiry` in `isServerRun`; X6's
  context is `s.ctx` via `WithRoot`, auth off for the run; Hubs touched adds `SnapRO`, `srvRest`,
  v3rpc's `lessorGrantOkL`.

## Draft, revision 3 (2026-11-04; P1 open)

- **C1.** `lease.bootCfg lg γl on := lg = decide (γl.mode ≠ none) ∧ (on = true → γl.mode = none) ∧
  (γl.mode = mono → leasesNoExpiry) ∧ ckptEffectsOk` (`∧ (γl.mode ≠ none → srvGrantOpen)` until S4),
  with `γl.leases = E.γ.leases` stated where `E` is (`lease.srvInv`). `mono`'s dead arm comes from
  `bootCfg`'s `_noExpiry` (internal) in `isServerRun`.
- **X2.** The mode conjunct leaves `srvGrantable`, `grantPermRq`, `grantPre`; the grant's reply carries
  the mode-free `leaseLiveAt`; `lease.srvInv` gains `□ lessorModeIs γl.leases (decide (γl.mode =
  mono))` with a law `leaseLiveAt` → `leaseGrantedAt` at `mono` (v3rpc's `lessorGrantOkL`,
  `leasegrant/Main.lean:192`). `srvRest_revocable` deleted: its callers take `lg = false` from
  `specSnap`'s premise and C1's coupling.
- **E2.** The row is "the cluster's only member, no membership change admitted" (persistent, from the
  cluster's boot peers and `ccApplyOk`), under which the not-found arm gives `leaseAbsentAt γl i id ∗
  lessorLb γl i` and the found arm `GrantedTTL ≠ 0`; the docstring carries the `r.lead` argument.
  `NewServer`'s configuration premise gains `ElectionTicks ≥ 1`, `TickMs ≥ 1`, no `Duration`
  overflow (inside `raftNode.bootCfg` or `lease.bootCfg`), `lessorCfg` `1 ≤ minLeaseTTL`.
- **E3.** The "granted at most once" right under the single-member row only (one generator, so no
  duplicate); explicit-ID grants take it too.
- **S3.** `lease.imageOk D ids`: every record `leaseEnc id t r` under `u64Be id`; ids only.
- **X5.** Blocked on P1.

**Decided (the user, 2026-11-04):** P1, the Perennial change (thread tokens by level, bounds-plan
D2(b)) proposed on its own, `EtcdServer.revokeExpiredLeases.wp_proof` a marked `sorry` meanwhile (a
new `sorry`, approved), the rest of the stage proceeding and landing with it; E2/E3, the
single-member row (a trusted restatement of `leaseTimeToLive`, the `axiom` skill before Freeze).

## Review round 3 (2026-11-04, a fresh `spec-reviewer` on `08cfd673a3`)

First tier: **R1** `γl.leases` cannot be a caller's name (`NewLessor` allocates `γl` in its post,
`NewLessor.lean:129-131`; `NewServer.specG` returns `E` existentially, `:311`). **R2** deleting
`srvRest_revocable` breaks `applySnapshot.specSnapM`'s proof (`EtcdServer__applySnapshot.lean:131`)
and the walk (`SnapApplyWalk.lean:369`), which have no `lg = false` premise. **R3** `srvSnapRO`'s
`lessorModeIs E.γ.leases γr.kv.lg` (`SnapRO.lean:447`) is false in revocable mode. **R4**
`kv_lease_served`'s `lg = true` arm (`etcdstart/ServedLease.lean:177`) registers grant/listing
specs fixed to `leaseGrantedAt` (`client/v3/InvLeaseGrant.lean:60,76`): false in revocable mode.
**R5** E2's found arm is not provable from a configuration premise: `MinLeaseTTL =
int64(math.Ceil(minTTL.Seconds()))` and the float specs are uninterpreted (`Spec/math/Ceil.lean`
posts `True`, `Duration.Seconds_ptr` some `f`). **R6** X5's `sorry` reaches every server result
(`run` takes `revokeExpiredLeases.spec`, `Link.lean` passes it unconditionally), unlike
`srvGrantOpen_open`, kept out by a premise only granting results discharge. **R7** (reachability
uncertain) on a restart, replayed grants are applied before any election, so a live lease is
forwarded (404 → not found). **R8** E3 is a sketch: no law, no invariant tying an id's first
appearance in the history to a spent right, no account of boot's and `Recover`'s snapshots.
Adequate: E2's row (static membership makes "only member" the pure `cfg = {nid}` of the names), S3,
the mode encoding, `mono`'s dead arm. Preferences: `leaseLiveAt` → `leaseLiveFrom` (exists,
`InvLessor.lean:345`; `leaseAbsentFrom` too); E2's configuration premise not in `lease.bootCfg`; S3's
key is `leaseKey id` (`RestLease.lean:32`), `t`, `r` existential; `srvGrantsLeases`' docstring.

The third round on the same statements (`notes/spec-first-plan.md`, "When to stop iterating"):
R1-R4, R6 and R7 repaired below; R5 and R8 go to the user; then the glue against the real callers.

## Draft, revision 4 (2026-11-04)

- **C1 (R1).** The caller chooses only the mode `m : lease.Mode`: `lease.bootCfg lg m on := lg =
  decide (m ≠ none) ∧ (on = true → m = none) ∧ (m = mono → leasesNoExpiry) ∧ (m = revocable →
  srvRevokeOpen) ∧ ckptEffectsOk` (and `m ≠ none → srvGrantOpen` until S4); `lease.srvInv on s E m :=
  … ∗ □ lessorModeIs E.γ.leases (decide (m = mono))`. No `lease.Names` record yet (the mode is the
  only caller-chosen datum; the names stay where `NewLessor` makes them).
- **X2 (R2, R3, R4).** `srvRest_revocable` kept, restated mode-generic (`lessorModeIs … false ∧ ¬ m =
  revocable → lg = false`); `applySnapshot.specSnapM` takes `E.lg = false →` until S4 (`applyAll`
  discharges it from `hlgk` and `isServer`'s `γr.kv.lg = E.lg`, `InvApplier.lean:674`); `srvSnapRO`'s
  mode conjunct at `decide (m = mono)`, `srvSnapRO`/`applyAll.specSnap` taking `m`;
  `lessorGrantOkL_of_server`/`lessorGrantOkL_server` take `lease.srvInv … mono`; `kv_lease_served`
  split by mode (mono as now; revocable registers the grant spec at the mode-free
  `∃ l, leaseLiveFrom` and a listing spec with no `G`); `leaseGrantedResp` (`LeaseGrant.lean:70`) and
  the chain's answer (`apply/Chain.lean:1132`) move to the mode-free fact.
- **X5 (R6).** `run`'s revocable arm takes the open premise `srvRevokeOpen` (sealed, its body
  `revokeExpiredLeases.spec`), in `lease.bootCfg` at `m = revocable`, discharged only in
  leaseexpiry's linked file (the marked `sorry` reaches leaseexpiry's results only, as
  `srvGrantOpen_open` reaches leasegrant's).
- **E2 (R7).** The row also says "first incarnation" (no restart): the restart contracts
  (`InvRestart.lean`) do not take `lease.bootCfg` at `m ≠ none` until a restart stage admits leases.
  The not-found arm gives `leaseAbsentFrom`.
- **Hubs touched** adds hub 3's `applySnapshot.specSnapM` (one premise until S4), `SnapRO`,
  `kv_lease_served`.
- **R5, R8**: the user's.

**Decided (the user, 2026-11-04):**
- **R5: track the TTL in the lessor.** The lessor history's snapshots record each lease's `ttl`.
  `Grant` and `Recover` only raise it (`lessor.go:301`, `:817`), so a lease granted with `TTL ≥ 1`
  keeps `ttl ≥ 1`. The restated `leaseTimeToLive` gives the found arm `GrantedTTL` as the lessor's
  recorded `ttl` of `id` at an index; the example grants `TTL = 1`. This touches the history's
  snapshots and the `Grant`, `Recover` and `Checkpoint` specs.
- **R8: generated ids only.**
  - In the revocable mode, `EtcdServer.LeaseGrant`'s spec requires the request's `ID = 0`.
    clientv3's `Grant` always sends `0`.
  - So every grant takes a fresh id from the member's generator, unique under the single-member
    row. Explicit-ID grants are outside the revocable mode's workload.
  - The invariant: each id's first appearance in the lessor history is the one grant of that
    generated id.
  - The law: an id absent at `i` after its grant at `i₀ ≤ i` stays absent at every `j ≥ i`.

## Plumbing: Part C (2026-11-04)

Done (revision 4's C1, with `revocable` refused by the slot until Part X):
- `etcdserver/LeaseApi.lean` (sealed, `etc/import-all.txt`): `lease.Mode` (`none | mono | revocable`);
  `lease.bootCfg lg m on := lg = decide (m ≠ none) ∧ (on = true → m = none) ∧ (m = mono →
  leasesNoExpiry ∧ srvGrantOpen) ∧ (m = revocable → False) ∧ ckptEffectsOk`, intros `_none`,
  `_mono`, eliminations `_lg`, `_auth`, `_ckpt`, `_open`, `_noExpiry`; `lease.srvInv on s E m`
  (persistent; `□ (⌜on⌝ → srvLessorNil s) ∗ srvPeerRt s ∗ srvLessorRd s E.γ.leases ∗
  lessorRdPool E.γ.leases`, `m` not read yet), `srvInv_intro` and the eliminations `_lessorNil`,
  `_peerRt`, `_lessorRd`.
- `NewServer.specG`: a binder `m : lease.Mode`, the premise `lease.bootCfg ρ.rd.kv.lg m on` in place
  of `on = true → lg = false`, `%Hckok` and `%Hslg`; `lease.srvInv on srv E m` in place of the post's
  four lease conjuncts. `spec`/`specM` unchanged as abbreviations (the binder is inside `specG`).
- Callers: `newServerMode` (`m := if lg then mono else none`, from `memberBoot`'s fact and its
  `ckptEffectsOk` premise), authkv's `startServer` (`none`). `Results`/`Link` pass proofs only (no
  edit; `Link.lean` regenerates identically). No v3rpc consumer reads the post's lease conjuncts
  (the served lease reads take them through `etcdstart.srvLeaseRd`, now from `srvInv_lessorRd`).

Deviation: the inner predicates keep their piece inline. `isServerRun` and `srvGrantOpen` are both in
`InvRun.lean`, upstream of `ckptEffectsOk` (`InvBoot`) and `srvLessorNil` (`ServerOn`), so `srvBuilt`,
`srvBuiltG`, `isServerBuilt(On)`, `isServerRun(On)` cannot name `lease.bootCfg` without moving
`srvGrantOpen` (with `runSnapLgOkBody`) and `ckptEffectsOk` below them; and they have no `m` or `on`
(threading them is about 140 sites). They keep `%Hslg` (`lg = true → leasesNoExpiry ∧
srvGrantOpen`), the plan's "needed half", which `NewServer`'s proof derives with `_noExpiry`/`_open`.
Likewise `etcdstart`'s `memberBoot`/`memberBootOn`/`alloc1` (pre-`NewServer`; `alloc1` has no
`ckptEffectsOk`), and `InvRestart`'s `%Hprt` (`bootstrap`'s round tripper, not the slot). For Part X
(the revocable arm needs `m` in `isServerRun`): options (a) a sealed `lease.runCfg lg m` in a module
below `InvRun` (moving `srvGrantOpen`), carried as `∃ m, lease.runCfg lg m` by the inner predicates,
`lease.bootCfg_run` its intro; (b) `m` threaded through the inner predicates; (c) inline until Part X.

Option (a), done (2026-11-04, the user's decision below): the inner predicates' piece behind a slot.
- `etcdserver/LeaseRun.lean` (new, sealed in `etc/import-all.txt`, `import all`-ed by `LeaseApi.lean`
  only): `lease.Mode` (moved from `LeaseApi.lean`), `runSnapLgOkBody` and `srvGrantOpen` (moved from
  `InvRun.lean`, names and docstrings kept), and `@[no_expose] lease.runCfg (lg : Bool) (m :
  lease.Mode) : Prop := lg = decide (m ≠ .none) ∧ (m = .mono → leasesNoExpiry ∧ srvGrantOpen) ∧ (m =
  .revocable → False)` (the last conjunct a placeholder until Part X). Laws: `lease.runCfg_none`,
  `lease.runCfg_mono` (intros before `NewServer`: `alloc1`'s callers), `lease.runCfg_lg`,
  `lease.runCfg_open` (`run_job_snap`). In `LeaseApi.lean`: `lease.bootCfg_run` (the intro from the
  boot slot, `NewServer`) and `lease.bootCfg_of_run` (`newServerMode`, from `memberBoot`'s).
- To put it below `InvRun.lean`, `InvRun.lean` is split: its vocabulary (`ApplyCtx`, `applyRes`,
  `applyStart`, `srvMetaSnap`, ..., which `runSnapLgOkBody` names) is `InvRunRes.lean`; then
  `LeaseRun.lean`; `InvRun.lean` keeps `isServerRun` and `srvSnapDisk_of_RO`. No definition changed.
- `%Hslg` is `⌜∃ m : lease.Mode, lease.runCfg γr.kv.lg m⌝` in `srvBuilt`, `srvBuiltG`,
  `isServerBuilt`, `isServerBuiltOn`, `isServerRun`, `isServerRunOn`, and the same conjunct in
  `etcdstart`'s `memberBoot`/`memberBootOn` and `alloc1`'s premise `hlg` (no new premise: `∃ m,
  lease.runCfg lg m` is equivalent to the old `lg = true → leasesNoExpiry ∧ srvGrantOpen`, by
  `m := if lg then mono else none`). `run_job_snap`'s `hslg` likewise. Callers: `NewServer`
  (`bootCfg_run`; the grant guard now from `bootCfg_noExpiry` directly), `newServerMode` (the mode
  is `memberBoot`'s, `bootCfg_of_run`), `alloc1_false`, `Alloc3`, auth's `MainAlloc`, `lease`'s and
  `leasegrant`'s `Main` (`runCfg_none`/`runCfg_mono`). `InvRestart`'s `%Hprt` untouched (not the
  slot). `lease.bootCfg`'s body unchanged (it repeats `lease.runCfg`'s conjuncts; Part X edits both).

## Plumbing: R5 and S1 (2026-11-04, branch `lease-expiry-recover`)

**R5, done** (`3498242493`). `LSnap` is `(lease map, item map, TTL map)`. The reader invariant
(`lessorRdBody`) gains `ttlTie` for every snapshot. A snapshot's TTL map has exactly its live ids,
and each lease's TTL is its read-only `ttl` field. Grant inserts the granted TTL (`grant_hist`,
`ttlTie_insert`), Revoke deletes it, and Attach/Detach keep it (`hist_append(_set)` take a
`tieSub` of the last snapshot). Recover's axiom appends `(∅, ∅, ∅)`. The laws:
- `leaseTTLAt γl i id t` (persistent): `id` has TTL `t` at index `i`.
- `leaseLiveFrom_ttl`: a lease found, with its `ttl` read, has that TTL in the history (what
  `TimeToLive` needs).
- `leaseGrant_ttl` (`LessorBackend.lean`): from Grant's post, the recorded TTL is `≥` the
  requested one (`grantTTL_ge`), so it is `≥ 1` for a `TTL ≥ 1` grant.

No spec changed: Grant's post already had `ttl ↦□ grantTTL mt ttl`. Checkpoint does not touch the
history.

**S1, partly done.**
- Done: `LeaseExpiredNotifier.Init` is specified and proved (`ee6424384a`, linked). Its post is
  `notifierAt np 1` again. The queue is not emptied: the stale entries stay, and `notifierAt` already
  admits any items.
- Not done: `Recover`'s new spec and proof, `initAndRecover`, `UnsafeCreateLeaseBucket`, and the
  `MustUnsafeGetAllLeases` axiom. The axiom was left out on purpose, so that the trust base changes
  only by the approved pair.

**The blocker: the frame fix has no supplier.** Go's `Recover` stores `le.rd = rd`. The model
splits `le.rd` between `lessorMu` and `rdOwn γl rd0`, so a provable spec must take `rdOwn γl rd0`
(the audit's frame finding). Its only caller cannot supply it:
- The snapshot walk (`SnapApplyWalk.lean:411`) holds no `rdOwn`.
- The apply thread's state (`leasesLive`, `srvApplyKVM`) holds no `rdOwn` either.
- `NewServer` drops `newWatchableStore`'s `∃ rd, rdOwn γl rd ∗ mvcc.rdIs rd …` (`BuildLemmas.lean:139`).
- The walk also lacks `lessorCfg`, which is needed to read `minLeaseTTL`.

Threading `rdOwn` reaches the apply-state hub: about 14 files and 32 sites use `leasesLive`, plus
NewServer/BuildLemmas. That changes the snapshot path's statements, which this stage was told not
to do. The options:
1. Thread `rdAt γl s` (`RangeDeleter.lean`, the L3c plan) from NewServer into the apply thread's
   state, as X6/X7's revocations need anyway (`apply/Chain.lean`'s `revokeRes`). Then land S1 on
   it, with the walk proving `rdIs` of its new closure.
2. Thread only `∃ rd, rdOwn γl rd` (no contract) through `leasesLive`: smaller, but X6 must
   redo it.
3. Defer S1 until L3c/X6 lands.

**Decided (the user, 2026-11-04):** the inner server predicates' lease premise behind a sealed
`lease.runCfg lg m` in a module below `InvRun` (Part C's option (a): `srvGrantOpen` and
`runSnapLgOkBody` move there; the inner predicates carry `∃ m, lease.runCfg lg m`, introduced from
`lease.bootCfg`); `Recover`'s range deleter by threading `lease.rdAt γl s` from `NewServer` into the
apply thread's state (option 1; Part X's revocations use it too), then S1 on it.

## Step 2 (thread `lease.rdAt`): stopped before plumbing (2026-11-04)

`lease.rdAt γl s` is `∃ rd, rdOwn γl rd ∗ □ ∀ ws γw, isWatchableStore ws s γw -∗ rdIs rd ws s γw`
(every watchable store over the inner store `s`, at any names: what `LessorDerive`'s revoke clause
needs, since `txn.kvWriter_open` hands it a store and names existentially). Its producer gives less:
`newWatchableStore.spec`'s and `mvcc.New.spec`'s posts (and `server_kv_watchable(_of, _ofM)`,
`Results.lean:915`, `BuildLemmas.lean:76, 229`, which restate them) end in `∃ rd, rdOwn γl rd ∗
mvcc.rdIs rd ws st γw`, the deleter's contract at the store's own `ws` and `γw` only, with `rd`
hidden. `isWatchableStore_agree` (`SnapApplyOpen.lean:164`) gives `ws' = ws` but not `γw' = γw`, and
`rdIs` at `γw` says nothing at another `γw'`, so `rdAt_intro` cannot be applied at `NewServer`.
Options:
- (a) Strengthen the two mvcc posts (and the three restatements) to `lease.rdAt γl st`: provable,
  since `newWatchableStore`'s proof of the closure (`s.Write(TODO)`, `newWatchableStore.lean:177`)
  uses `Write`'s spec at the store's names, which it can take at any `γw'` with `isWatchableStore s
  st γw'` (and `ws' = s` from the agreement law, moved into mvcc). Stronger posts on mvcc's
  constructors and one exported result (`server_kv_watchable`).
- (b) Weaken `rdAt` to the store's own names and change the revoke clause's consumer instead (would
  need `kvWriter_open` to return the construction's `γw`: a change to `txn`'s writer).
For the user. Steps 2-3 (S1) wait on this.

**Decided (the user, 2026-11-04):** the `rdAt` gap by (a): `newWatchableStore.spec`'s and
`mvcc.New.spec`'s posts (and their restatements, `server_kv_watchable`, `BuildLemmas`) give
`lease.rdAt γl st` (the deleter's contract at any names), proved over a store-agreement law moved into
mvcc; stronger proved posts, no trust change.

## Step 2: `rdAt` and `lessorCfg` threaded (2026-11-04)

Done by (a). `mvcc.isWatchableStore_agree` (`InvWatchStore.lean`, moved from `SnapApplyOpen`)
gives `ws' = ws`; `newWatchableStore`'s closure proof then takes `Write`'s spec at the caller's
`γw'`, so `newWatchableStore.spec`, `mvcc.New.spec`, `server_kv_watchable(_of, _ofM)` and
`M2StorageDraft` end in `lease.rdAt γl st`. The apply thread carries it on the server-level applier
row, not in apply's `leasesLive`: `srvApplyKV`/`srvApplyKVOn` end `∗ lease.rdAt E.γ.leases E.s`
(so `applyBuilt*`, `applyBuiltNA*` and NewServer's post hold it), and `snapWalkPost` returns it after
`leaseRevokers`; `applySnapshot_walk`'s pre gains `lease.lessorCfg lp` (from the caller's `#Hlcfg`).
Part X lends `rdAt` as `revokeRes` from the row. No statement weaker; no trust change.

## Step 3 (S1, `Recover`): stopped before writing (2026-11-04)

Two points the approved design does not settle:
1. **The form of `schema.MustUnsafeGetAllLeases`'s axiom.** `MustUnsafePutLease` is premise-style:
   it takes the triple of `tx.UnsafePut` and is proved against it. The same form here would take a
   triple of `tx.UnsafeForEach(Lease, visitor)`. Nothing proves that triple: there is no spec of
   `batchTx.UnsafeForEach` or of bbolt's `Bucket.ForEach`, so discharging it in `initAndRecover`
   needs a new axiom or a backend proof well outside this stage. Options:
   - (a) A contract over the batch lock's state, as `batchTxBuffered.UnsafeRange.spec` and
     `MustReadMembersFromBackend` are. The pre is `isBackend`, `bF "batchTx" b ↦□ t`,
     `batchLocked γ P b st`, `schema.Lease ↦□ bk` and `isBucket bk leaseBI`, with the bucket
     `bktOf st.S "lease"` holding only `leaseEnc id t r` under `leaseKey id`. The post is
     `batchLocked γ P b st` and a slice of fresh `*leasepb.Lease`, one for each record in key
     order. Its docstring covers `batchTx.UnsafeForEach` (bolt's cursor over the writer's tx), so
     it trusts a little more than the put does.
   - (b) Premise-style plus a new axiom for `batchTx.UnsafeForEach`. That is outside the approved
     trust change.
2. **The grant guard of recovered leases.** `lessorAuth` keeps `□ [∗list] id ∈ L, leaseGranted γl
   id` for the live set, and `NewLessor`'s `expiredC` payload depends on it. A post with
   `leaseOwn γl L' ∅` therefore needs `□ [∗list] id ∈ L', leaseGranted γl id` in `Recover`'s pre.
   The walk's `L' = []` makes it vacuous. The alternative, dropping the guard for recovered
   leases, would weaken `lessorExpiredC`.

The rest has a route with the existing lemmas:
- The backend: `bt_lockOut`/`bt_create`/`bt_unlockO`, `batchLocked_rbPart`, `rbPart_split`, and
  `commitReq_true` for `ForceCommit`.
- The leases: `closers_grant`'s steps (`init_RWMutex`, pools), or one new append lemma
  `closers_recover`. That lemma keeps `histMono` when every old live id is in `L'`.
- The heap: `heap.Init_.spec`, as in `LeaseExpiredNotifier.Init`.

**Decided (2026-11-04):**
1. The user chose (a). `schema.MustUnsafeGetAllLeases.wp_proof` is a contract over the locked batch
   transaction's state.
   - Pre: `batchLocked γ P b st`, with every record of `bktOf st.S "lease"` equal to `leaseEnc id t r`
     under `leaseKey id`.
   - Post: `batchLocked` unchanged, and a fresh slice of `*leasepb.Lease`, one per record, in key
     order.
   - Its docstring says what it trusts: `UnsafeForEach` reads the writer's bolt transaction, and
     Go's panic on a record that does not decode is excluded by the premise.
2. The coordinator's decision. `Recover`'s pre takes `□ [∗list] id ∈ L', leaseGranted γl id`;
   recovered leases are not exempted from the guard. The walk meets it at `L' = []`. A granting
   cluster's server meets it for any id, since its guard is pure in the mode.

## Step 3 (S1): `Recover` translated and proved (2026-11-04)

Done, under the approved trust swap (`- axiom lease.lessor.Recover.wp_proof`, `+ axiom
schema.MustUnsafeGetAllLeases.wp_proof`).
- `schema.UnsafeCreateLeaseBucket` translated (`schema.toml`) and proved, premise-style like
  `UnsafeCreateMetaBucket`. `schema.MustUnsafeGetAllLeases.spec`: the decided contract over
  `batchLocked`, records `lease.leaseRecEnc` (key and `leaseEnc` value) in key order (`bktEnts`).
  `lease.leaseRecs_nodup`: the records' ids are distinct.
- `lessor.initAndRecover.spec`/proof (`LessorRecover.lean`: `recMap`, `recTTLs`, `recLease`): the
  map holds one fresh `*Lease` per record, TTL raised to `mt`, with a receipt `⧖ |recs|`. The
  notifier is re-initialized (`notifierAt` already admits stale items). The checkpoint heap gets a
  new contents. The part is idle after `Unlock`, then `ForceCommit`.
- The ghost step (`LessorRecoverLemmas.lean`). `recover_one`/`recover_all`: each lease registered
  with the empty set (`setsOk_register`), its locks and pools made. `closers_swap`: the closers' map
  replaced (the old elements, both halves, deleted). `lessor_live_set`: the live set is the ids,
  with their `leaseGranted`. `recover_hist`: the snapshot `(recMap, ∅, recTTLs)` appended
  (`recover_step_ok`), `histMono` kept when every live id is recovered. `closers_recover` composes
  them.
- `lessor.Recover.spec` (the new text): pre adds `lessorCfg`, `lessorModeIs γl mono` (was
  `lessorRevocable`), `rdOwn γl rd0`, `□ [∗list] id ∈ ids, leaseGranted γl id`, the bucket's
  records (was: empty), and `mono = true → L ⊆ ids`. Post: `leaseOwn γl ids ∅`,
  `leaseRevokers γl ids`, `rdOwn γl rd`, `rbOwnIn S (r.insert "lease" (r "lease"))`, and the
  snapshot's index with `minLeaseTTL ↦□ mt`.
- The walk (`SnapApplyWalk.lean`) passes `mono = false`, `recs = []` (from `hlease`), the `rdOwn` of
  its `lease.rdAt`, and rebuilds `rdAt` with the new closure's `rdIs` (`s.kv.Write`: the store's
  agreement law and `watchableStore.Write`'s spec, two new hypotheses of the walk and of
  `applySnapshot`'s proofs, linked). The receiver's cell `s_ptr` is made persistent for the
  closure; the members loop's invariant holds it persistently.
- Not done here: S2-S4 (the monotone restore, the image's lease bucket, `srvGrantOpen`).

## Plumbing: Part X-a (2026-11-04)

**Done (commit 1): the revocable mode in the slots, X1, X3/X4, `run`'s expiry arm.**
- `Spec/.../etcdserver/EtcdServer__revokeExpiredLeases.lean` (new; no proof file, names-only): pre
  `isPkgInit ∗ srvFieldsAt s γ ci TM E ρ v ∗ srvRunFieldsAt s γr γg γcx rv SP ∗
  lease.expiredLeases (srvGrantGuard E.lg E.authMode.isOn) ls`, post `True`. Only what is below
  `LeaseRun.lean` can be named (the spec is `srvRevokeOpen`'s body, and `lease.runCfg` is under
  `InvRun`): so `srvFieldsAt` (auth off; `run` converts `srvFieldsAtM` by the guard's `on = false`),
  not `isServerRun`. The proof will add P1's thread resources and X6's.
- `LeaseRun.lean`: `@[no_expose] srvRevokeOpen := EtcdServer.revokeExpiredLeases.spec`,
  `srvRevokeOpen_spec`. `lease.runCfg lg m := lg = decide (m ≠ none) ∧ (m = mono →
  leasesNoExpiry) ∧ (m ≠ none → srvGrantOpen) ∧ (m = revocable → srvRevokeOpen)` (the open cases
  at every granting mode, as revision 4 says, so `runCfg_open` holds at `revocable`); laws
  `_revocable`, `_noExpiry`, `_revoke` added. `LeaseApi.lean`'s `lease.bootCfg` the same plus
  `on = true → m = none` and `ckptEffectsOk`; `bootCfg_revocable` added, `bootCfg_noExpiry` removed
  (its only user was the guard).
- X3: `lease.expiredLeases GA ls := ∃ ps, ⌜ps ≠ []⌝ ∗ ls ↦*□ ps ∗ [∗list] p ∈ ps, ⌜p ≠ null⌝ ∗ ∃ id,
  lsF "ID" p ↦□ id ∗ GA id` (`LessorBackend.lean`); `lessorExpiredC`'s payload `⌜¬ leasesNoExpiry⌝ ∗
  expiredLeases GA ls`. **Deviation:** `ps ≠ []` is added (Go: `if len(ls) != 0`); without it the
  `none` mode's arm is not dead (an empty slice meets any guard). With it the new payload implies the
  old one (`∃ id, GA id`).
- X1: `srvGrantGuard lg on := ⌜lg = true ∧ on = false⌝`. It keeps the flag `lg`, not the mode: its
  callers (`NewServer`'s `NewLessor` call, the field predicates through `E.lg`) have the flag, and
  `lg = decide (m ≠ none)` (`runCfg_lg`) gives the same guard. `srvGrantGuard_expired` restated: an
  expired slice gives `⌜lg = true ∧ on = false⌝`.
- X4: `lessorOk lg on l`'s `ExpiredLeasesC` bag carries `⌜¬ leasesNoExpiry⌝ ∗ expiredLeases
  (srvGrantGuard lg on)` (was `False`). The field predicates (`srvFieldsAt`, `srvFieldsAtM`,
  `srvFieldsBuilt`, `srvFieldsBuiltNA`) hold `lessorOk E.lg E.authMode.isOn v.lessor` (`authMode.isOn`,
  not `authOn`, so that the literal environment's projections match by `iframe`).
- `run`'s expiry arm: by the mode of `isServerRun`'s `∃ m, lease.runCfg γr.kv.lg m`: `none` dead
  (`γr.kv.lg = false`, `isServerC_lg` off, the guard's `E.lg = true`); `mono` dead (`runCfg_noExpiry`
  against `¬ leasesNoExpiry`); `revocable` calls `revokeExpiredLeases` through `srvRevokeOpen` and
  goes round the loop.

**Stopped before X2 (a design problem: the mode does not reach the client consumer).** X2 makes
`NewLessor`'s mode `decide (m = mono)`, so the grant chain (`grantPre`) cannot hold `lessorModeIs …
true` and its answer must be the mode-free `leaseLiveFrom`; the conversion to `leaseGrantedAt` then
needs `lease.srvInv … .mono` at v3rpc's `lessorGrantOkL_of_server`, whose caller is
`etcdstart.kv_lease_served`. That lemma sees the server only through `memberUp`'s `srvLeaseRd s E`,
which has no mode, and `memberUp`/`memberBuilt`/`memberBoot` (`∃ m`, not a parameter) do not carry
one. Options: (a) thread `m` as a parameter through `etcdstart`'s member predicates (`memberBoot`,
`memberBuilt`, `memberUp`, `srvLeaseRd`, `kv_lease_served`: about 100 sites in 33 files); (b) put the
lessor's mode in the apply environment (an `AEnv` field the stand-in `E₀`'s `envAgree` carries), at
the cost of a lease field in `AEnv` (against the slot convention's "never a field of `AEnv`");
(c) `srvLeaseRd` carrying `∃ m, lease.srvInv …` — not enough: `leasegrant` could not learn `m = mono`,
so its client spec would weaken. Recommended: (a).

**Decided (the user, 2026-11-04):** (a). The lease mode `m` becomes a parameter of etcdstart's
`memberBoot`, `memberBuilt`, `memberUp`, `srvLeaseRd`, `kv_lease_served` and what lies between; each
example picks its mode (`.none` everywhere but `leasegrant`, `.mono`; `leaseexpiry` later
`.revocable`). Then X2 as specified (revision 4 and the X-a brief).

**Plumbing: Part X2 (2026-11-04).** As decided, with these choices:

- Server: `NewLessor`'s mode `decide (m = mono)`; `srvGrantable`, `grantPermRq` and `grantPre` lose
  the mode conjunct; the grant's reply (`leaseGrantedResp`, `grantAnswer`) carries the mode-free
  `∃ l, leaseLiveFrom E.γ.leases i id l`. `lease.srvInv on s E m` gains `□ lessorModeIs E.γ.leases
  (decide (m = mono))`, and `lease.srvInv_grantedAt` turns the live fact into `leaseGrantedAt` at
  `.mono`. `srvSnapRO`'s mode conjunct is `∃ m, ⌜γr.kv.lg = decide (m ≠ none) ∧ E.lg = γr.kv.lg⌝ ∗
  lessorModeIs E.γ.leases (decide (m = mono))` (the `E.lg` tie: the auth-on install had none).
  `srvRest_revocable` is mode-generic (`m ≠ revocable`, `E.lg = decide (m ≠ none)`).
  `applySnapshot.specSnapM` takes `E.lg = false` until S4 (its walk used the lessor's revocable mode
  to refute the rest's leased arm, which the revocable mode no longer gives).
- v3rpc: `lessorGrantOkLive_of_server` (the server's grant at the mode-free `grantLiveG E`, no
  `srvInv`), `lessorGrantOkG_mono`, and `lessorGrantOkL_of_server` from the two at `lease.srvInv …
  .mono`; linked as `lessorGrantOkLive_server`, `lessorGrantOkL_server`.
- client: `etcdLeaseGrantSpecG G` (`etcdLeaseGrantSpec_eq`: the old spec at the grant at the
  history, by `rfl`), `etcdLeaseGrantSpecLive γl` (at `leaseLiveFrom`; weaker than nothing the
  clients use: `isGrpcRpc_leaseGrantLive_any`); `etcd_leaseGrantHandlerOkG` (the handler at any
  persistent `G`; `…OkL` its instance); `etcdLeaseGrantLiveMethods` / `etcd_leaseGrantLiveMethodsOk`
  (the lease reads, the listing at `etcdLeaseLeasesSpecAny`, the live grant).
- etcdstart: `memberBoot … (cmp) (m := none)` holds `lease.runCfg ρ.rd.kv.lg m`; `memberBuilt`,
  `memberUp` take `m` (default `none`); `srvLeaseRd s E m := ∃ on, lease.srvInv on s E m`
  (`srvLeaseRd_lessorRd`: the reader side it was). The start specs (`newServerMode`, `newServer`,
  `NewMember`, `StartServer`, `StartMember`, `StartPeriodicServer`, `StartCompactingServer`,
  `BuildServer.spec`/`specStop`, partition's `startMember`) quantify over the mode `lm` (stronger:
  the old ones are their instances at the mode of `memberBoot`'s former `∃ m`). The restart drafts
  (`specRestart`, `Start_builtR_spec`, `Start_builtS_spec`, restart's `startMember`) stay at the
  default `none`. `kv_lease_served … m (hm : ρ.rd.kv.lg = decide (m ≠ none))` posts
  `etcdLeaseServedAt m`: `none` the KV calls, `mono` `etcdLeaseGrantAt` (as before), `revocable`
  `etcdLeaseGrantLiveAt` (the live grant; the listing the lease reads' `etcdLeaseLeasesSpecAny`).
  `alloc1` takes the mode with its `runCfg`.

## Plumbing: Part X-b (2026-11-04): stopped at X7's design point, before any edit

The brief's gate: count the sites the mode must reach, do (i) (the mode a parameter of what needs it)
if under about 150, else stop with both options. Counted on `2c9b9fcd8b` (lines, `Proof`, `Spec`,
`examples`):

- **What reads the flag today.** The admission is pure and fed from the workload facts, not from
  `rqOk` alone: the apply thread's `rqOk E.lg x.log rq` (`uberApplier.Apply.spec`, `dispatch.spec`,
  `ApplyRec`) comes from `kvWork`'s `logShape γk.lg` (`entryShape` → `rqShape lg` → `rqOk lg` at every
  log), and `kvInv`'s `plainLogM γk.cmp γk.lg` (`plainEntryM`, `grantPropOk`). `γk` (`KVNames`) and
  `E` (`AEnv`, with `AEnv.lg`, tied by `srvKVInvs`' `γr.kv.lg = E.lg`) carry no mode.
- **(i), the mode a parameter.** Every predicate on that path gains `m`, and every binder above it:
  the pure names (`rqOk`, `rqShape`, `entryShape`, `logShape(M)`, `plainEntryM`, `plainLogM`,
  `grantPropOk`, their lemmas) 319 lines in 51 files; `kvInv`/`kvInvOn`/`kvInvM`/`kvWork`/
  `srvKVInvs(On, M)` 383 lines in 63 files; the apply side's `E.lg` 120 lines in 33 files (a mode
  binder in `Apply.spec`/`dispatch.spec` and their callers, since `AEnv` has none). The union of the
  flag's sites is 548 lines in 93 files; the changed lines are several hundred, well over 150.
- **(ii), a cluster flag `KVNames.lr : Bool := false`** (revocations admitted; `lr = decide (m =
  .revocable)` in `lease.runCfg`/`lease.bootCfg`). The pure names take it beside `lg`: 106 lines pass
  the flag explicitly (`… γk.lg`, `… lg`/`false`), the rest unfold; no binder threaded (it rides in
  `γk`). It needs an apply-side twin too (`AEnv.lr`, tied in `srvKVInvs` as `lg` is), since the apply
  thread reads `rqOk E.lg`: about 110-130 lines. Against the slot convention (a lease field in
  `KVNames` and in `AEnv`), as X-a's option (b) was.

Not decided here (the brief: (ii) is the user's). Two further points X7 meets whichever is chosen:
- `revokeRes` (`apply/Chain.lean:1314`) takes `⌜E.lg = false⌝ ∗ lease.lessorRevocable`: in a granting
  cluster the apply thread holds the live set's half `ltHalf` (48 sites) and the lessor's mode, so the
  revocation arm's resources must be reworked (the live set's half updated by `restRevoke`'s id), as
  the grant's were in lease-grant's 3b-4g.
- The KV model already has the revocation (`backendLog`/`backendTable`'s `.leaseRevoke` arms); the
  identity needs `revokeChanges (stateAfter log) id = []` from the plain log's lease-free keys and
  `commitLog log [] = log`.

**X6 not started**: `LeaseRevoke.spec`'s post (the revocation applied at some index) goes through
`raftRequest`, whose proposal needs X7's `reqPropOk` form.

**`revokeExpiredLeases.spec`'s pre (item 3, checked).** It has `srvFieldsAt` and `srvRunFieldsAt`
(with `srvGoAttachOk`: `s.ctx ↦□ c`, `s.stopping`, the wait group). A proof calling `LeaseRevoke` on
`LeaseGrant.spec`'s model lacks: `isServerReq s E ρ` (the request path's fields: `reqIDGen`, the raft
node, `kvInv`, the mint invariant; `srvFieldsAt` has only `waitInv`) and its `ρ` (the spec binds
none); `srvAuthAt s E` (`requireAuthInfo`, `WithRoot`'s `IsAuthEnabled`); a context fact for
`s.ctx` (`context.isContext c cd`: `srvGoAttachOk` has the field only) and a spec of
`authStore.WithRoot` (none exists; at auth off it returns its argument); per goroutine
`srvLeadTimeReader s`, `E.RD` and `□ (|==> idCred ρ.ids 1)` (P1's pools); and the mode
(`m = .revocable`: the guard gives only `E.lg = true ∧ auth off`). Not changed (the brief).

**Decided (the user, 2026-11-04): X7 option (iii).** `KVNames.lg` and `AEnv.lg` (Bool fields) are
replaced by fields `lm : lease.Mode := .none`; `lg` becomes a function of the same name
(`KVNames.lg γk := decide (γk.lm ≠ .none)`, likewise `AEnv.lg`), so the uses of `γk.lg`/`E.lg`/
`ρ.rd.kv.lg` read unchanged and only the sites that set or destructure the field change. Where the
code has both a mode `m` and the record, they are tied. The revocation arm of `rqOk`, the proposal
side and `kvInv`'s log shape read `lm = .revocable`. Then X7 (with the `revokeRes` rework and the
identity-step lemmas), then X6.

**Open item for Part E/P1: `revokeExpiredLeases.spec`'s pre** (not changed now). For its proof to
call `LeaseRevoke` it lacks: `isServerReq s E ρ` and a binder `ρ`; `srvAuthAt s E`; a context fact
for `s.ctx` (`context.isContext c cd`) and a spec of `authStore.WithRoot`; per goroutine
`srvLeadTimeReader s`, `E.RD`, `□ (|==> idCred ρ.ids 1)` (P1's pools); the revocable mode (`E.lm =
.revocable`, or `ρ.rd.kv.lm`).

**Done under option (iii) (2026-11-04, the X-b session's second part).**
- *The refactor* (`9f0627d0ad`). `KVNames.lm`/`AEnv.lm : lease.Mode := .none`; `lg` the reducible
  `decide (lm ≠ .none)` (`KVNames.lg_eq`/`lg_fold`, `AEnv.lg_eq`). `lease.Mode` moved to
  `lease/InvLessor.lean` (the apply layer names it). The tie chosen: `lease.runCfg`/`lease.bootCfg`
  take the record's `lm` and state `lm = m` in place of `lg = decide (m ≠ .none)` (`runCfg_lm`/
  `bootCfg_lm`; simpler than adding a second conjunct, and it gives `lg` by rewriting). `srvKVInvs`/
  `kvNameTiesM` tie `γr.kv.lm = E.lm`; `srvSnapRO`'s mode conjunct is `(⌜E.lm = γr.kv.lm⌝ ∗
  lessorModeIs (decide (E.lm = .mono)))`, no longer an existential mode.
- *The pure layer* (`73686c2598`, C2a). `rqOk`, `rqShape`, `entryShape`, `logShape(M)`,
  `grantPropOk`, `plainEntryM`, `plainLogM`, `entryOk(M)`, `plainOrCmpG` take `lm`; the grant arm at
  `lm ≠ .none`; no arm changes meaning.

**Not done: X7's revocation arm (C2b) and X6.** The design worked out, for the next session:
- `revokeKindOk rq := dispatchKind rq = .leaseRevoke ∧ needAdminPermission rq = false ∧ noSideEffect
  rq = false`; `rqOk`'s arm `match lm with | .revocable => revokeKindOk rq ∧ putOk log | _ => False`;
  `revokePropOk lm rq := lm = .revocable ∧ revokeKindOk rq` beside `grantPropOk` in `plainEntryM` and
  `reqPropOk` (result trivial, no client update, as the grant's).
- **`revokeRes` with the live set's other half.** `kvOwn`'s `leasesLive` already holds one half
  (`ltHalf E L`); `lessor.Revoke` (`revokeClause`) moves `lessorUser` to `L.filter (· != id)`, so the
  backend must update `γlt`, which needs `srvRest`'s half: `revokeRes E T rs := rdAt ∗
  lessorRevocable ∗ ltHalf E T ∗ E.RO rs ∗ ⌜E.lm = .revocable⌝` (`revokePre` gains `T`).
- **A design point for the triple's post.** The post today is `kvPost … ∗ revokeResAfter E id rs err`,
  conditional on `err`, with the outcome hidden in `kvPost`'s `∃`. The backend answers
  `.applied (revokeLog log id) false` whether the lease was live or not (`err` tells), while the auth
  and corrupt layers reject (`err ≠ nil`, `T` unchanged). Since `err = nil ↔ id ∈ L` and `L = T`
  (`ltHalf_agree`), at an applied outcome the live set after is `T.filter (· != id)` in both cases
  (`id ∉ T` makes the filter the identity), and at a rejection `T`. So the post should name the
  outcome, as `grantPost` does: `∃ o, … ∗ ltHalf E (revokeIds rq o T) ∗ E.RO (revokeRest T rq o rs)`
  with `revokeIds`/`revokeRest` (`restRevoke id` iff applied and `id ∈ T`) functions of the outcome;
  `dispatch.spec`'s post composes them with `grantIds`/`grantRest`. This changes the four revoke
  specs (`applierV3backend`, `authApplierV3`, `applierV3Corrupt`, the quota and capped wrappers'
  clauses) and `applierTriples`; internal to the apply package.
- `dispatch.spec`/`Apply.spec` take, for a revocation, `rdAt ∗ lessorRevocable` (`rdAt` from the
  server's applier row `srvApplyKV`; `lessorRevocable` from `srvSnapRO`'s `lessorModeIs (decide (E.lm
  = .mono))` at `E.lm = .revocable`) and give `rdAt` back.
- The server side: `AppliedTable`'s lemmas gain the revocation case (`T.filter`), `srvRestAt`'s
  `restLeasesWith f T r` commutes with `restRevoke` (a lemma), and the KV identity
  (`revokeChanges (stateAfter log) id = []` since no key is leased in `plainLogM`'s logs,
  `mvcc.commitLog log [] = log`, `0 ∉` the table's ids by `grantKindOk`).
- X6 then follows `EtcdServer.LeaseGrant`'s proof, with `revokePropOk` in the proposal.

**Decided (the user, 2026-11-04): the revoke triple's post names the outcome.** The apply
package's revoke specs (backend, auth, corrupt, the quota and capped clauses, `applierTriples`) take
a post naming the outcome as `grantPost` does, with `revokeIds`/`revokeRest` functions of it;
`revokeRes` gains the live set's other half (`ltHalf E T`) and `⌜E.lm = .revocable⌝`; after an
applied revocation the live set is `T.filter (· != id)`. (The mode-baseline raise 187 → 191 of the
`lit-mode` bridges is approved.)

## Plumbing: Part X-b, C2b (2026-11-04): the apply layer done, stopped at the KV identity

**Done** (`f18737307f`, on the decision above): `revokeKindOk` and `rqOk`'s live revocation arm at
`lm = .revocable` (`rqOk_leaseRevoke`); `revokeRes E T rs` with `ltHalf E T` and the mode; the
revoke specs' posts `kvPost … (fun o => revokeOutcomeIs resp err o ∗ revokeResAfter E rq T rs o)`
(`revokeIds`/`revokeRest` of the outcome, with their `_rejected`/`_nonRevoke`/`_noV3`/`_applied`
laws); the backend's proof updates the live set (`ltHalf_agree`, `ltHalf_update`; not live:
`L.filter (· != id) = L`); `dispatch.spec`/`Apply.spec` (and `Apply.specRec`) take and give back
`revokeOwn E rq` (`rdAt ∗ lessorRevocable` for a revocation, `True` otherwise) and compose
`revokeIds(A)`/`revokeRest(A)` over the grant's; `chain_revoke` restated with `T`.
`applyEntryNormal`'s four `Apply` sites supply `revokeOwn` as `True` and drop the wrappers
(`revokeA_drop`), since no revocation reaches them yet (`plainOrCmpG_rev`). No new axiom or `sorry`.

**Stopped: the KV identity needs a fact `kvInv` does not carry.** To admit a revocation at
`applyEntryNormal`, `kv_certPre_G`'s revocation case must certify the apply layer's log after the
outcome, `revokeLog log id = commitLog log (leaseDels (stateAfter log) id)`, from the KV model's
entry log, `backendLog`'s `if id ∈ lt.ids then commitLog log (revokeChanges …) else log`. They agree
when the state is lease-free (`mvcc.LeaseZero`: `leaseDels` is `[]`, and `revokeChanges` is `[]` for
`id ≠ 0`, with `0 ∉` the table's ids by `leaseGrantOk`), and lease-freeness of the model's log
follows from `plainLogM` (puts carry lease `0`; a grant keeps the log; a revocation commits only
deletions: `kvRaftSt_restorable`, generalized from `.none`) **given `mvcc.LogNoLease γk.log0`**,
which `kvInv` does not state (it has `γk.log0 ≠ []`; every allocation has `log0 = [[], []]`).
Without lease-freeness the two can differ (a key leased to `id ∈ L` but `id ∉ kvLeases γk A`: the
model's table folds `A` alone, the apply thread's set `appliedTable`'s `pre ++ A`). The apply
thread's `txn.leasesKnown L s` does not close the gap (case `id ∈ L`, `id ∉ lt`). Options:

- (a) `kvInv`'s conjunct `γk.log0 ≠ []` becomes `γk.log0 ≠ [] ∧ mvcc.LogNoLease γk.log0`
  (a strengthening of `kvInv`, a definition the server's exported statements use; its 23 openings
  and its allocations, all at `log0 = [[], []]`, change mechanically). Recommended.
- (b) the fact as a premise of `applyEntryNormal.spec`, threaded up the apply loop's specs to
  etcdstart (spec changes along that chain).

Left for after the decision: `revokePropOk` in `plainEntryM`/`reqPropOk(W)`, the server-side
revocation case (`srvRest_applyPG`'s, `AppliedTable`'s `T.filter`, the `restRevoke`/`restLeasesWith`
commute, `revokeOwn` from `srvApplyKV`'s `rdAt` and the revocable lessor), then X6 and the
mode-gated discharge of `lessorRevokeOk`.

**Decided (the user, 2026-11-04): (a).** `kvInv`'s conjunct `γk.log0 ≠ []` becomes `γk.log0 ≠ [] ∧
mvcc.LogNoLease γk.log0`. Then: the proposal side, the server's revocation case, the lease-freeness
lemma, X6.

## Plumbing: Part X-b, X7 done (2026-11-04); X6 stopped at the revoke answer's header

**Done (X7, the server's revocation case and the proposal side).**
- `revokePropOk lm rq := lm = .revocable ∧ revokeKindOk rq` in `plainEntryM` and in `reqPropOk`'s
  third disjunct (`grantPropOk ∨ revokePropOk`, result trivial, no client update);
  `kv_prop_au_grant` covers both (a revocation's entry is plain in the modes, claims nothing).
- Lease-freeness: `KVModelRestore`'s restorable lemmas generalized over `lm` (puts carry lease `0`,
  a grant keeps the log, a revocation of a lease-free log commits nothing); `kv_applied_step` gives
  `mvcc.LogNoLease x.log` from `kvInv`'s `LogNoLease γk.log0`; `kvTableOf_ne0` (`0 ∉` the table).
- `kv_certPre_G`/`batchStep_plainMG` take the lease-freeness and `0 ∉ lt.ids`, so the revocation's
  `revokeLog` is the model's entry log (`leaseDels`/`revokeChanges` both `[]`).
- `srvGrantable` carries `lessorModeIs (decide (E.lm = .mono))` (NewServer proves it from
  `bootCfg_lm`); `revokeOwn_take`: `rdAt ∗ srvGrantIf E ⊢ revokeOwn E rq ∗ (revokeOwn E rq -∗ rdAt)`
  at `plainOrCmpG E.lm rq`.
- `srvRest_applyPGR`: the rest after a revocation (`revokeRestA`/`revokeIdsA` over the grant's;
  `restRevoke` commutes with `restLeasesWith`; the live set's `T.filter`). `applyEntryNormal`'s
  auth-off sites supply `revokeOwn` from the applier row's `rdAt`, take it back, and use it;
  the auth-on sites still admit no revocation (`plainCover`).

**Stopped: X6's discharge needs the revoke response's header facts, which the answer drops.**
`lessorRevokeOk`'s post `leaseRevokeAns` needs, on success, `leaseHdrAns`: the header pointer
read-only, its id fields owned, its revision read-only, not `0`, reached (`etcdReached`, from a
certified log as `srvRevLb`). The apply layer's revoke answer is `dispatchAnswer`'s
`revokeOutcomeIs`: at `.applied`, only `∃ h, Header ↦ h ∗ ⌜h ≠ null⌝`, `applyErrIs`,
`revokeErrIs`; it takes no `E`, so it cannot hold the header's certificates (`idxCert E.γ.idx`,
`certOk E.γ`). The backend's proof has them (`newHeader.spec` gives `hdrFields`, the revision at
`log.length - 1`, `certOk`; `kvOwn` gives `idxCert`) and drops them. The grant's answer went the
same way and was carried separately (the lease-grant plan's 2.6: `grantAnswer E` in `grantRes`,
`grantArM` on the result, `grantAnsM` in `appliedOkM`). Options:
- (a) a revoke twin of 2.6: `revokeAnswer E rq resp err` (the header as `grantHdr E log'`) in the
  revoke posts' `revokeResAfter`, `revokeArM`, `revokeAnsM` in `appliedOkM`, through `Apply`,
  `applyEntryNormal`'s result and the wait. Strengthens the apply package's revoke posts and
  `appliedOkM` (the server's request-side vocabulary). Recommended: it is the established pattern.
- (b) `revokeOutcomeIs`/`dispatchAnswer` take `E` and hold `grantHdr` directly: fewer new
  predicates, but `dispatchAnswer` is E-free everywhere today (every KV answer).
- (c) X6's spec without the header (post: an error, or `resp ≠ null` with the revocation applied),
  discharging only a weaker contract than `lessorRevokeOk`: not the plan's.

**Decided (the user, 2026-11-04): (a).** The revoke header mirrors the lease-grant plan's 2.6: a
`revokeAnswer E` carrying `grantHdr E log'`, in the revoke posts' `revokeResAfter`, then
`revokeArM`, then a `revokeAnsM` conjunct in `appliedOkM`, carried through `Apply`,
`applyEntryNormal`'s result and the wait. Then X6.

**Done under (a) (2026-11-04).**
- *The apply layer.* `revokeOutcomeIs`'s applied arm drops the header (its ownership moved);
  `apply.revokeRespIs E r` (not `null`, the header `grantHdr E log`) and `apply.revokeAnswer E rq resp
  err` (`grantAnswer`'s mirror; `revokeAnswer_err`); `revokeResAfter E rq T rs resp err o` carries
  it. The backend's `LeaseRevoke` keeps `newHeader`'s facts on the live arm (the header at
  `revokeLog log id`, certified by `kvWriter_cert`); the not-found arm and the auth and corrupt
  rejections answer with their error. `dispatch.spec` gives `revokeAnsR E rq ar` (`grantRes`'s
  mirror; `revokeAnsR_not_revoke`, `revokeAnsR_null`), `Apply.spec`/`specRec` `revokeAnsRA`.
  (`revokeRes` was taken: `revokePre`'s resources.)
- *The server.* `revokeArM` in `resultIsW`, `resultIsWOn`, `resPostM` (`_of_res`, `_not_revoke`,
  their `W` forms; `adminKindOk_nonRevoke`); `revokeAnsM` in `appliedOkM` (`revokeAnsM_of_ar` in
  `raftRequest`). `applyEntryNormal`'s sites carry it as the grant's.
- *A gap of C2a fixed:* `rqSmall` had no revocation clause, so `rqShape` of a revocation required
  `putOk` at every log (unprovable); its `.leaseRevoke` clause is `putOk log` (`rqSmall_of_small`
  unchanged).
- *X6.* `LeaseRevokeRequest.GetID` translated (`etcdserverpb.toml`), specified and proved;
  `EtcdServer.LeaseRevoke.spec` (`srvRevokesLeases E ρ`: `ρ.rd.kv.lm = .revocable ∧ E.authOn =
  false`; the request `leaseRevokeReqRO r id`: not `null`, `ID ↦□ id`; post: an error with
  `applyErrIs`, or the response `leaseRevokedResp`: its header at a reached revision, the ids owned)
  proved over `requireAuthInfo`, the span, `raftRequest` (`reqPropOk`'s revocation form) and the
  type assertion; linked (`EtcdServer.wp_LeaseRevoke`).

**Stopped: the mode-gated `lessorRevokeOk` discharge needs `r ≠ null` from the trusted request.**
Go's `LeaseRevoke` with a nil `r` proposes an empty request, whose answer is not a
`*LeaseRevokeResponse`: the type assertion panics, so the spec needs `r ≠ null`. `lessorRevokeOk`'s
pre gives `v3rpc.leaseRevokeReqIs r id`, which is `pbLeaseRevokeRequest.recv` (trusted, in
`client/v3/InvLease.lean`; `Results.lean` equates them by `rfl`) and lacks it. The grant had the same
gap, closed by amendment (H) (`⌜r ≠ null⌝` first in `pbLeaseGrantRequest.recv`, true of Go: the
generated handler decodes into its own fresh allocation). Proposed, the same for the revocation:
`⌜r ≠ null⌝` first in `pbLeaseRevokeRequest.recv` and `v3rpc.leaseRevokeReqIs`. Then
`lessorRevokeOk_of_server` follows `lessorGrantOkLive_of_server` (`leaseHdrAns` from
`leaseRevokedResp`).

**Approved trusted-definition change (the user, 2026-11-04), amendment (H) for the revocation.**
`pbLeaseRevokeRequest.recv` (`client/v3/InvLease.lean`, trusted) gains `⌜r ≠ null⌝` first, and with it
`v3rpc.leaseRevokeReqIs`: true of Go, the generated handler decodes into its own fresh allocation
(`new(LeaseRevokeRequest)`). No axiom changes (the trust base stays 785 axioms, 6 sorries).

**Done: the mode-gated discharge.** `v3rpc.lessorRevokeOk_of_server` (`ServerLeaseRevoke.lean`,
`lessorGrantOkLive_of_server` mirrored): in a cluster that revokes leases (`srvRevokesLeases`), from
`EtcdServer.LeaseRevoke.spec`, `lessorRevokeOk s E S` (`leaseHdrAns` from `leaseRevokedResp`, the
error by `srvErrIs_of_applyErrIs`); linked as `v3rpc.lessorRevokeOk_server` (`v3rpc/Results.lean`).
The ungated `lessorRevokeOk` (any lease mode) stays an undischarged premise of the client results
(said in its docstring). Part X-b is complete; Part E not started.

## Plumbing: Part E (2026-11-04)

**Done.**
- *The example translated* (`017d6025d9`): project `leaseexpiry` in `etc/goose.py` (as `leasegrant`),
  `Code/`/`GeneratedProof/…/examples/etcd/leaseexpiry.lean`; `etc/gen-init.py`'s `ROOTS` and
  `PROGRAMS` (its `Init.lean` and `PkgTable.lean`, generated); `Base.lean` (package fact `True`),
  `Defs.lean` (leasegrant's premises at this example's addresses `127.0.0.1:23976`/`23986`, data
  directory `leaseexpiry.etcd`), `holdToken` specified and proved. The Go test passes (`Main` 3.2 s,
  the second lease expires too).
- *E3's first half, the user's "generated ids only"*: `EtcdServer.LeaseGrant.spec` takes
  `ρ.rd.kv.lm = .revocable → id0 = W64 0` (a weaker spec; its proof unchanged). Carried to the
  client: `v3rpc.lessorGrantOkG s E S G R` has a request filter `R : w64 × w64 → Prop` (default
  `True`, `⌜R m⌝` in its precondition), `v3rpc.LeaseServer.LeaseGrant.spec` takes `R` and `⌜R m⌝`;
  `lessorGrantOkLive_of_server`/`_server` give the contract at any `R` that has `ID = 0` in the
  revocable mode, `lessorGrantOkL_of_server`/`_server` take `ρ.rd.kv.lm ≠ .revocable`;
  `client.etcdLeaseGrantSpecGR G R` (`⌜R m⌝ ∗ etcdLeaseGrantSpecG G m Φ`), `etcdLeaseGrantSpecLive`
  is it at `ID = 0` (clientv3's `Grant` sends `(ttl, 0)`, `lessor.Grant.spec`);
  `etcd_leaseGrantHandlerOkGR` (and `…OkG` its corollary at `True`). `etcdLeaseGrantSpecLive_any`
  and `isGrpcRpc_leaseGrantLive_any` (unused) removed: the old contract covers any `ID`.
  `etcdstart.kv_lease_served` takes `ρ.rd.kv.lm = m` (was `lg = decide (m ≠ none)`; its callers
  have it).

**Proposed, awaiting the user (trusted): E2, the restated `EtcdServer.leaseTimeToLive.spec`.**
New vocabulary in `LeaseRead.lean` (the trusted spec's file):

```lean
/-- **The lease-TTL row** (the lease-expiry plan's E2, the user's: single member, first
incarnation): the cluster has one voter, and its lease mode is not `none`, which only a new
cluster's first incarnation has (the restart contracts, `memberBuiltR`/`BuildServer.specRestart`,
fix `.none`; a restart stage that admits leases must revisit `leaseTimeToLive.spec`). -/
def leaseTTLRow (ρ : ReqNames) : Prop :=
  (∃ v : w64, ρ.raft.raft.vs = [v]) ∧ ρ.rd.kv.lm ≠ .none

/-- **`errors.Is(err, target)` answers `true`** (Go's walk of `err`'s exact tree, the relation
`errors.Is.spec` posts). -/
def errIsTrue (err target : GoInterface) : IProp GF :=
  iprop(∃ (S : GoInterface → Prop) (I : GoInterfaceOk → Bool → Prop)
      (U : GoInterfaceOk → List GoInterface → Prop),
    _root_.Perennial.errors.errorWalkTree S I U target ∗
    ⌜S err ∧ exactRels I U ∧ _root_.Perennial.errors.IsWalk true I U target err true⌝)
```

The spec (changes: the binder `m`, `lease.lessorLb γl m` in the precondition, the two `□ (⌜leaseTTLRow ρ⌝ -∗ …)`
facts in the postcondition):

```lean
abbrev EtcdServer.leaseTimeToLive.spec : Prop :=
  leasePeersOk →
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (γl : GName)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (r : Loc) (dq : DFrac)
    (v : etcdserverpb.LeaseTimeToLiveRequest) (m : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReqM E.authOn s E ρ ∗ isServerReadM E.authOn s E γr ∗ srvLessorRd s γl ∗
      context.isContext ctx cd ∗ lease.lessorRdPool γl ∗ threadTok ∗ ⌜threadBound GF ≤ 2 ^ 30 - 1⌝ ∗
      lease.lessorLb γl m ∗ r ↦{dq} v }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"leaseTimeToLive"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); threadTok ∗
      r ↦{dq} v ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ w : etcdserverpb.LeaseTimeToLiveResponse, resp ↦ w ∗
          ⌜w.Header' ≠ null⌝ ∗ ⌜w.ID' = v.ID'⌝ ∗ (∃ hv : etcdserverpb.ResponseHeader, w.Header' ↦ hv) ∗
          □ (⌜leaseTTLRow ρ⌝ -∗ ∃ i : Nat, ⌜m ≤ i⌝ ∗ lease.leaseTTLAt γl i v.ID' w.GrantedTTL')) ∨
       (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err ∗
          □ (∀ e : GoInterfaceOk,
              globalAddr go_etcd_io.etcd.server.v3.lease.ErrLeaseNotFound ↦□ GoInterface.ok e -∗
              errIsTrue err (GoInterface.ok e) -∗ ⌜leaseTTLRow ρ⌝ -∗
              lease.leaseAbsentFrom γl m v.ID'))) }}
```

Docstring addition (why it is true of Go, `v3_server.go:636-696`): *Found* (`GrantedTTL`): on the
leader path the response's `GrantedTTL` is `le.TTL()`, the `ttl` field of the lease `Lookup`
returned from this member's lessor at an index no older than `m` (the caller's bound: the lookup is
after the call), which the history records (`ttlTie`); on the forwarded path a `200` comes only from
a peer serving etcd's lease handler, which, the cluster's only member being this one, answers from
this lessor too, later. *Not found* (`errors.Is(err, ErrLeaseNotFound)`: Go's returned errors are
leaves, so `err` is the lessor's `ErrLeaseNotFound`): on the leader path `Lookup` returned `nil` at an
index no older than `m`; on the forwarded path (`isLeader()` false at the check; a `404`, which the
examples' raft-only peer listeners always answer, or a lease handler's not found) the member had not
yet led: a sole voter's first incarnation applies no lease before raft stores its leadership
(`r.lead` is stored from the `Ready` before its committed entries are applied, `raft.go:190-202`;
before the first election only the bootstrap's conf changes are committed) and a sole voter never
loses it, so the lessor had no lease at all at the check's index (`≥ m`). Without the row both are
false: a follower forwards to another member's lessor; a restarted member applies its replayed
grants before any election and forwards, getting `404` for a live lease (review round 3, R7).
Callers: `EtcdServer.LeaseTimeToLive.wp_proof` passes its `lessorLb γl m` (it has one, from
`lessorTTLOk`'s precondition); `ttlAns` and `leaseTTLOut` carry the two facts (the handler's
not-found arm from `errIsTrue`, which it has from its `errors.Is` call: `Hw1` with `Htree`, `HS`);
the client's TTL spec for the revocable mode (`etcdLeaseTTLSpecL γl`: not-found `TTL = -1 ∧
GrantedTTL = 0` gives the absence, found gives the TTL at an index) registered by
`kv_lease_served`'s revocable arm.

**Proposed with it (not trusted): `Main.spec`** = `leasegrant`'s with `leaseexpiry`'s package and
addresses, `leaseexpiry.etcd`, and **no `lease.leasesNoExpiry`**; the proof at `.revocable`
(`alloc1 … .revocable (lease.runCfg_revocable …)`), resting on the gated `srvGrantOpen_open` and
on `srvRevokeOpen` (both reached through `lease.runCfg … .revocable`). **No sorry discharges
`srvRevokeOpen` yet** (X-a stated it as an open premise; nothing in the tree proves it): the result
needs a new marked `sorry`, `srvRevokeOpen_open` beside `srvGrantOpen_open` (or
`EtcdServer.revokeExpiredLeases.wp_proof` as one, the P1 decision's form), reached by leaseexpiry's
results only: the trust base would go from 6 to 7 sorries. The P1 decision (2026-11-04) approved
such a sorry; to be confirmed when `Main`'s proof lands. It raises
`etc/bounds-baseline.txt` as `leasegrant`'s did (`spec-thread` +1, `spec-receipt` +2: the thread and
receipt bounds of `Main.spec`): for approval when it lands. A collection
`etc/tcb-collections/leaseexpiry.txt` (roots `examples/etcd/leaseexpiry`) then.

**E3's second half: designed, not built (for review).** `Main`'s two uses need "absent stays
absent" and "the TTL of `id` is its grant's":
- (b) *Distinct grant ids in the log.* `LeaseGrant`'s generated id: `Next()`'s `idFresh γi u`
  (today dropped) is kept and handed to the proposal; the grant form of `reqPropOk` (revocable mode)
  carries it, and the proposal's commit step deposits it in `kvInv`: a new conjunct `[∗ list] u ∈ U,
  idFresh γk.ids u` with the log's grant ids `U.map (· &&& 2^63-1)`. Exclusivity of `idFresh` makes `U`
  duplicate-free; one generator (`ids.pfx` fixed, the single-member row) makes the masked ids
  distinct (`pfx ||| (x &&& (2^48-1))` differ in the low 48 bits). In a multi-member cluster two
  members' prefixes can differ only in bit 63 (review round 1's preference), so the law is stated
  under the row.
- (c) *The lessor's history tied to the applied log.* Each snapshot's live set is the applied
  table of a prefix of the log (`appliedTable`: grant adds, revoke removes), the prefixes monotone in
  the index: one more component of the lessor history (`LSnap`'s index into the applied log), kept by
  `Grant`/`Revoke` at the apply thread (which holds the applied log, `leasesLive`). With (b): `id`
  enters the live set once, by its grant entry, and never after its revocation; its lease object is
  the grant's, so its recorded TTL is the grant's (`≥ 1` for `Grant(1)`, R5's `leaseGrant_ttl`).
  The reply's fact `grantLiveG` must then also carry the recorded TTL `≥` the request's (the
  `G`/`R` pair above takes the request; or the reply's `TTL` field, which the backend sets to
  `l.TTL()`).
- `Recover` (snapshot restore) breaks (c) unless its ids are the snapshot's applied table: S3/S4's
  `lease.imageOk`, which the revocable mode reaches only with S4 (today `specSnapM` takes `E.lg =
  false`).
- Size: `kvInv` (a definition the server's exported statements use; about 25 openings), the grant's
  proposal (`reqPropOk`, `kv_prop_au_grant`), `LeaseGrant`'s proof, the lessor history (`LSnap`,
  `lessorRdBody`, `grant_hist`, `revoke` step, `recover_hist`), `srvRest`'s grant/revoke cases. The
  user decided the invariant's content; the carrier (`kvInv`'s conjunct and the history's prefix
  index) is a strengthening of `kvInv` and of the lessor history: for review before plumbing.

**`srvRevokeOpen`: what discharging it needs** (the body is `EtcdServer.revokeExpiredLeases.spec`;
analysis, nothing changed).
1. *The spec's precondition* (the X-b open item, rechecked against Go `server.go:860-905`): the
   request path's `isServerReq s E ρ` with a binder `ρ` and the mode `ρ.rd.kv.lm = .revocable`
   (`LeaseRevoke.spec`'s `srvRevokesLeases`; the grant guard gives only `lg ∧ auth off`); the read
   side for `ensureLeadership` (`isServerReqM`/`isServerReadM`, `srvReadReader s γr`, `srvLgReader
   s`, `threadTok`, the thread bound); `srvAuthAt s E`; per inner goroutine `srvLeadTimeReader s`,
   `E.RD`, `□ (|==> idCred ρ.ids 1)`; `s.ctx`'s context fact (`srvGoAttachOk` has only the field
   `srvCtxAddr s ↦□ c`: a `context.isContext c cd` for the server's root context, from `NewServer`'s
   `context.WithCancel`); and from `run`, the outer `GoAttach`'s `srvGoRes s ∗ srvLgReader s`
   (returned to `run`).
2. *Callee specs that do not exist*: `authStore.WithRoot` (not translated; at auth off it returns its
   argument after `IsAuthEnabled`, which takes the auth store's `enabledMu` read lock: a slot);
   `leaseExpired.Inc()` (a package `prometheus.Counter`, its initializer axiomatized: a
   `Counter.Inc` contract like `CounterVec.WithLabelValues`'s `Inc`); `zap.Logger.Warn` with
   `zap.Uint64`/`zap.String`/`zap.Error` and `fmt.Sprintf("%016x")` (the warn paths).
3. *Threads (P1)*: `GoAttach.spec` gives `f` only `P` and takes the caller's token into the wait
   group, so the outer goroutine has no `threadTok` for `ensureLeadership` and no `srvGoRes` for the
   inner `GoAttach`es, and each inner goroutine has none for `LeaseRevoke` (whose `raftRequest`
   forks nothing but takes slots) — Perennial's thread tokens by level (`notes/perennial-changes.md`,
   bounds-plan D2(b)): the forked goroutine keeps levels `≥ 1`, from which it borrows `wgMu`'s,
   the logger's, the read loop's and the auth lock's reader slots from server-owned pools. Also a
   bound on how many rounds overlap: a round returns with up to `maxPendingRevokes` goroutines still
   in `LeaseRevoke` (bounded in time by the request timeout, not in number by anything the logic
   sees), and `run` starts a round every expiry tick: the pools must be refilled by the inner
   goroutines' returns (`<-c` and `Done`), so the counted bound is the wait group's, not the round's.
4. *The channel `c`*: a buffered `chan struct{}` of capacity `maxPendingRevokes` used as a
   semaphore (`c <- struct{}{}` before each fork, `<-c` at each goroutine's end): its bag carries the
   slots of point 3 back (the "inner pool's bound" of P1).
5. *`select` on `s.stopping`*: `srvGoAttachOk`'s `isStopChanInternal` (exists).
Then `srvRevokeOpen` is proved (`srvRevokeOpen_spec`'s converse from
`revokeExpiredLeases.wp_proof`) and passed in leaseexpiry's linked file only, as `srvGrantOpen_open`
is in leasegrant's; until then the marked sorry above stands in.

**Decided (the user, 2026-11-04, on the above):**
- `Main.spec` as proposed, with `etc/bounds-baseline.txt` +1 `spec-thread`, +2 `spec-receipt`, the
  collection `etc/tcb-collections/leaseexpiry.txt`, and the P1 sorry (approved in principle):
  trust base 6 → 7 sorries, reached only by leaseexpiry. Its form: `srvRevokeOpen_open` (a theorem
  `srvRevokeOpen` by `sorry`, beside `srvGrantOpen_open` in `EtcdServer__run.lean`), not
  `EtcdServer.revokeExpiredLeases.wp_proof`: the latter's spec will be restated (the analysis'
  points 1-5 add to its precondition), and a proof file would put the sorry into the server's
  `Link.lean`; the premise form keeps it out of every result but leaseexpiry's, as
  `srvGrantOpen_open` is.
- E3's second half: (b) and (c) as designed.
- **E2 not approved**: the row `vs = [v] ∧ lm ≠ none` is not the decided one (revisions 2/3: this
  member the cluster's only member, no membership change admitted; round 3: first incarnation). It
  does not say `v` is this member, and it encodes the first incarnation by a convention of the
  restart contracts. Revised below, for a fresh review, then the user.

**E2, revision 2 (2026-11-04).** What the names give:
- `ρ.raft.raft.vs` (`SrvRaft.vs`) is the voters the cluster started with; its configuration is
  `Membership.simple (listToSet vs)` (`NodeApiVocab.lean:222`: those voters, no learners, no joint
  configuration) at index `0` (`srvClusterOk`'s `confAt … 0`), and at every index of a committed
  log (`srv_confAt_simple`, `SrvRaftLog.lean:987`, proved from the server's log invariant: every
  conf entry is a boot `AddNode` of a voter, `ccPolOk`, which the rule keeps, `srvRuleKeeps`). So
  "no membership change admitted" is a theorem of every server here, and `vs = [mid]` with `mid`
  this member's id (the `memberID` field, `srvReqFieldsAt`'s `memberID ↦□`) says "this member is
  the cluster's only member, ever".
- *First incarnation, explicitly*: `ρ.ids.inc = 0`. `IdNames.inc` is the incarnation number of the
  member's id key `(pfx, inc)` (R2c, `notes/restart-plan.md`); the cluster's allocation gives each
  boot member the key `(pfx, 0)` (`srvMemberBoot_alloc`, `NewServerAlloc.lean:352`, with its
  exclusive entry `(pfx, 0) ↪[cnt] …`), so another incarnation of the member, which must register
  a key of its own in the same map, cannot have `inc = 0`. The first incarnation is the one
  `NewServer` boots from a fresh WAL directory (`walDirFresh`) with an empty lease bucket
  (`NewLessor`'s premise, `⌜(r.lookup "lease").getD ∅ = ∅⌝`), so its lessor starts empty and its
  committed log holds only the bootstrap's conf changes until a leader commits more.
  Alternatives considered: `lm ≠ .none` (a convention of the restart contracts, which fix `.none`:
  rejected); a new persistent ghost token minted by the first-boot path (as explicit, but a new
  name to thread through `NewServer`'s post and `etcdstart`; `inc` already exists and is already
  exclusive per key).

The row and the spec (revision 2; the rest of the spec as revision 1):

```lean
/-- **The lease-TTL row** (the lease-expiry plan's E2, the user's): the server `s` is its cluster's
only member (`mid`, its `memberID`, the one voter the cluster started with; the membership never
changes, `srv_confAt_simple`) in its first incarnation (its id key's incarnation `0`, which only the
cluster's allocation gives, `srvMemberBoot_alloc`). -/
def leaseTTLRow (s : Loc) (ρ : ReqNames) : IProp GF :=
  iprop(∃ mid : w64, structFieldRef EtcdServer go!"memberID" s ↦□ mid ∗
    ⌜ρ.raft.raft.vs = [mid] ∧ ρ.ids.inc = 0⌝)
```

In the postcondition, `⌜leaseTTLRow ρ⌝ -∗` becomes `leaseTTLRow s ρ -∗` in both arms:

```lean
          □ (leaseTTLRow s ρ -∗ ∃ i : Nat, ⌜m ≤ i⌝ ∗ lease.leaseTTLAt γl i v.ID' w.GrantedTTL')) ∨
       (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err ∗
          □ (∀ e : GoInterfaceOk,
              globalAddr go_etcd_io.etcd.server.v3.lease.ErrLeaseNotFound ↦□ GoInterface.ok e -∗
              errIsTrue err (GoInterface.ok e) -∗ leaseTTLRow s ρ -∗
              lease.leaseAbsentFrom γl m v.ID'))) }}
```

**Progress after the decisions (2026-11-04).**
- `Main.spec` (`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/leaseexpiry/Main.lean`) written as
  approved: leasegrant's without `lease.leasesNoExpiry`, the leaseexpiry package and addresses. Its
  proof waits for E2 (the not-found arm) and E3 (c) (absent stays absent): no proof file yet.
- `srvRevokeOpen_open` (`EtcdServer__run.lean`, beside `srvGrantOpen_open`): the approved P1
  `sorry`. Trust base 6 → 7 sorries; until `Main`'s proof is linked no result reaches it.

**E2, revision 3 (2026-11-04, after a fresh `spec-reviewer`'s review of revisions 1-2).** The
review: the leader path, the meaning of `vs = [mid]` (only member, no learner, no membership change:
`SrvRaft.cfg = listToSet vs`, `Membership.simple`, `srv_confAt_simple`), the forwarded not-found
argument (`updateLead` before the `applyc` send, `raft.go:190-202`; a sole voter keeps itself
active) and `errIsTrue` (with `exactRels`, `isWalk_det`; the forwarding loop returns only
`ErrLeaseNotFound`, a leaf) hold. Its findings and what revision 3 does:
- *R1 (soundness): an outsider's raft message.* rafthttp's handler checks only the cluster id and
  `Process` steps any unknown `From`: a higher-term `MsgApp` from a non-member makes the sole voter a
  follower, it forwards to its own URL and reads `404` as "not found" for a live lease. **Excluded by
  the trusted transport contract** (decisions.md D21b (A): `Start`/`AddPeer` call `Process` only with
  messages of the cluster's ghost network, which only members' `rnMsgOk` sends fill): no new premise;
  the docstring names that contract as the margin (below).
- *R2 (soundness): the forwarded found arm.* `leasePeersOk` promises only that a `200` carries a set
  response, not that it is this member's lessor's answer; a foreign program at the member's peer URL
  meets it with any `GrantedTTL`. The found arm is needed (`Main` tells "expired, not yet revoked",
  `TTL = -1` from a negative `Remaining()`, from "not found" by `GrantedTTL ≠ 0`). **Proposed: a
  stronger `leasePeersOk`** (an approved premise: the user's call; its text below). The examples meet
  it trivially: their peer listeners never answer the path `200`.
- *C1 (completeness): the callers carry no `ρ`.* `ttlAns`, `leaseTTLOut`, `lessorTTLOk`,
  `raftLeaseRead` are over `s E γl`. Revision 3 keys the row on `s` (below), which they have; the
  facts go into `ttlAns`/`leaseTTLOut` as is. The proved wrapper's own errors (`requireAuthInfo`, the
  keys check, `ErrAuthOldRevision`, `v3_server.go:697-720`) must discharge the not-found implication
  vacuously: `errors.Is` of them against `ErrLeaseNotFound` is false (distinct error cells,
  `lease/Base.lean`'s `errVarCell`): a proof obligation of `EtcdServer.LeaseTimeToLive.wp_proof`.
- *A1 (abstraction): `ρ.ids.inc = 0`* is true only through non-local facts (`idIncarnation_alloc`
  posts no `inc ≠ 0`; `restartNames` fixes neither `cnt` nor `inc`; `NewServer.specG` takes
  `idShare ρ.ids` at any key) and uses the id generator's bookkeeping as the identifier of a start.
  **Replaced by `srvFirstStart s`**: a new persistent, sealed predicate of the server package, minted
  only by `NewServer`'s first-start branch (the one that takes `wal.bootRes cfg`, i.e. `walDirFresh`,
  and `NewLessor`'s empty lease bucket) and returned in its postcondition (to `memberBuilt`), with
  no other intro: "this server was built by `bootstrap` from a fresh WAL directory and an empty
  backend". It states the start, which is what the truth argument uses (raft's log at start is the
  bootstrap conf changes; the lessor starts empty), not the generator's counter.
  *Alternative* if `NewServer`'s postcondition must not change: keep `ρ.ids.inc = 0` with the
  reviewer's minimum, `inc ≠ 0` in `idIncarnation_alloc`'s postcondition and `ρ'.ids.cnt = ρ.ids.cnt
  ∧ ρ'.ids.inc ≠ 0` in `restartNames`, which makes it a local fact (still bookkeeping as identity).
- *M1:* the member id through `srvMemberIDAddr s` (as `srvHeaderFacts`); `errIsTrue` moves to
  `apply/Base.lean` beside `exactRels` (generic error vocabulary).
- Noted (not this spec's): `Main` also needs E3 (c) (the grant's recorded TTL `≥ 1`) and the
  client's `m` at or past the grant's index.

**Proposed, awaiting the user (trusted): E2, revision 3, exact text.**

`apply/Base.lean` (generic, beside `exactRels`):
```lean
/-- **`errors.Is(err, target)` answers `true`** (Go's walk of `err`'s exact tree, the relation
`errors.Is.spec` posts; with `exactRels`, `isWalk_det` makes the answer Go's). -/
def errIsTrue (err target : GoInterface) : IProp GF :=
  iprop(∃ (S : GoInterface → Prop) (I : GoInterfaceOk → Bool → Prop)
      (U : GoInterfaceOk → List GoInterface → Prop),
    _root_.Perennial.errors.errorWalkTree S I U target ∗
    ⌜S err ∧ exactRels I U ∧ _root_.Perennial.errors.IsWalk true I U target err true⌝)
```

The server package (an API module, sealed; minted in `NewServer`'s proof on the first-start branch):
```lean
/-- **The server `s` was started for the first time** (`NewServer`'s first-start branch:
`bootstrap` from a fresh WAL directory, `wal.bootRes`, and an empty backend, `NewLessor`'s empty
lease bucket): raft's log at start is the bootstrap configuration changes and the lessor starts
with no lease. Persistent; `NewServer`'s postcondition is its only introduction. -/
@[no_expose] def srvFirstStart (s : Loc) : IProp GF := ...
```

`LeaseRead.lean` (the trusted spec's file):
```lean
/-- **The lease-TTL row** (the lease-expiry plan's E2, the user's: this member is the cluster's
only member, and in its first incarnation): the cluster's voters are exactly this member (`vs`, the
boot voters, are the configuration at every committed index, `srv_confAt_simple`, with no learner:
no membership change is admitted), and the server was started for the first time. -/
def leaseTTLRow (s : Loc) (ρ : ReqNames) : IProp GF :=
  iprop(∃ mid : w64, srvMemberIDAddr s ↦□ mid ∗ ⌜ρ.raft.raft.vs = [mid]⌝ ∗ srvFirstStart s)
```

The spec (revision 1's, with `leaseTTLRow s ρ -∗` for `⌜leaseTTLRow ρ⌝ -∗` in both facts):
```lean
abbrev EtcdServer.leaseTimeToLive.spec : Prop :=
  leasePeersOk →
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (γl : GName)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (r : Loc) (dq : DFrac)
    (v : etcdserverpb.LeaseTimeToLiveRequest) (m : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReqM E.authOn s E ρ ∗ isServerReadM E.authOn s E γr ∗ srvLessorRd s γl ∗
      context.isContext ctx cd ∗ lease.lessorRdPool γl ∗ threadTok ∗ ⌜threadBound GF ≤ 2 ^ 30 - 1⌝ ∗
      lease.lessorLb γl m ∗ r ↦{dq} v }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"leaseTimeToLive"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); threadTok ∗
      r ↦{dq} v ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ w : etcdserverpb.LeaseTimeToLiveResponse, resp ↦ w ∗
          ⌜w.Header' ≠ null⌝ ∗ ⌜w.ID' = v.ID'⌝ ∗ (∃ hv : etcdserverpb.ResponseHeader, w.Header' ↦ hv) ∗
          □ (leaseTTLRow s ρ -∗ ∃ i : Nat, ⌜m ≤ i⌝ ∗ lease.leaseTTLAt γl i v.ID' w.GrantedTTL')) ∨
       (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err ∗
          □ (∀ e : GoInterfaceOk,
              globalAddr go_etcd_io.etcd.server.v3.lease.ErrLeaseNotFound ↦□ GoInterface.ok e -∗
              errIsTrue err (GoInterface.ok e) -∗ leaseTTLRow s ρ -∗
              lease.leaseAbsentFrom γl m v.ID'))) }}
```

Docstring addition (why it is true of Go, `v3_server.go:636-696`), revision 1's with: *Found*, the
forwarded path: a `200` at the member's own peer URL is its lessor's answer (the strengthened
`leasePeersOk`), later than the call, so at an index `≥ m`. *Not found*, the forwarded path: the
member forwards only while `isLeader()` is false; a sole voter in its first start (`srvFirstStart`:
raft's log is the bootstrap's conf changes, the lessor empty) applies no lease before raft stores its
leadership (`raft.go:190-202`), and keeps it: no other member exists (`vs = [mid]`), and **the
trusted transport contract (decisions.md D21b (A)) delivers only the cluster's members' messages**,
so no outsider's higher term deposes it; hence the lessor had no lease at the check's index (`≥ m`).
Without the row both arms are false (a follower forwards to another member's lessor; a restarted
member applies replayed grants before its election and forwards).

`leasePeersOk`, strengthened (its docstring is its meaning; one sentence added after "...`http.go:116-156`)"):
> and a `200` from the peer URL of a member comes from that member's `leasehttp.NewHandler` over that
> member's own lessor (so its `LeaseTimeToLiveResponse` is that lessor's answer at the request's
> time),

and **False of** gains: "or a program serving a member's peer URL other than that member's
handler".

**E3 (b), done (`6bf78a792f`, 2026-11-04).** `LeaseGrant` keeps `Next()`'s claim right of the
generated id in the revocable mode and hands it to the proposal (`reqPropOk`'s grant/revoke form
carries `grantIdOwn γk rq`); the commit step (`kvGrantIds_snoc` in `kv_prop_au_*`) deposits it in a
new last conjunct of `kvInv`, `kvGrantIds γk L`: the log's revocable-mode grant ids are `U` masked,
`U` without repeat, each `u`'s claim right owned. **`kvInv` holds `idUnclaimed`, not `idFresh`**:
`idFresh`'s slot and prefix fact are member names, which `kvInv_congr` forbids, so only the issued
map's element is kept (the coordinator: fine). Laws: `kv_grantIds_nodup` (any prefix of the
requested log: its grant ids are `U.map mask`, `U.Nodup`) and `leaseIdMask_nodup_of_pfx` (distinct
ids of one prefix stay distinct after the mask).
- **Open item:** every grant id in the log has one prefix (`idPfx u = p` for all `u ∈ U`), from
  `idClusterOk` and the single-member row (one member, one generator). Not yet a law of `kvInv`:
  `kvGrantIds` would carry the prefix, or the masked distinctness is derived where the row is known.

**E3 (c), the design refined (2026-11-05, before building).** Instead of an index of each snapshot
into the applied log, the lessor's history carries **the ids it ever had** (`U`), a ghost set whose
authority is split between the lessor's reader invariant and the apply thread (the one caller of
`Grant` and `Revoke`):
- history invariant `histOnce hs` (both modes): an id's lease is one `*Lease` and its live indices
  are an interval (live at `i` and `k`, `i ≤ j ≤ k`: live at `j` with the same `l`); with `U` the
  union of the snapshots' ids;
- `lessor.Grant`'s spec takes the caller's half of `U` and, in the revocable mode, `id ∉ U`; it
  returns `U ∪ {id}` on success (and no `ErrLeaseExists`: not live);
- the apply thread keeps `U` = the ids of the applied log's successful grants; `id ∉ U` at a grant
  from (b) (distinct grant ids in the log, after the mask: the open item above);
- consequences, the laws `Main` uses: *absent stays absent* (`leaseAbsentFrom γl m id` with `id`
  live at some index `≤ m` gives absent at every index `≥` the absence) and *the TTL of `id` is its
  grant's* (one `*Lease` per id, its `ttl` field persistent: `leaseTTLAt γl i id t` gives `t =
  grantTTL mt ttl` of the grant, `≥ 1` for `Grant(1)`, `grantTTL_pos`);
- `Recover`: the first start's lessor is empty (`NewLessor`'s empty bucket), so `U = ∅`; a restart
  in the revocable mode needs S3/S4 (not reached).
Same content as the reviewed design ("the lessor's history tied to the applied log"), carried by a
set instead of per-snapshot indices.

**E2, revision 4 (2026-11-05, after a second fresh `spec-reviewer` round, on revision 3).** The
review found the Go argument for both arms true (the leader path needs no row; the forwarded
not-found: `isLeader()` false, `updateLead` before `applyc`, a sole voter keeps leadership under
CheckQuorum, `raft/raft.go:1299-1310`, and transfer is skipped for a single voter,
`server.go:1258,1316`), no Go bug, and five problems with revision 3, each addressed:
1. *The row still took `ρ`* (C1 not fixed: `ttlAns`, `lessorTTLOk`, `raftLeaseRead`, `leaseTTLOut`
   and the client contracts above them are over `s E γl`; `restartNames` keeps `ρ.rd.raft`, so `ρ`
   cannot tell a restart). Revision 4: **the row is over `s` only**; the voters are part of the
   first-start fact.
2. *`srvFirstStart`'s body was elided*, so "first incarnation" stayed a convention (a sealed `def`
   can be introduced by any `import all`; `walDirFresh` is not exclusive, `storage/WalDir.lean:9-12`).
   Revision 4 gives its body, about `s`'s own objects: its lessor's history begins with the empty
   snapshot, and its raft node is a node `StartNode` made (a persistent per-node-object fact,
   `nodeStartedFresh`, which only `StartNode`'s postcondition gives: `RestartNode` does not; the
   node object is the incarnation, `raft-durable-node-api.md`). It is returned **beside**
   `memberBuilt` (in `BuildServer.spec`/`StartServer`'s `memberUp`), not inside it (`memberBuiltR`
   is `∃ …, memberBuilt …`, so a restart contract would have to produce it).
3. *The stronger `leasePeersOk` is not needed* (dropped): under the row, a forwarded call means the
   lessor was empty at the `isLeader()` read, whatever the reply; so the found arm says "the TTL at
   an index `≥ m`, or absent from `m`". `Main` still concludes: a found reply with `GrantedTTL = 0`
   either contradicts the recorded TTL `≥ 1` (E3 (c)) or the lease is absent from `m`.
   `leasePeersOk` (also a premise of the `lease`/`leasegrant` closed theorems) is unchanged.
4. *"No membership change admitted" was implicit* (only through the model-wide `srv_confAt_simple`):
   revision 4 states it in the row (`srvStaticVoters s vs`: the configuration rule of `s`'s cluster
   is the static one, `γ.rule = srvRule 0 γ.boot`, and the voters `vs`).
5. Docstring: CheckQuorum, transfer skipped, no other member to send a snapshot; the leader path
   holds without the row; "a change admitting conf changes or restarts must revisit this spec".
   Collections resting on the strengthened spec: every collection reaching
   `EtcdServer.leaseTimeToLive.spec` (today `lease`, `leasegrant` and the server's: to list exactly
   with `etc/tcb-report.py --roots leaseTimeToLive --per-root` when it lands).

**Proposed, awaiting the user (trusted): E2, revision 4, exact text.** (Supersedes revision 3's.)

`apply/Base.lean` (generic, beside `exactRels`), unchanged from revision 3:
```lean
/-- **`errors.Is(err, target)` answers `true`** (Go's walk of `err`'s exact tree, the relation
`errors.Is.spec` posts; with `exactRels`, `isWalk_det` makes the answer Go's). -/
def errIsTrue (err target : GoInterface) : IProp GF :=
  iprop(∃ (S : GoInterface → Prop) (I : GoInterfaceOk → Bool → Prop)
      (U : GoInterfaceOk → List GoInterface → Prop),
    _root_.Perennial.errors.errorWalkTree S I U target ∗
    ⌜S err ∧ exactRels I U ∧ _root_.Perennial.errors.IsWalk true I U target err true⌝)
```

The raft node API (`Spec/go_etcd_io/raft/v3/Api.lean`'s vocabulary; an API change, interface diff
for review), given by `StartNode`'s postcondition only:
```lean
/-- **The node `n` was made by `StartNode`** (persistent): its raft log began as the bootstrap
log `ctxs` of the voters `vs`, from a fresh storage (`raftState γ id RaftState.init`); `RestartNode`
gives no such fact. -/
@[no_expose] def nodeStartedFresh (n : Loc) (γ : Cluster) (vs : List w64) (id : w64) : IProp GF
```

The server package (`Proof/go_etcd_io/etcd/server/v3/etcdserver/LeaseRead.lean`, beside the trusted
spec's vocabulary; minted in `NewServer`'s proof, returned beside `memberBuilt`):
```lean
/-- **`s`'s voters are `vs`, statically** (persistent): the configuration rule of `s`'s raft
cluster is the static rule over its bootstrap (`srvRule 0 boot`: no configuration change is
admitted), whose voters are `vs`, no learner. -/
def srvStaticVoters (s : Loc) (vs : List w64) : IProp GF :=
  iprop(∃ γ : ServerRaftNames, srvRaftNamesOf s γ ∗
    ⌜γ.raft.vs = vs ∧ γ.rule = srvRule 0 γ.boot⌝)

/-- **`s` is in its first start** (persistent): its lessor's history begins with the empty
snapshot, and its raft node was made by `StartNode` (`nodeStartedFresh`). -/
def srvFirstStart (s : Loc) : IProp GF :=
  iprop(∃ (γl : GName) (n : Loc) (γ : ServerRaftNames) (id : w64),
    srvLessorRd s γl ∗ lease.lessorAt γl 0 (∅, ∅, ∅) ∗
    srvRaftNamesOf s γ ∗ srvNodeAddr s ↦□ n ∗ nodeStartedFresh n γ.raft.cl γ.raft.vs id)

/-- **The lease-TTL row** (the lease-expiry plan's E2, the user's: this member is the cluster's
only member, no membership change is admitted, and it is in its first start). -/
def leaseTTLRow (s : Loc) : IProp GF :=
  iprop(∃ mid : w64, srvMemberIDAddr s ↦□ mid ∗ srvStaticVoters s [mid] ∗ srvFirstStart s)
```
(`srvRaftNamesOf s γ` and `srvNodeAddr s` stand for the server's existing persistent tie of `s` to
its raft names and its node field, whatever their names are in `InvServer`; to be fixed to the
existing names when plumbed, no new content.)

The spec (revision 1's, with `ρ` unused by the row):
```lean
abbrev EtcdServer.leaseTimeToLive.spec : Prop :=
  leasePeersOk →
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (γl : GName)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (r : Loc) (dq : DFrac)
    (v : etcdserverpb.LeaseTimeToLiveRequest) (m : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReqM E.authOn s E ρ ∗ isServerReadM E.authOn s E γr ∗ srvLessorRd s γl ∗
      context.isContext ctx cd ∗ lease.lessorRdPool γl ∗ threadTok ∗ ⌜threadBound GF ≤ 2 ^ 30 - 1⌝ ∗
      lease.lessorLb γl m ∗ r ↦{dq} v }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"leaseTimeToLive"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); threadTok ∗
      r ↦{dq} v ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ w : etcdserverpb.LeaseTimeToLiveResponse, resp ↦ w ∗
          ⌜w.Header' ≠ null⌝ ∗ ⌜w.ID' = v.ID'⌝ ∗ (∃ hv : etcdserverpb.ResponseHeader, w.Header' ↦ hv) ∗
          □ (leaseTTLRow s -∗
              (∃ i : Nat, ⌜m ≤ i⌝ ∗ lease.leaseTTLAt γl i v.ID' w.GrantedTTL') ∨
              lease.leaseAbsentFrom γl m v.ID')) ∨
       (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err ∗
          □ (∀ e : GoInterfaceOk,
              globalAddr go_etcd_io.etcd.server.v3.lease.ErrLeaseNotFound ↦□ GoInterface.ok e -∗
              errIsTrue err (GoInterface.ok e) -∗ leaseTTLRow s -∗
              lease.leaseAbsentFrom γl m v.ID'))) }}
```

Docstring addition (why it is true of Go, `v3_server.go:636-696`): *The leader path* (`isLeader()`
true at the check), without the row: `Lookup` runs after `waitAppliedIndex`, so at an index `≥ m`;
found, `GrantedTTL` is `le.TTL()`, the lease's `ttl` field, written only by `Grant` before the lease
enters the map (`lessor.go:301-302`; `ttlTie`); not found, `Lookup` returned `nil`. *The forwarded
path* (`isLeader()` false), under the row: `s`'s first start (`srvFirstStart`: its node made by
`StartNode`, so its log began as the bootstrap's configuration changes, and its lessor empty)
applies no lease before raft stores its leadership (`r.lead` is stored from the `Ready` before its
committed entries are sent to the apply loop, `raft.go:190-202,237`), and a sole voter
(`srvStaticVoters s [mid]`) keeps it once it has it: CheckQuorum counts the leader itself active
(`raft/raft.go:1299-1310`), leadership transfer is skipped for a single voter
(`server.go:1258,1316`), no other member exists to send a higher term or a snapshot, and the
trusted transport contract (decisions.md D21b (A)) delivers only the cluster's members' messages;
so at the check's index (`≥ m`) the lessor had no lease at all, whatever the forwarded reply
(`404`, which the examples' raft-only peer listeners answer, `etcdstart/common.go:172`, or another
answer). Hence the found arm's disjunction and the not-found arm (Go's returned errors are leaves:
`errIsTrue` with `ErrLeaseNotFound` means `err` is it). Without the row both are false (a follower
forwards to another member's lessor; a restarted member applies replayed grants before its
election and forwards: review round 3, R7). A change admitting configuration changes or restarts
with leases must revisit this spec.

Callers (proved, not trusted): `ttlAns`/`leaseTTLOut` carry the two `□ (leaseTTLRow s -∗ …)` facts
(over `s`, which they have); the wrapper `EtcdServer.LeaseTimeToLive.wp_proof` discharges the
not-found implication for its own errors (`requireAuthInfo`, the keys check,
`ErrAuthOldRevision`: `errors.Is` against `ErrLeaseNotFound` false, distinct error cells); `Main`
gets `leaseTTLRow s` from `StartServer`'s `memberUp` (`isServerBuiltC_mid` gives the member id
field, `ps = [id]`).

**E3 (c), decided (the user, 2026-11-05: route (A)).** Groundwork `6a515b550c` (`histOnce`,
`everIn` and their pure laws). **Trusted-statement change, relayed as approved by the coordinator, NOT YET MADE: it waits for the user's own confirmation** (an agent's relay is not consent for a trusted change): the trust-boundary axiom
`lease.NewLessor.wp_proof`'s postcondition gains `lease.leaseEver γl ∅`. It is ghost-only and true of
Go, because a fresh lessor has had no lease. It must go through the `axiom` skill before Freeze.
Then:
- `LessorRdNames` gains U's ghost name;
- `lessorRdBody` holds U's other half, with `histOnce` and "every id in the history is in U";
- `Grant` takes `leaseEver γl U` and, in the revocable mode, `id ∉ U`, and returns `U ++ [id]`;
- `Revoke`/`Attach`/`Detach` leave U unchanged;
- `Recover` takes its ids `∉ U` and returns `U ++ ids`;
- stage 2 is in `srvRest`, with the one-prefix fact (E3 (b)'s open item) as an explicit premise of
  the revocable mode. That premise is untrusted, true under the single-member row, and stays until
  E2 is approved.

**E2, revision 5 (2026-11-05, after a third fresh `spec-reviewer` round, on revision 4).** The
review found the Go argument right: the leader path, the forwarded path under the row
(`setLead` only from `updateLead`, before `applyc`; `isLeader` is `MemberID() == Lead()`; a sole
voter is always active, raft `raft.go:967-969,1299-1310`), restarts excluded (`StartNode` only when
`len(peers) > 0`, `bootstrap.go:580-583`; `NewServer.spec` covers only a first start), the callers
able to carry `□ (leaseTTLRow s … -∗ …)`, and the found arm's disjunction enough for `Main`. No Go
bug. What it found, and what revision 5 does:
- *S1: the row's facts were not tied to one cluster or one lessor* (`srvRaftNamesOf` does not exist;
  nothing pins one `ServerRaftNames` to `s`; `lessorPin` maps `γl → lp`, not back). Revision 5:
  **one set of existentials, through `s`'s node object**, and the spec's own `γl`:
  `nodeStartedFresh` (only `StartNode` makes it, for its fresh `n`) pins the cluster to `n`.
- *S2: `nodeStartedFresh` had no body.* Revision 5 gives one: the node's `isNode` and the cluster's
  `nodeBoot`, and a persistent lower bound of the node's driver history at its start,
  `nodeDriverFrom n (NodeDriverState.init …)` — a new raft-internal persistent fact minted only by
  `StartNode`'s proof (`RestartNode`'s driver starts elsewhere, `RestartNode.lean:39-45`).
- *A1: "no membership change admitted" was not stated*: `srvRule 0 boot` admits any validating
  change and every cluster has it (`rnEnvOk`, `InvRaftNode.lean:474-476`); the model is static only
  through `ccPolOk`/`srv_confAt_simple`. Revision 5 states the consequence: **at every committed
  index the configuration is `simple {mid}`** (raft's `confAt`).
- *C1: typing.* `rule`/`boot` are `SrvRaft`'s (now unused); `srvNodeAddr s` holds a `GoInterface`.
- *C2: where the row is returned:* a separate conjunct of `BuildServer.spec`'s and `StartServer`'s
  postconditions (first start), inside neither `memberBuilt` nor `memberUp` (both used by the
  restart example); a restart `NewServer` must not return it.
- *C3 (`Main`'s chain, not this spec):* a law `lessorAt γl i σ ⊢ lessorLb γl i` and E3 (c)'s TTL
  `≥ 1` law.
- *M1-M3, docstring:* cite `MoveLeader`'s member check (`server.go:1268-1271`) and raft's
  ignoring a transfer to self (`raft.go:1667-1669`), not only `server.go:1258,1316`; `≥ m` comes
  from `lessorLb`'s monotonicity, not `waitAppliedIndex`; `lessorAt γl 0 ∅` holds of every lessor
  today (`NewLessor` takes an empty bucket) and becomes meaningful once restarts recover leases.
- *Unverified by the reviewer* (the wrapper's proof obligations, not the spec's text): `errIsTrue`
  against `ErrLeaseNotFound` refutable for the leader path's other leaf errors (`ErrLeaderChanged`,
  `ErrTimeoutWaitAppliedIndex`) and the wrapper's own: distinct error cells.

**Proposed, awaiting the user (trusted): E2, revision 5, exact text.** (Supersedes revisions 3-4's.)

`apply/Base.lean`, beside `exactRels` (unchanged since revision 3):
```lean
/-- **`errors.Is(err, target)` answers `true`** (Go's walk of `err`'s exact tree, the relation
`errors.Is.spec` posts; with `exactRels`, `isWalk_det` makes the answer Go's). -/
def errIsTrue (err target : GoInterface) : IProp GF :=
  iprop(∃ (S : GoInterface → Prop) (I : GoInterfaceOk → Bool → Prop)
      (U : GoInterfaceOk → List GoInterface → Prop),
    _root_.Perennial.errors.errorWalkTree S I U target ∗
    ⌜S err ∧ exactRels I U ∧ _root_.Perennial.errors.IsWalk true I U target err true⌝)
```

Raft's node API (`Spec/go_etcd_io/raft/v3/Api.lean` vocabulary, sealed; `StartNode.spec`'s
postcondition gains it; an API change, its interface diff for review; `nodeDriverFrom` is a new
raft-internal persistent lower bound of a node's driver states, `StartNode`'s proof mints it at
`NodeDriverState.init`, `RestartNode`'s at its restart state):
```lean
/-- **The node `n` of the cluster `γ` was made by `StartNode`** (persistent): `n` is the node of
`id` in `γ` (`isNode`), `γ` was bootstrapped with the voters `vs` (`nodeBoot`), and `n`'s driver
began in the initial state, over a fresh storage (`nodeDriverFrom … NodeDriverState.init`), so its
log began as the bootstrap log. `RestartNode` gives no such fact. -/
@[no_expose] def nodeStartedFresh (n : Loc) (γ : Cluster) (N : Namespace) (vs : List w64)
    (ctxs : List (List w8)) (id : w64) : IProp GF :=
  iprop(isNode n γ N id ∗ nodeBoot γ N vs ctxs id ∗ ⌜id ∈ vs⌝ ∗
    ∃ (si : GoInterfaceOk) (K : GName), nodeDriverFrom n γ N (NodeDriverState.init (interface.ok si) K))
```

`Proof/go_etcd_io/etcd/server/v3/etcdserver/LeaseRead.lean`, the trusted spec's vocabulary:
```lean
/-- **The lease-TTL row** (the lease-expiry plan's E2, the user's): this member `mid` is the
cluster's only member, no membership change is admitted, and it is in its first start. Through
`s`'s own node object `n`: `n` was made by `StartNode` with the voters `[mid]` (its log began as
the bootstrap log), every committed index's configuration is `{mid}` alone, with no learner, and
the lessor `γl`'s history begins empty (true of every lessor today, `NewLessor` taking an empty
bucket; meaningful once a restart recovers leases). Returned by `BuildServer`'s and `StartServer`'s
first-start postconditions, as their own conjunct; a restart gives none. -/
def leaseTTLRow (s : Loc) (γl : GName) : IProp GF :=
  iprop(∃ (mid : w64) (n : Loc) (cl : Cluster) (ctxs : List (List w8)),
    srvMemberIDAddr s ↦□ mid ∗
    srvNodeAddr s ↦□ interface.mkOk (go.GoType.PointerType node.ty) #n ∗
    nodeStartedFresh n cl srvClusterN [mid] ctxs mid ∗
    □ (∀ (l : List LogEntry) (k : Nat), isCommittedLogLb cl l -∗ ⌜k ≤ l.length⌝ ={⊤}=∗
        confAt cl k (Membership.simple (GMap.listToSet [mid]))) ∗
    lease.lessorAt γl 0 (∅, ∅, ∅))
```

The spec: revision 4's, with `leaseTTLRow s γl` for `leaseTTLRow s` in both facts:
```lean
          □ (leaseTTLRow s γl -∗
              (∃ i : Nat, ⌜m ≤ i⌝ ∗ lease.leaseTTLAt γl i v.ID' w.GrantedTTL') ∨
              lease.leaseAbsentFrom γl m v.ID')) ∨
       ...
              errIsTrue err (GoInterface.ok e) -∗ leaseTTLRow s γl -∗
              lease.leaseAbsentFrom γl m v.ID'))) }}
```
(the rest of the triple exactly as revision 4).

Docstring addition: revision 4's, with: "at an index `≥ m`" justified by the caller's `lessorLb γl m`
and the history's monotonicity (not by `waitAppliedIndex`); the sole voter keeps its leadership:
CheckQuorum counts the leader active (raft `raft.go:967-969,1299-1310`), shutdown transfer skipped
for a single voter (`server.go:1258,1316`), `MoveLeader` rejects a non-member transferee
(`server.go:1268-1271`) and raft ignores a transfer to self (`raft.go:1667-1669`), no other member
exists to send a higher term or a snapshot (`confAt … {mid}`; the transport contract, decisions.md
D21b (A)); "a change admitting configuration changes or restarts with leases must revisit this
spec".

Not part of the trusted text, needed by `Main`: a law `lessorAt γl i σ ⊢ lessorLb γl i`; E3 (c)'s
"TTL is the grant's, `≥ 1`"; the wrapper's distinct-error-cell refutations.

**Decided (the user, 2026-11-05; the user's own answers to the coordinator, through
AskUserQuestion).**
1. E2 revision 5's exact text (above), including `nodeStartedFresh` in raft's API (interfaces
   regenerated, diff reported).
2. E3 (c) route (A): `lease.NewLessor.wp_proof`'s postcondition gains `lease.leaseEver γl ∅`
   (chosen over (B)). A trusted-statement change: through the `axiom` skill before Freeze.
3. `Main.spec` as proposed; the sorry `srvRevokeOpen_open`; `etc/bounds-baseline.txt` +1
   `spec-thread` / +2 `spec-receipt` (`etc/bounds-check.py --check --update` for exactly that); the
   collection `etc/tcb-collections/leaseexpiry.txt`.

## Applying E2 rev 5 and E3 (c) (2026-11-05)

Done (commit `2796280ca2`, downstream of the lessor not yet repaired):
- raft: `NodeNames.start` and `CfgNames`' last name; `nodeDriverFrom` (raft-internal, persistent:
  the node's driver state at its start, a discarded ghost variable), minted by `StartNode` at
  `NodeDriverState.init` and by `RestartNode` at its restart state; the sealed `nodeStartedFresh`
  (`InvNodeRule`), in `StartNode.spec`'s post, carried by `bootstrappedRaft.newRaftNode.spec` and
  `NodeStartSpec`.
- lease, E3 (c) stage 1: `LessorRdNames` gains U's name (`γr.2.2.2`; the mode is `γr.2.2.1`);
  `lessorRdBody` holds U's half with `histOnce` and `histIn` (every id a snapshot has, `snapHas`,
  is in U); `leaseEver γl U` the owner's half; `Grant` takes `leaseEver γl U` and
  `lessorModeIs γl true ∨ ⌜id ∉ U⌝` and returns `U ++ [id]` (`U` on an error); `Recover` takes its
  ids `∉ U` and returns `U ++ ids`; `Attach`/`Detach`/`Revoke` keep U (their history lemmas take
  `histOnce`'s step and "the new snapshot's ids are the last one's"); `NewLessor`'s post gains
  `leaseEver γl []`; the law `lessorAt_lb`. Pure laws `histIn_snoc{,_new}`, `histIn_mono`,
  `not_everIn_of_histIn` (`LessorHist`).
- server: `errIsTrue` (`apply/Base`), `leaseTTLRow` (revision 5's text, typed: A1 below) and its
  raft part `leaseTTLRowR s vs` with `leaseTTLRow_intro` (`LeaseRead`); `leaseTimeToLive.spec`
  restated (revision 5, with the docstring).

**Decided by the agent, pending the user** (also in `questions.md`):
- A1, the row's typing. `nodeStartedFresh`, `isCommittedLogLb` and `confAt` take a storage model;
  `LeaseRead` has none in scope. Options: (a) `∃ γ : SrvRaft` with `letI := srvStor γ`, the
  cluster `γ.cl` (the server's own instance, as `srv_confAt_simple` states it); (b) a section
  variable `[StorageModel GF]` (the spec would quantify over a model the server does not use).
  Recommendation and done: (a), the same content as the approved text.
- A2, `histIn`'s scope: every id of a snapshot's lease map **and** item map (`snapHas`), so that
  "`U = []`" pins a snapshot to `(∅, ∅, ∅)` (with `ttlTie`); keeping it is an `Attach` of a live
  id, `Detach`'s and `Revoke`'s subsets (`Revoke`'s items are of live ids, `leaseClosers`' `HIL`).
- A3, the row's `γl` against the built server's `E.γ.leases` (inside `memberBuilt`/`memberUp`'s
  existentials; `envAgree` does not fix it, and `srvLessorRd` has no agreement law: `lessorPin` maps
  `γl → lp` only). Options: (a) `lease.srvInv` (sealed, already in both through `srvLeaseRd`) gains
  `lessorAt E.γ.leases 0 (∅, ∅, ∅)`, minted in `NewServer` from `NewLessor`'s `leaseEver γl []`;
  `BuildServer`/`StartServer` return the γl-free raft part (`leaseTTLRowR s ps`) as their own
  conjunct; `Main` makes the row with `leaseTTLRow_intro`; (b) the row inside `memberUp` (C2 rules it
  out); (c) an agreement law for `srvLessorRd` (a new pin direction in the lessor). Recommendation:
  (a), no trusted text changes beyond the approved ones.
- A4, the revocable mode's freshness, mode-free: `Grant`/`closers_grant` take
  `lessorModeIs γl true ∨ ⌜id ∉ U⌝` (the caller's `srvGrantable` has the mode).

**E3 (c) stage 2 done (2026-11-05, commits `ad82e00f41`..`2d88d1a45e`).** U threaded through the
apply chain: `isApplyLessor`'s Grant clause and `grantPre`/`grantPost` take U (`apply.everOwn E U`:
`leaseEver` in a granting cluster, `True` otherwise; `apply.grantFresh E rq U`); `srvRest`'s
granting arm carries `srvEver E A` (U among `srvGrantLog A`, the revocable grant ids of `A`'s entries
with data); freshness at `applyEntryNormal` from `kv_entry_grantFresh`. **The one-prefix fact is
proved, not a premise**: `kvGrantIds` records `idPfx u = kvPfx γk` (the generator's prefix in the
revocable mode), `grantIdOwn` carries it from `idFresh`, `kv_grantIds_nodup` concludes the masked ids
distinct; the single-member condition is at the allocation (`srvMemberBoot_alloc`: revocable →
`γk.ids.pfx` the member's prefix; `kvInv_congr` gains `kvPfx` agreement). `NewServer` puts
`leaseEver γl []` in the initial image, `lease.srvInv` gains `lessorAt E.γ.leases 0 (∅,∅,∅)`
(`lessorAt_empty`, `lease.srvInv_first`), `NewServer.specG`/`BuildServer.spec`/`StartServer.spec`
return `leaseTTLRowR` (first start only; `specStop`/`specRestart` unchanged).

**Decided by the agent, pending the user:**
- A5, `Recover` with no record: its only server call (`applySnapshot`, `recs = []`, a cluster that
  grants none) has no `leaseEver`; options (a) `Recover` takes and returns
  `⌜recs = []⌝ ∨ leaseEver γl U` (two sites), (b) `srvRest`'s non-granting arm also holds
  `∃ U, leaseEver` (every `srvRest_false` site). Done: (a).
- A6, `srvEver`'s list is `srvGrantLog A` (entries with data), not every entry: `irrDecode` is
  opaque, so an empty filler entry is not known to decode to no grant.

**Stage 3 and the `nodeStartedFresh` review (2026-11-05).** `d415a8d11e` carries
`leaseTimeToLive`'s facts through the wrapper `EtcdServer.LeaseTimeToLive`. The wrapper's own
errors are refuted, not given a fallback: `errIsTrue_leaf_ne`, `authErrVarIs_not_leaseNotFound`,
and the auth specs strengthened to answer `authErrVarIs`. The facts continue through v3rpc's
`ttlAns`/`leaseTTLOut` to the client's live contracts `etcdLeaseTTLSpecLive`/`etcdLeaseLeasesSpecLive`.
Those contracts are registered by `kv_lease_served`'s revocable arm (`etcdLeaseGrantLiveAt addr s
E`). The lessor laws `lessorAt_absent_stays` and `leaseTTLAt_ttl_agree` are in `LessorHist.lean`.
`01cfcabf20` is raft's interface diff.

The spec review of `nodeStartedFresh` found nothing first-tier. Its N1 is done: the start record is
now a tag, `ApiImpl.nodeStartTag n γ boot`: `StartNode` writes `true`, `RestartNode` writes `false`.
It replaces the driver-state record (`nodeStartRec`/`nodeDriverFrom`). With the tag, the exclusion
of restarts no longer depends on `RestartNode` discarding its record or on its `[scope]` premise.
The interface does not change. The other findings and the nonissue are in `questions.md`.

**The granted TTL and `Main` (2026-11-05).**

`28411daeac` threads E3/R5's granted TTL from `lessor.Grant` up to the client's revocable grant
contract. The grant's success fact takes the request (`G : w64 × w64 → w64 → IProp GF` in
`lessorGrantOkG` and `etcdLeaseGrantSpecG/GR`; the monotone mode passes `fun _ id => …`).
`etcdLeaseGrantSpecLive γl` is now
`∃ i l t, leaseLiveFrom γl i id l ∗ lsF "ttl" l ↦□ t ∗ ⌜sint.Z req.1 ≤ sint.Z t⌝`.
It also changes the apply contract's Grant clause, `grantAnswer`, `leaseGrantedResp` (which gains
`reqTTL`) and `EtcdServer.LeaseGrant.spec`'s post.

`e1c0d90073` proves leaseexpiry's `Main` and links it (`MainLinked`, which passes
`srvGrantOpen_open` and `srvRevokeOpen_open`). Its `Adequacy` and `Results` are leasegrant's, without
`leasesNoExpiry`. The collection is `etc/tcb-collections/leaseexpiry.txt`.

How the proof goes:
- The poll loop's invariant is "`gone` → `leaseAbsentFrom γl i0 id`", where `i0` is the grant's
  index.
- Each answer is turned, under the row (`leaseTTLRow`, from `StartServer`'s `leaseTTLRowR` and
  `lease.srvInv_first`), into "`GrantedTTL ≠ 0` ∨ absent": `leaseTTLAt_ttl_agree` makes a found
  answer's `GrantedTTL` the lease's `ttl ≥ 1`.
- `Leases()` is asked at the absence's index. `lessorAt_absent_stays` shows the listing's snapshot
  lacks the lease, so the range loop never panics.

Bounds: +1 spec-thread, +2 spec-receipt (leaseexpiry's `Main`, as leasegrant's), in the baseline.

## Freeze (2026-11-05) and its change log

Frozen at `lease-expiry-frozen` (`ea7937b221`), approved by the user via etcd-grove-82. Changes to
frozen or exported statements since:

- **2026-11-05, merge of lean `53a8c33764` (post-merge change to an exported statement; approved by
  the user via etcd-grove-82).** `etcd_leaseexpiry.BootFacts` is now `etcdstart.BootFacts`
  (`OneMember.lean`), as leasegrant's and lease's are, which adds the field `urls : bootURLsOk
  (LogEntry.toEntries bl 0)` (the boot members' peer URLs valid UTF-8 and pairwise disjoint) to the
  hypotheses of `etcd_leaseexpiry_safe` and `leaseexpiry_Main`. Cause: lean's restart R2b-3d gap 3,
  which made `etcdstart.alloc1` take the fact; it is not derivable from the other boot facts
  (`BootLog` leaves the members' contexts, where the URLs are, arbitrary). No axiom or `sorry` added.
- Not a change: the same merge's `srvRunFieldsAt` stop predicate `SP` (R2b-2). The frozen
  `EtcdServer.revokeExpiredLeases.spec` already quantified over it; `run`'s proof now passes its own.
- Merged beside it, not a change to a frozen statement: `NewServer.specG`'s post keeps the lease slot
  (`lease.srvInv`, `leaseTTLRowR`) and restart's stop slot (`srvStop.keep`).
- **2026-11-05, S2–S4 Scope (approved change to a frozen statement, by the user via etcd-grove-82):**
  `lease.lessor.Recover.spec`'s ever-set premise `∀ id ∈ recs, id ∉ U` becomes `∀ id ∈ recs, id ∈ U →
  id ∈ L` (an id the lessor had is still live), its post `leaseEver γl (U ∪ ids)`: in a snapshot
  restore the follower usually already had some of the snapshot's leases, so the frozen premise was
  false in the normal case. To be applied in S2–S4's Draft (branch `lease-p1`'s successor).
- **2026-11-05, S2–S4 Draft stop, option (A) (approved change to a frozen statement, by the user via
  etcd-grove-82, Q-S4).** `lease.leaseTTLAt_ttl_agree` (`LessorHist.lean:528`), an id's TTL is the
  same at every index of the lessor's history, is false of Go once snapshots carry leases: a restore
  rebuilds each lease with TTL raised to *this* member's `minLeaseTTL`, which differs between members
  configured differently (`nonissues/etcd-lease-ttl-differs-across-members.md`). It is replaced by a
  min-TTL law: every TTL the history records is at least the lessor's `minLeaseTTL`, which is a new
  `lessorRdBody` clause. The internal `histOnce` becomes ids-only (the `*Lease` is free), and
  `leaseexpiry/Main.lean:324` is re-proved from the new law plus `minLeaseTTL ≥ 1` of its own
  configuration. The statements of `etcd_leaseexpiry_safe` and `leaseexpiry_Main` are unchanged
  (checked at the end with `etc/gen-interface.py` / the TCB roots).

- **2026-11-05, S2–S4 Draft, second stop (approved changes to frozen and trusted statements, by the
  user via etcd-grove-82).** (A)'s `minLeaseTTL ≥ 1` has no source: `int64(math.Ceil(…))` is
  uninterpreted in the model (`FloatToInt.lean`), and `lessorCfg` leaves the minimum free.
  - Q-S6 (A-ii): the min-TTL law is replaced by a requested-TTL lower bound. Every TTL a lessor's
    history records for an id is at least the TTL its grant requested. That bound is put on the
    records in `bkRestAtL` (lease-grant's Freeze and #7's `imageAt`; `notes/lease-grant-plan.md`,
    amendment (I)) and in `srvRestAt`, and the trusted `NewLessor` axiom's post allocates a
    requested-TTL ghost map (ghost only; attacked with the axiom skill before the Freeze).
    `leaseexpiry/Main.lean:324` gets `GrantedTTL ≥ 1` from its own request of 1.
  - Q-S7: `lease.lessor.Recover.spec`'s post gives `leaseOwn` in a caller-chosen order `Lr`, a
    permutation of the records' ids (Go's `leaseMap` is unordered), so that it matches `ltHalf`'s
    log order.

- **2026-11-05, S2–S4 Draft, third stop, Q-S8 (approved change to frozen and exported statements, by the
  user via etcd-grove-82).** Main cannot name its grant's request: Grant.spec's post gives only the
  object's TTL, and on one lessor a TTL can fall from 10 to 0 across restores from leaders with
  different minimum TTLs, so no law from objects alone gives `t' ≥ 1`.
  - `lease.lessor.Grant.spec`'s success post issues a persistent `lease.leaseReqIs γl id ttl`. It is
    carried up the frozen grant chain to the client contract: the apply contract's Grant clause,
    `grantAnswer`, `leaseGrantedResp`, `EtcdServer.LeaseGrant.spec`'s post, v3rpc's grant
    instance, and `etcdLeaseGrantSpecLive`'s success fact.
  - `lease.lessor.Recover.spec` (its third change) takes the records' requests `rq` and issues
    `leaseReqIs` for each record.
  - New law `leaseTTLAt_ge_req`.
  - From here on, the batching rule (the user's): further frozen or exported changes are applied as
    DRAFT, logged old → new with their cause, and brought as one batch at the Draft's end.

## S2–S4 Draft (2026-11-05)

Branch `lease-snap` (off lean `1f992c54b0`). **Stopped on item 1 (`Recover.spec`'s ever-set premise),
and therefore on items 2–4, before any frozen or hub statement was edited.** What is committed is
true today and consumes nothing: the image's lease vocabulary and the S2 table lemmas
(`Proof/go_etcd_io/etcd/server/v3/etcdserver/ImageLeases.lean`). The statements of items 1–4 are
below as text, with what stops them.

### The stop: a recovered live lease is a new `*Lease` with a possibly different TTL

Go's `initAndRecover` (`lessor.go:808-835`) makes a fresh `Lease` per record, its `ttl` the
record's raised to *this member's* `minLeaseTTL`. The record is the leader's: `Grant` wrote
`max(req, leader's minLeaseTTL)`. `minLeaseTTL` is per member (`server.go:344-349`:
`ceil((3·ElectionTicks/2)·TickMs)` of that member's configuration). So when a follower that applied
a grant later restores a snapshot containing the lease, the lease is the same id, a new `*Lease`
and, when the members' `minLeaseTTL` differ, a different TTL. Example: leader `minLeaseTTL` 10,
follower 2, `Grant(TTL 5)`: the follower's lessor has TTL 5, then 10 after the restore, and its
`TimeToLive` answers `GrantedTTL` 5, then 10.

The approved premise `id ∈ U → id ∈ L` admits exactly this case. That is right: it is the normal
case, and the old premise `id ∉ U` was false there. But the lessor's reader invariant
(`lessorRdBody`, `InvLessor.lean`) and two laws do not admit it:
- `histOnce` (internal) says an id live at `i` and at `k ≥ i` is live at every index between with
  **the same `*Lease`**. `Recover` appends a snapshot that maps a live id to a fresh `*Lease`.
  `closers_recover` (`LessorRecoverLemmas.lean:353`) closes the invariant through `histOnce_fresh`,
  which needs every recovered id new to the history. Under the new premise that step is false, so
  `Recover.wp_proof` cannot be repaired by a local `sorry` without asserting a false lemma.
- Weakening `histOnce` to ids (live over an interval, the `*Lease` free) is internal and keeps
  `lessorAt_absent_stays`: a revoked id is in `U` and not in `L`, so the premise keeps it out of
  `recs`. But it removes `histOnce_lease`, whose only consumer is **`leaseTTLAt_ttl_agree`**
  (`LessorHist.lean:528`, in `lease-expiry-frozen`): "a lease's TTL at any index of the history is
  its `ttl` field". After the restore above that law is **false of Go**, not only unprovable.
  `leaseexpiry`'s `Main` uses it to refute a found answer with `GrantedTTL = 0`.

The generalized snapshot specs (items 2, 3) and the deletion of `srvGrantOpen` (item 4) are provable
only through a `Recover` that admits recovered live ids, so they wait on this too. Writing them now
with `sorry`s would put statements that are unprovable under the current lessor invariant behind
marked `sorry`s. The brief excludes that.

**Options (for 82 and the user):**
- (A) *Weaken the frozen law to what `Main` uses* (recommended). `Main` only needs a found TTL
  `≠ 0`. Candidate: "every TTL the history records for `id` is at least the lessor's
  `minLeaseTTL`". Grant raises to it (`grantTTL`), `Recover` raises to it (`recTTLs`), and
  `lF "minLeaseTTL" lp ↦□ mt` is persistent. This would be a new `lessorRdBody` clause beside
  `ttlTie`. `Main` then needs `mt ≥ 1`, a fact of its own fixed configuration (`ElectionTicks`,
  `TickMs`), not a scope premise. Alternatively "at least the grant's requested TTL", but that needs
  the image's TTLs constrained (`f id ≥ req`), which changes `bkRestAtL` (frozen in lease-grant and
  #7). With (A), `histOnce` becomes ids-only, `histOnce_lease` and `leaseTTLAt_ttl_agree` are
  replaced, and `leaseexpiry/Main.lean:324` is re-proved from the new law. These are frozen and
  exported proofs: the user's decision.
- (B) *Keep the law by a cluster premise* "all members share `minLeaseTTL`": a scope premise on the
  exported results, false for heterogeneous clusters. Not recommended.
- (C) *Per-epoch agreement* (the law only between restores): `Main` cannot show that no restore
  happened, because `run`'s proof is generic. Does not work.

S5's Go test should cover this: a follower with a smaller `ElectionTicks` than the leader,
`TimeToLive` before and after its restore. It is Go's documented behavior (TTL raised to the
member's minimum), so it goes in `nonissues/` if anywhere.

### The statements, before → after (not applied)

1. **`lease.lessor.Recover.spec`** (`Spec/.../lease/lessor__Recover.lean:64`, frozen; change
   approved, Q-S2):
   - before: `(∀ id ∈ recs.map (·.1), id ∉ U)`
   - after: `(∀ id ∈ recs.map (·.1), id ∈ U → id ∈ L)`
   - post unchanged: `(⌜recs = []⌝ ∨ lease.leaseEver γl (U ++ recs.map (·.1)))`. **The list form
     `++` is kept for the approved `U ∪ ids`.** `leaseEver` is a ghost variable over `List w64`, and
     every use is membership (`histIn`, `Grant`'s `id ∉ U`, `histIn_mono`). `++` has the union's
     membership, needs no lawful `BEq` (which `List.union` would), and matches `Grant`'s
     `U ++ [id]`.
   - re-checked:
     - `□ [∗list] id ∈ recs.map (·.1), leaseGranted γl id` fits: in a granting cluster `srvRest`'s
       `srvGrantable` gives `□ ∀ id, leaseGranted`.
     - the mode premise `mono = true → ∀ id ∈ L, id ∈ recs.map (·.1)` fits, from
       `appliedTable_mono_sub`.
     - `⌜recs = []⌝ ∨ leaseEver γl U` fits: granting, the apply thread's `everOwn` is `leaseEver`;
       not granting, `recs = []` (`imageLeasesAt_nil` with the empty table).
     - **But see the stop:** the proof's `closers_recover` needs `lessorRdBody` changed.
2. **`EtcdServer.applySnapshot.specSnapM`** (hub 3, approved):
   - `E.lg = false →` dropped.
   - `(hlease : ((backend.rbData d.P D).lookup go!"lease").getD ∅ = ∅)` becomes
     `(hlease : imageLeasesAt γr d.P D A')`, placed after `A'`.
   - **Also needed, beyond the Scope's wording:** `lease.lessorRevocable E.γ.leases` becomes
     `lease.lessorModeIs E.γ.leases (decide (E.lm = .mono))`. In the monotone mode no caller can
     give a revocable lessor. `Recover` takes the mode, and `srvSnapRO` already holds this fact
     (`HlpM`).
   - `hA'` (`snapRestImgM`) stays: the rest model's lease bucket is always empty
     (`restModel_lease`), so "the image's buckets with `lease` emptied" is still the rest model's.
   - What the proof needs:
     - the walk calls `Recover` with `imageLeasesAt_recs`'s records;
     - the mode premise comes from `appliedTable_mono_sub` and the KV invariant's
       `plainLogM γk.cmp .mono`;
     - the ever-set premise comes from `appliedTable_granted_live`, `srvEverOk` and `kvGrantIds`'
       `Nodup`;
     - after the restore, `srvRest E' γr A'`'s leased arm: `E'.RO (restLeasesWith f (appliedTable
       γr A').ids (restModel …))` from `hA'` and `imageLeasesAt`, plus `ltHalf` and `srvEver` at
       `A'`.
3. **`EtcdServer.applyAll.specSnap`/`specSnapM`** (`EtcdServer__applyAll.lean:163, 258`): drop
   `γr.kv.lg = false →`.
   - Their proofs (`ApplyAllSnap.lean`, `ApplyAllSnapOn.lean`) give `hlease` from
     `SnapImageFacts(On).hlease`. That field becomes `imageLeasesAt γr d.P D A'`, which
     `snapRecv_image(On)` gets at any `lg` from `imageAt`'s `bkRestAtL` (`imageLeasesAt_of_bkRestAtL`,
     proved) instead of from `bkRestAt_of_L` at `lg = false`.
   - `snapRecv_image` itself takes `HElg` for `plainLogM … .none` (the conf-change and restore-log
     facts). Those must be restated at the KV names' mode: `restoreLogOk_kvRaftOf` and
     `kvTableOf_plainM` take `.none` today. This is an open point.
   - `run_job_snap`: its `case true` (`srvGrantOpen_snap`) goes, and the `lg = false` proof covers
     both cases. `run_snap_jobOn` stops passing `Hcmlg.2`.
4. **`lease.bootCfg`/`lease.runCfg`** (hub request, accepted):
   - drop `(m ≠ .none → srvGrantOpen)`;
   - delete `lease.bootCfg_open`, `lease.runCfg_open`, `srvGrantOpen`, `srvGrantOpen_snap`,
     `runSnapLgOkBody` (`LeaseRun.lean:51`) and `srvGrantOpen_open` (`EtcdServer__run.lean:281`);
   - `bootCfg_mono`/`_revocable` and `runCfg_mono`/`_revocable` lose `hopen`;
   - `etcd_leasegrant`/`etcd_leaseexpiry`'s `Main` and `_safe` lose `hslg`, and their `MainLinked`
     files stop passing `srvGrantOpen_open`.
5. **`imageAt`** (#7's Freeze): **no change needed.** It already states `bkRestAtL` (lease-grant's
   Freeze amendment (D), `InvImage.lean:114`). The receiver reduced it to the plain case with
   `bkRestAt_of_L` at `lg = false` (`SnapRecvFacts.lean:485`), and the leased case reads
   `bkRestAtL` directly.

### New vocabulary (committed, `ImageLeases.lean`)
- `imageLeasesAt γr P D A'`: the image's lease bucket is `restLeasesWith f (appliedTable γr A').ids`
  over the rest model's bucket, for some `f`. That is one record per id of the snapshot's table (ids
  only, TTLs existential, remaining TTL 0), in the same form as `bkRestAtL` and `srvRest`'s leased
  arm. No `leasepb` decoding law is needed: the records are `leaseRecEnc`'s, which
  `MustUnsafeGetAllLeases` already takes.
- `imageLeasesAt_of_bkRestAtL` (proved), `imageLeasesAt_nil` (proved: an empty table gives the old
  `hlease`).
- `imageLeasesAt_recs` (DRAFT `sorry`): `Recover`'s `recs`.
- `appliedTable_mono_sub` (DRAFT `sorry`): S2, monotone mode.
- `appliedTable_granted_live` (DRAFT `sorry`): S2, revocable mode.

### Open points (besides the stop)
- **The monotone mode's ever-set.** `srvEverOk` bounds `U` only in the revocable mode
  (`U ⊆ srvGrantLog A`). In the monotone mode `Recover`'s premise needs `U ⊆ L`. It holds (nothing
  leaves a monotone lessor), but nothing records it. Add `E.lm = .mono → ∀ u ∈ U, u ∈
  (appliedTable γr A).ids` to `srvEverOk`, or a lessor law `U ⊆ L` in the monotone mode.
- **`ltHalf`'s list order.** `Recover` gives `leaseOwn γl (recs.map (·.1))`, in key order.
  `srvRestAt` holds `ltHalf E (appliedTable γr A).ids`, in log order, and `ltHalf_agree` is list
  equality. After a restore the two orders differ. Either `ltHalf`/`leaseOwn` become set-like (a
  permutation), or the apply side keeps the lessor's order.
- **`snapRecv_image(On)` at the KV names' mode** (item 3's note).
- The S2 lemmas' statements are believed true but unproved: `appliedTable_granted_live` relies on
  every successful grant of the table being an entry counted by `logRevGrantIds` (grants with data,
  decoded).

### Build and trust base
`lake build Proof.go_etcd_io.etcd.server.v3.etcdserver.ImageLeases` passes. Nothing imports the
module, so no importer rebuilds. Sorry delta: three new declarations with `sorry`, each marked
`-- DRAFT S2–S4` and reached by no result, so `etc/tcb-report.py`'s results and collections are
unchanged. No axiom.

### Resumption after Q-S4 (A) and Q-S5, 2026-11-05: stopped again, at `Main`'s `minLeaseTTL ≥ 1`

Option (A) and the `specSnapM` mode change are approved (`d8ee999600`). Before any Lean edit, I
checked the one step (A) needs outside the lessor: `leaseexpiry/Main.lean:324` re-proved from the
min-TTL law plus "`minLeaseTTL ≥ 1`, a fact of `Main`'s own configuration". **That fact is not
derivable in the model, and every way to supply it changes a trusted or frozen statement that was
not approved.** Nothing was applied: the lessor, `Recover.spec`, items 2–4 and `Main` are as on
lean. Items 2–4's proofs go through `Recover`, whose proof needs the lessor change, whose law
`Main` cannot use yet. So they wait too: applying them with `sorry`s would put statements behind
`sorry`s that are unprovable under the current definitions.

**Why `minLeaseTTL ≥ 1` has no source.**
- `Main` holds the lessor's reader invariant, its own lease (`leaseLiveFrom`, its `ttl` field
  `gt` with `1 ≤ gt` from `Grant`'s post) and the answer's `leaseTTLAt j id t'`. It does not see
  the lessor's location or its `minLeaseTTL` field.
- `lease.NewLessor.wp_proof` is an axiom whose post gives `lessorCfg lp`, i.e.
  `∃ mt, lF "minLeaseTTL" lp ↦□ mt`. `mt` is not tied to `cfg.MinLeaseTTL'`.
- `NewServer` computes `MinLeaseTTL` as `int64(math.Ceil(minTTL.Seconds()))`. In the model
  `int64(f)` steps to an uninterpreted `float64ToInt64 f` (`Float64ToInt64Semantics`,
  `FloatToInt.lean`), so `MinLeaseTTL ≥ 1` is unprovable whatever `Main`'s `ElectionTicks` and
  `TickMs` are.
- A `sorry` on "this lessor's `minLeaseTTL ≥ 1`" would be false in some models of the hypothesis
  class (where `float64ToInt64` gives `0`). The rules exclude it.

**The routes, each beyond what is approved:**
- (A-i) *Configuration route* (the brief's intent). Three changes:
  - `NewLessor`'s axiom post names the configured minimum, `lF "minLeaseTTL" lp ↦□
    cfg.MinLeaseTTL'`. It is true of Go (`newLessor` sets `minLeaseTTL: cfg.MinLeaseTTL`), but it
    strengthens a trusted statement: it needs the `axiom` skill and the user.
  - A trusted float fact: `int64(math.Ceil(d.Seconds())) ≥ 1` for a duration `d > 0`. This needs
    `Float64ToInt64Semantics` and `math.Ceil` interpreted, a Perennial change to propose on its own.
    Or else a local trust-boundary fact, which grows the trust base.
  - The lease slot (`lease.srvInv`) carries "the lessor's minimum is `mt`, `1 ≤ mt`" to `Main`.
    That slot sits in `NewServer.specG`'s post, so it is a hub change.
- (A-ii) *Request route* (no floats). The history records, per id, at least the TTL its grant
  requested. That holds of Go: a leader's `Grant` writes `max(req, its minLeaseTTL) ≥ req`, and
  `Recover` only raises. `Main` then gets `t' ≥ 1` from its request `1`. It needs the image's and
  `srvRest`'s record TTLs bounded below by the table's requested TTL. The table already stores
  `(g.id, g.ttl)`, so the change is `∃ f, (∀ (id, r) ∈ table, r ≤ f id) ∧ …` in `bkRestAtL` and
  `srvRestAt`, both frozen (#7's `imageAt` via `bkRestAtL`; lease-grant's `srvRest`). It also
  needs the lessor to keep a ghost map of requested TTLs (`Grant` writes it, `Recover`'s premise
  bounds the records by it). The map's allocation is a ghost-only change to `NewLessor`'s axiom
  post, as E3 (c)'s `leaseEver` was.
- (A-iii) *Per-snapshot lower bound kept by `Main`'s own lease*. Not true: the recovered
  `max(rec, mt)` has no relation to the follower's earlier `max(req, mt)` unless `rec ≥ req`,
  which is (A-ii)'s image fact.

Recommendation: **(A-ii)**. It is true of Go without float reasoning. Its trusted part is
ghost-only (the requested-TTL map, as `leaseEver`'s was), and its frozen part is a weakening of
nothing: it adds a true conjunct to what the sender already proves (`Grant`'s `grantTTL` is
`≥ req`, `RestLease.lean`). (A-i) is closer to the approved wording but needs a float fact Perennial
cannot state today.

### The open points: proposed resolutions (not applied; each the smallest true change)

- **The monotone ever-set** (`Recover`'s premise needs `U ⊆ L` when `mono`). Add to
  `lessorRdBody`, mode-free, the converse of `histIn`: `histCover hs U : ∀ u ∈ U, everIn hs u`
  (every id the lessor ever had appears in some snapshot).
  - `Grant` keeps it: its id is in the new snapshot. `Recover` keeps it: its ids are in the
    recovered snapshot. The others leave `U`.
  - With `histMono`, in the monotone mode an id that appears once is live in the last snapshot, so
    the law `lessorRdInv γl ∗ lessorModeIs γl true ∗ leaseEver γl U ∗ leaseOwn γl L I ⊢ |={E}=>
    ⌜∀ u ∈ U, u ∈ L⌝` gives `Recover`'s premise.
  - Internal to the lessor. `NewLessor`'s initial `U = []` makes it vacuous there, so the
    axiom's post is unchanged in substance. No change to `srvEverOk`, which frozen specs carry
    through `srvRest`.
- **`ltHalf`'s order** (`Recover`'s `leaseOwn γl (recs.map (·.1))` is in key order; `srvRestAt`
  and `leasesLive` hold `ltHalf` at the table's log order; `ltHalf_agree` is list equality).
  - The lessor's lists are order-free in Go: `leaseMap` is a map, and `lessorMu`, `leaseClosers`
    and `lessorAuth` read `L` through membership only. So the smallest change is in `Recover.spec`:
    a caller-chosen order `Lr` with `Lr.Perm (recs.map (·.1))`, the post at `Lr`
    (`leaseOwn γl Lr ∅`, `leaseRevokers γl Lr`). The walk picks the snapshot table's ids. One
    frozen spec, one caller.
  - **This is a change to `Recover.spec` beyond the approved premise: it needs approval.**
  - The alternative, `srvRestAt` holding `∃ T', T'.Perm T ∗ ltHalf E T'`, is internal to
    `InvRest`. But it reaches every grant and revoke lemma that threads `ltHalf` (`InvRest.lean`
    838–1027, `ApplyCmpArm.lean`, `ApplyRec.lean`, `applierV3backend__LeaseRevoke.lean`) and
    changes `srvRest`'s meaning under frozen specs. Larger.
- **`snapRecv_image(On)` at the KV names' mode**: internal lemmas only.
  - `restoreLogOk_kvRaftOf` (`KVModelRestore.lean:280`, today at `plainLogM cmp .none`)
    generalizes to `plainLogM cmp lm`: a grant leaves the KV log, and a revocation is `revokeLog`
    of no attached key, the identity (X7's lease-free-keys fact).
  - `bkRestAt_of_L` is replaced by `imageLeasesAt_of_bkRestAtL` (proved, `ImageLeases.lean`), and
    the other buckets come from `restLeasesWith_lookup_other`. So the plain-image lemmas
    `image_bootBuckets`, `image_membBuckets`, `clusterImageOk_of_bkRestAt` and
    `restModel_bk_of_bkRestAt` get `bkRestAtL` twins whose lease arm is the emptied one, as `hA'`
    already states.
  - `SnapImageFacts(On).hlease` becomes `imageLeasesAt γr d.P D A'`. The mode-on receiver
    (`snapRecv_imageOn`) needs no lease case if `plainLogOn` admits no grant: to check in Prove.
  - No frozen statement changes.

### Build and sorries
No Lean change in this round: the build is unchanged, and the DRAFT sorries are still the three
of `ImageLeases.lean` (`imageLeasesAt_recs`, `appliedTable_mono_sub`,
`appliedTable_granted_live`), reached by no result.

### Third round (after Q-S6 (A-ii) and Q-S7, 2026-11-05): stopped at how `Main` learns its request

The base is `2add3b6a0f` (lean `080f18c48f` merged). Before any Lean edit I checked (A-ii) end to end
at its one consumer, `leaseexpiry/Main.lean:324`. **The requested-TTL map gives `Main` nothing
unless `Main` learns the map's entry for its own id, and only the grant chain can tell it: a
change to `lease.lessor.Grant.spec`'s post and to the frozen chain above it, beyond Q-S6/Q-S7.**
Nothing was applied.

**What `Main` holds at line 324:**
- the reader invariant (`HrdInv`);
- its grant's facts, through the client's live contract `etcdLeaseGrantSpecLive`
  (`InvLeaseGrant.lean:97`): `leaseLiveFrom γl gi id gl` (the object `gl` is `id`'s lease at
  some index), `ttl gl ↦□ gt` and `1 ≤ gt`;
- the answer's `leaseTTLAt γl j id t'`.

`Grant.spec`'s post (`lessor__Grant.lean`) is where these come from:
`leaseLiveFrom γl 0 id l ∗ ∃ mt, lF "minLeaseTTL" lp ↦□ mt ∗ lsF "ttl" l ↦□ grantTTL mt ttl`.
None of it names the request in ghost state.

**Why no law over these facts works:**
- A history clause "every TTL of `id` ≥ `Q id`" (Q the requested-TTL map) is true of Go. Recovered
  TTLs are `max(rec, mt) ≥ req`, since the leader's record is `max(req, its mt)`. But `Main` cannot
  name `Q id`.
- A law from the facts `Main` has (`l` is `id`'s lease somewhere, `ttl l = t`) to `t' ≥ t` is false:
  `l` may be a recovered object whose TTL a later restore lowers. Example: the record from leader
  L0 has `max(req, mt_L0)`, a later one from L1 has `max(req, mt_L1) < max(req, mt_L0)`.
- To distinguish `Main`'s object as the granted one, `Main` needs a provenance fact from `Grant`.
- `Main` gets `1 ≤ gt`, which bounds its own object's TTL, not the request. With `mt` uninterpreted,
  `gt ≥ 1` says nothing about `req`.

**The smallest change that works (for 82 and the user):**
1. `lease.lessor.Grant.spec` (frozen): the success arm also gives the persistent
   `lease.leaseReqIs γl id ttl`, "the request of `id`'s grant was `ttl`". It is a ghost-only
   addition to a *proved* spec: `Grant`'s proof inserts `id ↦ ttl` into the lessor's map, where
   `id` is fresh because the map's ids are ever-ids. No trusted statement changes beyond Q-S6's
   allocation.
2. The grant chain carries it to the client's contract (frozen and exported definitions; the
   statements of `etcd_leaseexpiry_safe` and `leaseexpiry_Main` are unchanged):
   - the apply contract's Grant clause, `grantAnswer`, `leaseGrantedResp`;
   - `EtcdServer.LeaseGrant.spec`'s post;
   - v3rpc's `lessorGrantOkG` instance;
   - `etcdLeaseGrantSpecLive`'s `G`, which becomes `∃ i l t, leaseLiveFrom γl i id l ∗
     lsF "ttl" l ↦□ t ∗ ⌜sint.Z req.1 ≤ sint.Z t⌝ ∗ lease.leaseReqIs γl id req.1`.

   This is the same path `28411daeac` threaded the granted TTL along.
3. `Recover.spec` (frozen; a third change beyond Q-S2 and Q-S7) takes the records' requests:
   - `rq : w64 → w64` with `∀ x ∈ recs, sint.Z (rq x.1) ≤ sint.Z x.2.1`, which the image's new
     `bkRestAtL` bound gives;
   - `□ [∗list] x ∈ recs, ⌜x.1 ∉ U⌝ ∨ lease.leaseReqIs γl x.1 (rq x.1)`, an issued request agreeing
     with the caller's;
   - its post gives `leaseReqIs γl x.1 (rq x.1)` for each record.
4. The apply thread keeps, for every id of its ever-set, `leaseReqIs γl u r` with `r` the
   requested TTL of `u`'s grant in the log. This is internal to `srvEver` in `InvRest`, as `histCover`
   is to the lessor; the log's grant ids are distinct (`kvGrantIds`). That is the evidence item 3's
   premise takes.
5. The law replacing `leaseTTLAt_ttl_agree`: `leaseTTLAt_ge_req : lessorRdInv γl ∗ leaseReqIs γl
   id r ∗ leaseTTLAt γl j id t ⊢ |={E}=> ⌜sint.Z r ≤ sint.Z t⌝`. `Main` then concludes `t' ≥ 1`
   from its request `1`, a short proof.

Without item 1, the map, the `bkRestAtL`/`srvRestAt` bound and the `NewLessor` allocation (Q-S6)
have no consumer, and `Main:324` has no proof. A `sorry` there would be a true statement, but it
is blocked on a frozen change rather than Prove work, which the brief excludes. Everything else
approved (the lessor's `histOnce` ids-only and `histCover`, Q-S7's `Lr`, items 2–4 of the Draft) is
independent of this choice. It waits only because dropping `leaseTTLAt_ttl_agree` breaks `Main`'s
proof.

### Fourth round (after Q-S8, 2026-11-05): applied, as DRAFT

Applied on `lease-snap` under the batching rule (frozen or exported changes beyond the approvals
applied as DRAFT and logged below, not stopped at). `srvGrantOpen`, `srvGrantOpen_snap`,
`runSnapLgOkBody`, `srvGrantOpen_open`, `bootCfg_open`, `runCfg_open` are deleted; no `hslg` is
left in the Mains or the `MainLinked` files.

**The statements, before → after (the approved ones).**

- `lease.histOnce hs` (Q-S4 (A)): "live at `i` with lease `l` and at `k` → live at every `j`
  between *with `l`*" → ids only: `(σ.1.lookup id).isSome → (ρ.1.lookup id).isSome →
  (τ.1.lookup id).isSome`. `histOnce_lease` deleted; `histOnce_snoc`'s premise "same `*Lease` or
  never had" → "live in the last snapshot or never had"; `histOnce_fresh` → `histOnce_recover`.
- `LessorRdNames`: `GName × GName × Bool × GName` → `… × GName × GName` (the fifth, `γr.2.2.2.2`,
  the requested TTLs' ghost map; `U` moves to `γr.2.2.2.1`).
- `lessorRdBody` gains a last conjunct `∃ Q, ghostMapAuth γr.2.2.2.2 1 Q ∗ ⌜reqOk hs Q⌝`, with
  `reqOk hs Q := (∀ i σ id t r, hs[i]? = some σ → (σ.1.lookup id).isSome → σ.2.2.lookup id = some
  t → Q.lookup id = some r → sint.Z r ≤ sint.Z t) ∧ (∀ id r, Q.lookup id = some r → everIn hs id)`.
- New `lease.leaseReqIs γl id r := ∃ γr, lessorPinR γl γr ∗ ghostMapElem γr.2.2.2.2 id □ r`
  (persistent).
- `leaseTTLAt_ttl_agree` (… `leaseLiveFrom γl m id l ∗ lsF "ttl" l ↦□ t ∗ leaseTTLAt γl j id t' ⊢
  ⌜t' = t⌝`) → `leaseTTLAt_ge_req : lessorRdInv γl ∗ leaseReqIs γl id r ∗ leaseTTLAt γl j id t ⊢
  |={E}=> ⌜sint.Z r ≤ sint.Z t⌝` (proved).
- `lessor.Grant.spec`, success post: `… ∗ leaseEver γl (U ++ [id])` → `… ∗ leaseEver γl (U ++ [id])
  ∗ leaseReqIs γl id ttl` (Q-S8; proved: `grant_hist` inserts it, `grantTTL_ge`).
- `lessor.Recover.spec` (Q-S4, Q-S7, Q-S8): binders `+ (rq : w64 → w64) (Lr : List w64)`; premise
  `∀ id ∈ recs.map (·.1), id ∉ U` → `∀ id ∈ recs.map (·.1), id ∈ U → id ∈ L`, plus
  `∀ x ∈ recs, sint.Z (rq x.1) ≤ sint.Z x.2.1` and `Lr.Perm (recs.map (·.1))`; pre `+ □ ([∗list] x
  ∈ recs, ⌜x.1 ∉ U⌝ ∨ leaseReqIs γl x.1 (rq x.1))`; post `leaseOwn γl (recs.map (·.1)) ∅`,
  `leaseRevokers γl (recs.map (·.1))` → at `Lr`, `+ □ ([∗list] x ∈ recs, leaseReqIs γl x.1 (rq
  x.1))`.
- `NewLessor`'s axiom: statement text unchanged; its post's `lessorInv` now contains the map (the
  body above), and its docstring gains the bullet on the requested TTLs (ghost-only, allocated empty,
  no claim about Go).
- `applySnapshot.specSnapM`: `(hlease : (rbData d.P D "lease").getD ∅ = ∅)` → `(hlease :
  imageLeasesAt γr d.P D A')` (moved after `hA'`); `E.lg = false →` dropped;
  `lease.lessorRevocable E.γ.leases` → `lease.lessorModeIs E.γ.leases (decide (E.lm = .mono))` (Q-S5).
- `applyAll.specSnap`, `specSnapM`: `γr.kv.lg = false →` dropped.
- `lease.bootCfg lm m on`: the conjunct `(m ≠ .none → srvGrantOpen)` dropped (`bootCfg_mono`,
  `bootCfg_revocable` lose `hopen`); `lease.runCfg lm m` likewise (`runCfg_mono`, `runCfg_revocable`
  lose `hopen`); `run_job_snap`, `run_job_snapC` lose `hslg`.
- `etcd_leasegrant.Main.wp_proof` loses `hslg : srvGrantOpen`; `etcd_leaseexpiry.Main.wp_proof`
  loses `hslg` (keeps `hrev`). `Main:324` re-proved from `leaseTTLAt_ge_req` and the grant's
  `leaseReqIs … 1` (a real proof).

**The batch: frozen, exported or trusted changes beyond the approvals** (each old → new, cause).

1. `apply.isApplyLessor`'s `Grant` clause (frozen contract), success post `… ∗ lease.leaseEver
   γ.leases (U ++ [id]) ∗ ∃ t, …` → `… ∗ lease.leaseEver γ.leases (U ++ [id]) ∗ lease.leaseReqIs
   γ.leases id ttl ∗ ∃ t, …`. Cause: Q-S8's "carried up the grant chain" (the lessor's post feeds it,
   `LessorDerive`).
2. `apply.grantAnswer`'s success fact `∃ i l t, leaseLiveFrom … ∗ lsF "ttl" l ↦□ t ∗ ⌜g.ttl ≤ t⌝`
   → `… ∗ ⌜g.ttl ≤ t⌝ ∗ lease.leaseReqIs E.γ.leases g.id g.ttl`. Cause: the same chain.
3. `leaseGrantedResp E resp reqTTL`'s last conjunct `… ∗ ⌜reqTTL ≤ t⌝` → `… ∗ ⌜reqTTL ≤ t⌝ ∗
   lease.leaseReqIs E.γ.leases id reqTTL`. Cause: the same chain.
4. `v3rpc.grantLiveG E m id`: `… ∗ ⌜m.1 ≤ t⌝` → `… ∗ ⌜m.1 ≤ t⌝ ∗ lease.leaseReqIs E.γ.leases id
   m.1`. Cause: the same chain (`etcdLeaseGrantSpecLive` is it by definition).
5. `etcdLeaseGrantSpecLive γl` (the client's exported contract): `… ∗ ⌜req.1 ≤ t⌝` → `… ∗ ⌜req.1 ≤
   t⌝ ∗ lease.leaseReqIs γl id req.1`. Cause: Q-S8's endpoint; `Main` names its request through it.
6. `SnapImageFacts.hlease`, `SnapImageFactsOn.hlease` (internal structures, exported): the empty
   bucket → `imageLeasesAt γr d.P D A'`. Cause: `specSnapM`'s new `hlease`.
7. `lessor_live_perm` (new law, DRAFT sorry): the lessor's authority, the lock's half, `leaseOwn`
   and `leaseRevokers` at a permutation. Cause: Q-S7's `Lr` (`Recover`'s proof).
8. The lessor's internal lemmas `grant_hist`, `closers_grant` (+ `r`, `hrt`, post `leaseReqIs`),
   `recover_hist`, `closers_recover` (the new `hfresh`, `rq`, the requests in and out). Cause: the
   approved lessor changes.

No new or widened axiom besides the approved `NewLessor` post; no trusted model.

**The TTL bound (Q-S6 (A-ii)), applied in a second pass at 82's instruction** (the first pass put it on
`bkRestAtL` alone, which made the sender's `mergedObs_of_M`/`bkRestIf_of_rb` false; reverted). Its
source is the lessor's contract (`isApplyLessor`'s `⌜ttl ≤ t⌝`, from `grantTTL_ge`), which the
apply chain dropped: the record's TTL is carried up to `srvRestAt`, then to the sender, then to
`bkRestAtL`. Every statement below is true, and all are proved (no sorry added).

- New vocabulary: `leaseTTLsAbove T f := ∀ p ∈ T, sint.Z p.2 ≤ sint.Z (f p.1)` (`KVModelDefs`;
  the table's TTL is the grant's request, `backendTable`'s `(g.id, g.ttl)`), `apply.grantTTLOk rq t
  := ∀ g, rq.leaseGrant = some g → sint.Z g.ttl ≤ sint.Z t` (`Chain`).
9. `apply.grantPost` (the applier's `LeaseGrant` triples, frozen): `∃ t, E.RO (grantRest t …)` →
   `∃ t, ⌜sint.Z g.ttl ≤ sint.Z t⌝ ∗ E.RO (grantRest t …)`. Cause: Q-S6's bound (the backend's
   proof has it from the lessor's contract; capped/corrupt/rejected at `t := g.ttl`).
10. `apply.uberApplier.dispatch.spec`, `apply.uberApplier.Apply.spec` (frozen), and
   `ApplyRec`'s internal triples: the post's `∃ t, E.RO (revokeRest… (grantRest t …))` → `∃ t,
   ⌜apply.grantTTLOk rq t⌝ ∗ E.RO (…)`. Cause: the same.
11. `srvRestAt E T r` (internal): `T : List w64` → `T : LeaseTable`, its `∃ f` → `∃ f, ⌜leaseTTLsAbove T
   f⌝ ∗ E.RO (restLeasesWith f T.ids r)`; `srvRestAt_open`, `srvRest_open`, `srvRest_close` gain
   `⌜E.lg = true → leaseTTLsAbove (appliedTable γr A) f⌝`; `srvRest_applyG/P/P0/PG/R/PGR` take it
   (`hfb`) and the post's `grantTTLOk`. New pure laws: `grantRestA_leasesF`, `dispatchTable_ttls`,
   `dispatchTableA_ttls`, `chainTable_sub_nonGrant`, `dispatchTable_sub_nonGrant`.
12. The sender: `bkRestAtM M T` (`T : List w64` → `LeaseTable`, `∃ f, leaseTTLsAbove T f ∧ …`),
   `mergedObsM`'s table `if lg then kvLeases … else []`; `bkRestIf_of_rb`, `mergedObsM_of_obs`,
   `stop_mergedObs`, `stop_mergedObsP` take `hfb`. `mergedObs`'s statement is unchanged (it is
   `bkRestAtL`'s).
13. `bkRestAtL γk bootLog L D` (lease-grant's Freeze, #7's `imageAt`): `∃ f, ∀ n ∈ restBuckets, …`
   → `∃ f, leaseTTLsAbove (kvLeases γk L) f ∧ ∀ n ∈ restBuckets, …`; `bkRestAtL_of_rb` takes the
   bound. `imageLeasesAt` (round 3's) gains the same; `imageLeasesAt_recs` (DRAFT sorry) gains the
   per-record bound `∀ x ∈ recs, ∀ p ∈ appliedTable γr A', p.1 = x.1 → sint.Z p.2 ≤ sint.Z x.2.1`
   (what `Recover`'s `rq` premise takes, with `rq` the table's requests).

**Not yet applied (left for the next round; none a false statement).**

- `srvEver` keeping `leaseReqIs` (Q-S8). It threads through the apply chain's grant step
  (`applyEntryNormal`'s five `srvEver_grant`/`srvEver_same` sites): `srvEver_same`'s `everOwn E U ⊢
  srvEver …` would be false with the requests in `srvEver`, so the laws must take them and every
  caller carry them. Its only consumer is the granting walk's `Recover` pre (`⌜x.1 ∉ U⌝ ∨
  leaseReqIs …`), a DRAFT branch. Proposed: `srvEver`'s `∃ U` gains `□ [∗list] u ∈ U, ∃ r,
  lease.leaseReqIs E.γ.leases u r ∗ ⌜r = the log's request of u⌝`.
- `histCover` (internal): only the granting walk's `Recover` premise needs it; added with that proof.

**DRAFT S2–S4 sorries** (all Prove work): `LessorRecoverLemmas`: `recover_hist`'s request update,
`closers_recover`'s `hrq` step, `lessor_live_perm`; `ImageLeases`: `imageLeasesAt_recs`,
`appliedTable_mono_sub`, `appliedTable_granted_live`; `SnapRecvOn`: `hlease` with auth on; `EtcdServer__applySnapshot`: the granting walk (`lg = true`)
and the empty bucket at `lg = false`; `ApplyAllSnap`, `ApplyAllSnapOn`: the `lg = true` case.

## S2–S4 Test (2026-11-05)

`examples/etcd/leasesnap/leasesnap_test.go` (build tag `leasesnap`; the examples module lacks the
integration framework's dependencies, so it runs as a package of etcd's `tests` module in a scratch
checkout of the fork at `673da07c8fab`, the file's header says how). Two tests, no proof; 3 of 3 runs
pass, nothing contradicts a spec.

- `TestLeaseSnapshotRestore`, etcd's integration framework: three members, `SnapshotCount` 10,
  `SnapshotCatchUpEntries` 5, members restarted with different `ElectionTicks` (the framework takes
  per-member config by editing `Member.ElectionTicks` before `Restart`): `minLeaseTTL` 1, 30, 90
  (m0, m1, m2). Grants of 20 and 200 through each member; then three restores, each a member
  stopped, the leader writing past two snapshots, the member restarted and logging `restored lease
  store` (`applySnapshot` → `lessor.Recover`): m0 (min 1) from m2 (min 90), with a lease granted and
  one revoked while it was down; m2 from m0 (records 30 < m2's 90); m0 again from m1 (min 30). The
  lessor is read through `EtcdServer`'s unexported field, the bucket with `MustUnsafeGetAllLeases`.
- `TestLessorRecoverMinTTL`: lessor B (min 2, then 10) with its own leases `Recover`s A's backend
  (min 10, then 2).

Claims: (1) `Recover.spec`: after each restore the lessor's ids are exactly the bucket's records
(the revoked lease gone, the one granted while down present, a lease live before and recorded still
live; in the unit test B's own unrecorded lease gone), each TTL `max(record, own min)` (m2: records
30 → TTL 90). PASS. (2) `leaseTTLAt_ge_req`: every lessor TTL, record and `TimeToLive`'s
`GrantedTTL`, on every member at every check, ≥ the request. PASS. `GrantedTTL` differs across
members (lease requested 20: 20 with m0 leading, 90 with m2 leading) and across one member's restores
in both directions (m0 leading: 20, then 90 after restoring m2's image, then **30** after restoring
m1's: the TTL is not monotone, only bounded below by the request). (3) `Grant.spec`: each answer's
TTL `max(request, the proposing member's min)` (20→20, 30, 90; 200→200), each member's lessor and
record `max(request, its own min)`. PASS. (4) The lease bucket: at every check, on every member, one
record per lessor lease, no duplicate, TTL ≥ request. PASS (checked on the live backend at quiescent
points, the leader's after its snapshots and the restored member's, which is the image received;
not on the snapshot file itself).

Seen on the way (no spec claims otherwise): after a restore a member's bucket and lessor disagree
on TTLs (m2: record 30, lessor 90), since `initAndRecover` does not rewrite records; and right
after a leadership change `TimeToLive`'s remaining `TTL` exceeds `GrantedTTL` (149 against 90:
`Promote` extends by the election timeout). `nonissues/etcd-lease-ttl-differs-across-members.md`
("no test") is now reproduced by this test.

## Scope candidate: discharging `srvRevokeOpen_open` (2026-11-05; parked until S2–S4 lands)

Status: a candidate, not yet brought to the user (etcd-grove-82 brings it when it is next in the queue). It is a
stage of its own (spec-first: Scope → Freeze), after S2–S4, because both change `run` and `NewServer`.
It takes the trust base from 4 sorries to 3. Below: the design (a read-only design agent), then the
feasibility probe of its hard stops 6–7, then the open points.

### Open points before Scope
- **Levels need `threadBound` large enough.** A thread token holds levels `l < threadBound GF`, and
  Perennial guarantees only `1 < threadBound` (`Threads.lean:83`). The design uses levels up to 7. The
  closed theorems fix `threadBound GF = n + 2` (`etcdstart/Adequacy.lean:115`), so either they take
  `n ≥ 6`, a scope premise on exported results (a hard stop), or the design uses fewer levels, e.g. one
  leveled pool of the bundled readers at a single level. To settle in the Scope.
- **Q6 (E.RD).** The probe recommends raising `backend.authRdN` to `2^28 + 2^7`. It is true of Go,
  costs about 40–60 lines, and changes the exported backend API (`authRdN`, `rdStockN_val`) and the count in
  the trusted premise `authSchemaSrv`, which gets an axiom-skill review. Alternative: a mode split in
  `authStoreKit`, which reverses the user's N2.
- **Q7 (lgMu).** Level `raftPool` and share it. It needs no frozen, exported or trusted change and costs
  about 50–70 lines. Shrinking `httpProcSlots` would strengthen a trusted assumption, so it is rejected.

### The design
#### Design: discharging `srvRevokeOpen_open`

The sorry can be removed without new axioms, but the change is not small and has more hard stops than the five needs listed in the lease-expiry plan. Two resource supplies are too small for any thread-token design, and those two are where I am least sure. No upstream (Go) change is needed, and no Perennial change: P1 at `84d538063` is enough.

## 0. Go code: no bug found

I read `server.go:860-905` and `GoAttach` at `:2435`. Nothing panics as long as each `*Lease` in the slice is non-nil, which `lease.expiredLeases` gives.

If an inner `GoAttach` is skipped because the server is stopping, nothing ever runs `<-c`. The outer `select` still exits, because `stopping` is closed by then, so this is not a deadlock either. Nothing goes in `issues/`.

## 1. Threads

**Why pools are unavoidable.** Each round leaves up to 16 inner goroutines alive. `run` starts a new round every tick without waiting, and an inner goroutine may block forever, as far as the proof can see. So the number of live outer and inner goroutines is unbounded.

- Any per-round supply of reader slots from `run`, or carried through `c`, runs out.
- The only sound bound is the thread-token count. Every reader slot an expiry goroutine uses must come from a leveled pool (`threadPool.isThreadPoolL`) with at least `threadBound GF − 1` copies, borrowed with a level token the goroutine holds.

**The channel `c`.** It needs no ownership. Model it as a bag with predicate `True`: the sends and the `<-c` carry nothing, and the bound comes from the thread tokens, not from `c`. This replaces need 4 of the plan.

**Which wait group becomes leveled.** Only the server's `s.wg`, with pending level `p = 1`.
- `sync.tokJoinL` cannot be used directly: its `ownAdder` is exclusive, while `GoAttach`'s adders are concurrent `wgMu` readers.
- Instead, re-prove `goAttachInv` (`InvGoAttach.lean:98`) in `tjInv`'s leveled form. `threadToks k` becomes `levelToks 0 d ∗ levelToks 1 q`.
- `wp_goAttach_Add` takes `levelTok 1`. The fork (`tokJoinL.start`-style, by `wp_fork_tok_upd`) puts the fresh token's level 0 in the slot and hands `levelTok 1` back. `wp_goAttach_Done` returns `levelTok 0`.
- The counter stays below `2T`, so `srvGoAttachOk`'s `⌜threadBound GF ≤ 2 ^ 31⌝` (`InvGoAttach.lean:122`) becomes `⌜2 * threadBound GF ≤ 2 ^ 31⌝`. That holds because `threadBound GF ≤ 2^28` (`isServer`).

**`GoAttach.spec`: one spec, generalized.** The new spec implies the old one. Its callers are `Start`, `applyEntryNormal` (×3), `sendMergedSnap` and v3rpc `monitorLeader`. They switch to a corollary `wp_GoAttach_tok` in `InvGoAttach.lean`, which states the old triple: split `threadTok = levelTok 1 ∗ …` and frame `threadTokFrom 1` through `f`.

```lean
abbrev EtcdServer.GoAttach.spec : Prop :=
  ∀ (s : Loc) (γ : GoNames) (f : GoFunc) (P : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvWgReaderAt s γ ∗ levelTok 1 ∗ srvLgReader s ∗ P ∗
      {{ P ∗ goRunning γ ∗ threadTokFrom 1 }} (App (Val #f) (Val #()))
        {{ RET #(); goRunning γ ∗ threadTokFrom 1 }} }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"GoAttach")) (Val #f))
  {{ RET #(); srvWgReaderAt s γ ∗ levelTok 1 ∗ srvLgReader s }}
```

**`run`'s token.** `start` forks `run` with plain `wp_fork` (`EtcdServer__start.lean:534`), so `run` holds no token. Switch to `wp_fork_tok_body`: `run` gets a fresh `threadTok` from the fuel and keeps it forever. Each round it:
- gives up `levelTok 1` to the outer `GoAttach` and gets it back at the fork;
- borrows a `wgMu` slot from the pool with `levelTok 3` and gives it back after the call;
- uses its own `Hlr` (`srvLgReader`).

**The outer goroutine** holds `threadTokFrom 1`.
1. It borrows `lgMu` (level 2) for `Logger()`.
2. It borrows `read.mux` (level 4) and calls `ensureLeadership` with `levelTok 7`, then returns the `read.mux` slot.
3. It borrows `wgMu` (level 3). Each inner `GoAttach` then uses its `levelTok 1` plus the held `wgMu` and `lgMu` slots.
4. It returns everything to the pools before exiting.

**Each inner goroutine** holds `threadTokFrom 1`.
- It borrows `leadTimeMu` (level 5) and `E.RD` (level 6) for `WithRoot` and `LeaseRevoke`. `LeaseRevoke` takes no thread token.
- It gives both back and calls `Done` for `levelTok 0`, so it exits with a whole `threadTok`.

**Why `threadBound` is never exceeded.**
- Every live goroutine (`run`, outer, inner) is one token from the fuel.
- At most `T − 1` borrowers per pool: each borrower has deposited a distinct token of that pool's level.
- The `wg` counter equals level-0 slots plus level-1 pendings, which is below `2T`.
- So overlapping rounds are fine.

**`ensureLeadership`'s trusted contract** (`Spec/.../EtcdServer__ensureLeadership.lean:44-49`): `threadTok` becomes `levelTok l` for a caller-chosen `l`, in and out. Its faithfulness argument (`tickMu` readers ≤ live goroutines < 2^30) never used the token's identity, only adequacy's thread bound. The other caller, `LeaseRenew`, splits off one level.

## 2. The restated spec (frozen: hard stop)

Old: the text at `Spec/.../EtcdServer__revokeExpiredLeases.lean:39-47`, whose precondition ends with `lease.expiredLeases …` and whose post is `True`. New:

```lean
abbrev EtcdServer.revokeExpiredLeases.spec : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF)
    (ρ : ReqNames) (v : SrvFields) (γr : ReadNames) (γg : GoNames)
    (γcx : context.ContextNames) (rv : RunFields) (SP : IProp GF) (ls : GoSlice) (ρq : ReqNames),
  srvRevokesLeases E ρq →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvFieldsAt s γ ci TM E ρ v ∗ srvRunFieldsAt s γr γg γcx rv SP ∗
      lease.expiredLeases (srvGrantGuard E.lg E.authMode.isOn) ls ∗
      srvRevokeCtx s E ρq γr γg ∗ srvLgReader s ∗ threadTok }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"revokeExpiredLeases")) (Val #ls))
  {{ RET #(); srvLgReader s ∗ threadTok }}
```

The new bundle is sealed, persistent, in `LeaseRun.lean`, opened by laws:

```lean
@[no_expose] def srvRevokeCtx (s : Loc) (E : apply.AEnv GF) (ρq : ReqNames) (γr : ReadNames)
    (γg : GoNames) : IProp GF :=
  iprop(isServerReq s E ρq ∗ isServerRead s E γr ∗ □ (|==> idCred ρq.ids 1) ∗
    (∃ (c : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
      srvCtxAddr s ↦□ GoInterface.ok c ∗ context.isContext c cd) ∗ srvWithRootOk s E ∗
    (∃ γp, threadPool.isThreadPoolL srvRvkN 2 γp (srvLgReader s)) ∗
    (∃ γp, threadPool.isThreadPoolL srvRvkN 3 γp (srvWgReaderAt s γg)) ∗
    (∃ γp, threadPool.isThreadPoolL srvRvkN 4 γp (srvReadReader s γr)) ∗
    (∃ γp, threadPool.isThreadPoolL srvRvkN 5 γp (srvLeadTimeReader s)) ∗
    (∃ γp, threadPool.isThreadPoolL srvRvkN 6 γp E.RD))
```

`ρq` is a separate binder because `Start` hands out `{ρ with wait := γw}` for the request side. I am unsure whether `ρq = {ρ with wait := γw}` exactly.

Where each resource comes from at `run`'s call site (`EtcdServer__run.lean:1372-1385`):

| Resource | Source |
|---|---|
| `srvRevokesLeases E ρq` | `lease.runCfg_lm Hmo` (`γr.kv.lm = .revocable`), `ρq.rd = γr`, and `E.authOn = false` from `hCoff` |
| `threadTok` | new conjunct of `isServerRun`, from the fork |
| `srvLgReader` | `"Hlr"` |
| `isServerReq`, `isServerRead`, `idCred` (`#HNR`), `isContext` (`#Hcctx` from `wp_WithCancel_Background`) | all already persistent in `start`'s context |
| `wgMu` and `read.mux` pools | carved in `start` from `srvStartReaders`' stocks (2^28 each, `InvStart.lean:317-330`) |
| `leadTimeMu` pool | carved in `NewServer` from the discarded rest (`NewServer.lean:1408`) |
| `lgMu` pool, `E.RD` pool | **see hard stops 6–7** |
| `srvWithRootOk` | from the auth store's construction (§3) |

Pools and facts built in `NewServer` reach `start` through one new sealed conjunct of the construction premise, `srvRevokeBuilt s E`.

Frozen or exported statements this changes (all hard stops):
- `revokeExpiredLeases.spec` (frozen).
- `isServerRun`/`isServerRunC`: gain `"Htok" ∷ threadTok` and `"#Hrvk" ∷ srvRevokeCtx …`.
- `isServerBuilt*`/`srvBuiltG` bodies: gain `srvRevokeBuilt`. The text of `NewServer.specG` is unchanged.
- `run.spec`/`run.specStop` post: `True` becomes `threadTok`.
- `srvGoAttachOk` body: the `2T` bound.
- `srvStartReaders` stock counts. `Start.spec`'s text is unchanged; what the post hands out shrinks.
- `GoAttach.spec`: an API change.
- `ensureLeadership.spec`: an axiom statement.

Unchanged: `srvRevokeOpen`'s text, `Main.spec`, `isServerReq`.

## 3. Callee specs that don't exist yet

| Callee | What exists | Proposal |
|---|---|---|
| `zap.Logger.Warn`, `zap.Uint64`, `zap.String`, `zap.Error`, `MemberID`, `Logger` | All exist (`Spec/go_uber_org/zap/`, `EtcdServer__MemberID`) | Nothing new |
| `fmt.Sprintf("%016x", lid)` | `Spec/fmt/Sprintf.lean` | Reuse it for an `int64` argument. Not checked; `SprintfID` is the fallback |
| `leaseExpired.Inc()` | Its initializer is in `opaqueInitsOk` (`Init.lean:356`): no fact | **Preferred:** translate the initializer and prove it from the existing `prometheus.NewCounter.wp_proof` (an existing axiom; no growth). **Fallback:** a `leaseExpired_init` axiom like `proposalsFailed_init` (`Init.lean:155`): +1 axiom, hard stop |
| `authStore.WithRoot` | Not translated (`auth.toml`) | Add it to `translate`. Prove `auth.authStore.WithRoot.specOff` over the existing `IsAuthEnabled.spec`: at auth off it returns `ctx`. Add a contract `isAuthRoot st RD M` (below) to the auth store construction's post beside `isReqAuth` (an auth API change), derived in `AuthReqDerive.lean`; `srvWithRootOk` wraps it |

The `WithRoot` contract:

```lean
def isAuthRoot (st : GoInterface) (RD : IProp GF) (M : auth.AuthMode) : IProp GF :=
  iprop(∃ ai : GoInterfaceOk, ⌜st = GoInterface.ok ai⌝ ∗ □ (∀ ctx : GoInterface,
    {{ RD ∗ ⌜M.isOn = false⌝ }} (App (Val #(methods ai.ty go!"WithRoot" ai.v)) (Val #ctx))
    {{ RET #ctx; RD }}))
```

Unsure: whether goose's reach for `WithRoot` (gRPC `metadata`, `tokenSimple`) needs new names-only packages. If it cannot be translated, the fallback is a contract axiom, which is trust-base growth.

## 4. Bounds accounting

- `spec-thread`: the spec mentions no `threadBound`; the pools hide it. `ensureLeadership.spec`'s `≤ 2^30 − 1` stays. Expected Δ = 0.
- `stock`: same number of `List.replicate` matches; only the counts change.
- `etc/bounds-check.py --check` should pass unchanged, maybe with `bounds-allow.txt` entries for the pool construction sites.

Each pool lives in its lock's owner:

| Pool | Owner file |
|---|---|
| `wgMu` | `InvGoAttach` |
| `read.mux` | `InvRead` |
| `leadTimeMu` | `InvProposer` |
| `lgMu` | `InvApplier`, or shared with the transport's `raftPool` |
| `E.RD` | auth/backend (`RdPool.lean`) |

They are bundled once, sealed, in `LeaseRun`.

## 5. Commit order and size (each step proves only true statements)

1. **Leveled `s.wg`.** `goAttachInv`, Add/Done, the `2T` bound, the generalized `GoAttach.spec`, `wp_GoAttach_tok`, the 6 call sites. About 300 lines; everything proved.
2. **`ensureLeadership` contract to `levelTok l`.** Run the `axiom` skill first, then `LeaseRenew`. About 30 lines; needs user approval.
3. **Callees.** `WithRoot` (goose config, regeneration, proof, `isAuthRoot` through the auth store's post) and `leaseExpired`'s initializer. About 250 lines plus the regenerated translation.
4. **Pools and plumbing.** `NewServer` and `start` pools, `srvRevokeBuilt`/`srvRevokeCtx`, `isServerRun` (+`threadTok`), the `run` fork, `run`'s post. About 400 lines. Do it only after hard stops 6–7 are settled: the pool inits need `threadBound ≤ n + 1`, which is false for `E.RD` today (128 copies).
5. **The spec and the proof.** Restate `revokeExpiredLeases.spec`; add `revokeExpiredLeases.wp_proof` (about 400 lines); change `run`'s call site; add `srvRevokeOpen_proved`; replace `srvRevokeOpen_open` in `leaseexpiry/MainLinked.lean`; delete the sorry. Trust base goes from 4 sorries to 3 (lean's count after revRoom; corrected 2026-11-05) (`--check --update`, `tcb-collections/leaseexpiry.txt`).

Total: about 1,400–1,800 lines over 5 commits.

## Hard stops

1. **Frozen spec restated:** `EtcdServer.revokeExpiredLeases.spec`.
2. **Trusted axiom restated:** `ensureLeadership.spec`, `threadTok` to `levelTok l`.
3. **Exported definitions and statements changed:**
   - `isServerRun`/`isServerRunC`, `isServerBuilt*`/`srvBuiltG` bodies, `srvGoAttachOk` (bound), `srvStartReaders` counts;
   - `run.spec`/`run.specStop` posts;
   - `GoAttach.spec` (an interface diff);
   - the auth store's post (gains `isAuthRoot`).
4. **Goose configuration:** `auth.toml` (`WithRoot`), and `etcdserver.toml` plus `gen-init.py` `SPECIAL` (`leaseExpired`).
5. **Possible trust-base growth:** a `leaseExpired_init` axiom, or a `WithRoot` contract axiom, only if the preferred routes fail.
6. **`E.RD` supply too small:** `backend.authRdN = 2^7` (`RdPool.lean:45`, `NewServer.lean:918-925`), so no `E.RD` pool can be built. It must rise to at least 2^28, which touches the backend and auth construction. **I have not checked that this is feasible.** It is the main risk.
7. **`lgMu` stock too small:** `NewServer` has about 2^28 − c slots left after `httpProcSlots` (2^29) and `raftPool` (2^28, `:577`), short of the 2^28 − 1 a pool needs. Options:
   - make `raftPool` leveled and share it (this touches rafthttp; check whether a trusted Transport axiom names it);
   - or shrink `httpProcSlots`, which changes `NewServer.specG`'s post.
   - Unsure which is smaller.

### The feasibility probe (hard stops 6–7)
**Q6 and Q7: feasibility of the E.RD and lgMu supplies (read-only; nothing built or checked)**

Neither is a blocker: both have a true route. Q6's route needs a hard-stop approval; Q7's does not. Separately, I found a gap that affects the whole design (third section).

**Q6: E.RD**

(a) What it is and where it comes from:
- `AEnv.RD` is "the auth store's reader resource" (`apply/Chain.lean:614-620`). At the real server it is `auth.authRd stp R M = enabledRd ∗ cacheRd ∗ beRd ∗ R` (`InvAuth.lean:2495-2523`, `AuthSrv.lean:555-570`). That is three RWMutex reader slots of the auth store plus a ticket `R` backed by a backend reader slot.
- The expiry path really uses it. `LeaseRevoke.spec` takes `E.RD`. `processInternalRaftRequestOnce` uses it for `AuthInfoFromCtx` (its spec, lines 31 and 72), which calls `IsAuthEnabled`, i.e. `enabledMu.RLock()` (`store.go:937-940`). `WithRoot` also calls `IsAuthEnabled` first (`store.go:1159-1161`). So an unbounded number of goroutines take `enabledMu` reader slots. That is real, not an artefact of the proof.
- Mode off: the `NewAuthStore` axiom gives `actualMaxReaders` (2^30−1) copies. `authStoreKit_off` keeps `authRdN−1` and throws the rest away (`AuthSrv.lean:322-326`).
- Mode on: `authSchemaSrv` (`AuthSrv.lean:~70-118`) gives `authRdN` tickets in exchange for `authRdSlots d = backend.rdAuth` (`AuthSnapKit.lean:38-44`). `authSchemaSrv` is a trusted named premise of the exported auth-on results (`examples/etcd/auth/Results.lean:67,81`; `etcdserver/Results.lean:2036,2082`). `newAuthStore_on` is then called with N = `authRdN−1` (`AuthSrv.lean:458-467`).
- Both modes post `authRdSupply` = `authRdN−1` copies (`AuthSnapKit.lean:48-54`). `NewServer` takes 1+1+64+1 = 67 of them (`NewServer.lean:918-929`).
- Why 2^7: a local choice, "≥ the 67 copies NewServer hands out" (`notes/snapshot-auth-on-plan.md:115`, `notes/decisions.md:30668`). No Go bound and no axiom fixes it. It sits in the backend's partition `rdPoolN + authRdN + rdStockN = actualMaxReaders` (`RdPool.lean:41-58`).

(b) Users of `authRdN`: `RdPool.lean` (the partition, `rdAuth`, `bkRPool`, `rdToks_pool`), `AuthSnapKit.lean:54`, `AuthSrv.lean:104,323-325,460-467,566,589`, `NewServer.lean:920,1159`, `StopShutdown.lean:241`. Through `rdStockN`/`mvcc.nReaders`: `mvcc/InvStore.lean:5040`, `New.lean:76`, `NewStore.lean:39,97`, `ReaderRetire.lean:155`, `store__Restore.lean:884`, `newWatchableStore.lean:214`, `RestoreMoves.lean:631`, `RestoreCmp.lean:198`, `SnapApplyWalk.lean:714`, `SnapRestoreM.lean:236`, `StopShutdown.lean:583`, `NewServer.lean:759`. Every one of these needs only "positive" or "≥ a few hundred".

(c) Raising it to `authRdN = 2^28 + 2^7`. The pool needs `authRdN − 1 − 67 ≥ 2^28 − 1`.
- `rdStockN` becomes 2^30−1−2^28−(2^28+2^7) = 536870783.
- Statements that change:
  - **Exported (backend API):** the body of `backend.authRdN` and the statement of `rdStockN_val` (`interface/.../backend/RdPool.txt:50,100`; `etc/api/backend.txt:29`). The interface must be regenerated.
  - `mvcc.nReaders_val` (`InvStore.lean:5040`).
  - The literal `hAN` (`NewServer.lean:920`); the `decide` lines at `AuthSrv.lean:323,460` still pass.
  - **Trusted premise:** `authSchemaSrv`'s text is unchanged, but its ticket count grows. Review it with the `axiom` skill: it stays symmetric, taking `authRdN` slots for `authRdN` tickets.
  - No axiom changes.
- It is true of Go. Per backend, the `readTx` RWMutex partition is 2^28 + (2^28+2^7) + the rest = 2^30−1, within Go's 2^30. The auth locks need N ≤ 2^30−1. Live RLocks are bounded by threads anyway.
- Size: about 40–60 lines plus the interface regeneration.

(d) Alternatives:
- There is no existing E.RD pool. The only `isThreadPool` users are `rafthttp/Net.lean`, the lessor and the backend's `rdPool` (which holds `rdTok`, not E.RD).
- `srvRevokesLeases` forces `E.authOn = false` (`LeaseRevoke.lean:37-38`). So a mode split works: in non-on modes `authStoreKit` would post 2^28 more of the `RD` copies `authStoreKit_off` discards today. It is true and leaves the backend, mvcc and `authSchemaSrv` alone.
- But it reverses the user's decision N2 ("no mode split, no `actualMaxReaders` stock", `snapshot-auth-on-plan.md:130-131`) and changes `authStoreKit`, which `authSrvTP`/`NewServer.specM` use as a premise. I am unsure how mode `any` would be handled.
- **Recommendation:** raise `authRdN`. Hard stops: the backend API diff and the larger count in the trusted premise.

**Q7: the lgMu stock**

The facts:
- The total is Perennial's `sync.init_RWMutex`, `actualMaxReaders` = 2^30−1 (`NewServer.lean:555,565`), which matches Go's 2^30. It cannot change.
- It is split into `httpProcSlots` 2^29 (`:572`), `raftPool` 2^28 (`:577-578`) and about 70 fixed slots (`:579`, `:1568-1578`).
- `raftPool` cannot go below 2^28−1 while `threadBound ≤ 2^28`, and lowering `threadBound` would undo the approved J8a-6 statement (`notes/decisions.md:28583-28600`). So (iii) offers nothing cheap.

(i) Level `raftPool` and share it. **This is the cheapest route.**
- `raftPool R := ∃γ, threadPool.isThreadPool raftPoolN γ R` (`rafthttp/Net.lean:262`), built with `threadPool.init` (`:279`).
- Its only consumers are proved code: `startPeer` borrows and gives back (`startPeer.lean:112`), and `Transport.Start.spec` takes `raftPool R` by name (`Spec/.../Transport__Start.lean:57`). There is no Transport axiom, rafthttp has no `etc/api` list, and nothing is in `interface/`.
- Change: `raftPool R := ⌜l < threadBound GF⌝ ∗ ∃γ, isThreadPoolL raftPoolN l γ R`, and `raftLoan` keeps the levels a borrower did not lend.
- `raftPool_borrow`/`raftLoan_giveBack` keep their statements (`threadTok` in and out), split with `threadTokFrom_succ` (`Threads.lean:357`). Add `borrowL`/`giveBackL` laws for holders of a level token.
- The expiry goroutines then borrow from `NewServer`'s existing `#HrPool`, so no new stock is needed.
- No exported, frozen or trusted text changes. About 50–70 lines.

(ii) Shrink `httpProcSlots` (2^29, `net/http/Boundary.lean:186`). This is the worst option.
- It appears in the trusted `Serve_spec` (`Boundary.lean:571-578`), a physical assumption about concurrent handlers, and in `NewServer.specG`'s post (`Spec/.../NewServer.lean:339`), which `etcdstart/Defs.lean:322` consumes.
- Shrinking it makes a trusted assumption stronger, and I cannot show the stronger one is true.

**A gap in the design itself (not Q6 or Q7)**

A thread token holds only levels `l < threadBound GF` (`Threads.lean:124`, `:362-366`), and Perennial guarantees only `1 < threadBound` (`:83`). The design uses levels up to 7, so it needs `8 ≤ threadBound GF` somewhere. I found no lower bound in the etcdserver proofs; `isServer` has only `threadBound ≤ 2^28` (`NewServer.lean:377`). Route (i)'s level needs the same.

Whether the closed theorems' choice of `threadBound` makes such a premise harmless is something I have not checked.
