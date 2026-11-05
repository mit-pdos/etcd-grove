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
