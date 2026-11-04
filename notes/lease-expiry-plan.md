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
