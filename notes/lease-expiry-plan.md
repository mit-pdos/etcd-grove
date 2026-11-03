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
`leaseMap`/`itemMap`, and `initAndRecover` (`:770`) reads every record of the new backend's `lease`
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
