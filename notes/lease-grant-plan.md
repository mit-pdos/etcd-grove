# The closed lease-grant example (2026-11-02; branch `lease-grant`)

The stage after `notes/lease-ex-plan.md`: a Go program that grants a lease through etcd's client and
then lists the leases, with a closed theorem that it does not panic. Lean-first (no Rocq
counterpart). It is `notes/leases-plan.md`'s L3c (grant half) and L4 (`EtcdServer.LeaseGrant`),
cut to what the example needs.

## Scope (2026-11-02; the user's choice: "Grant, then Leases")

`examples/leasegrant`'s `Main` starts one member, serves it, connects a client,
`cli.Grant(ctx, 600)` (returns on an error: a server-chosen id can collide, `ErrLeaseExists`, and a
call can time out), then `cli.Leases(ctx)`, and panics unless the granted ID is listed. Auth off.
Revocations stay out of the server's workload (`rqOk .leaseRevoke = False`, as on `lean`); expiry
stays out (`notes/leases-plan.md` Q1(b), the user's choice of 2026-10-24).

## What is missing (the survey, 2026-11-02)

The grant is closed at five places on `lean`:

1. **No guard.** The server's grant guard `srvGrantGuard` (`InvApplier.lean:473`) is `False`:
   `NewLessor`'s `GA`, which every grant needs (`leaseGranted`). `lessorOk`'s `ExpiredLeasesC`, the
   dead expiry arms of `run` and `UberOn`'s `lookupNil` rely on it being `False`: expiry and the
   guard must be separated (a trust-boundary contract, `lessorOk`; the `NewLessor` axiom).
2. **No proposal.** `reqPropOkW` (`InvRequest.lean:567`) takes `plainReq`; `plainCover`
   (`KVModelDefs.lean:72`) has no grant.
3. **No apply.** `rqOk .leaseGrant = False` (`apply/Chain.lean:264`); the dispatch arms close by
   absurdity; `isApplyLessor`'s Grant clause (`apply/Contracts.lean:360`) is not exact (no
   `id' = id`, no `L ++ [id]`); `applierV3backend.LeaseGrant.spec`'s post says nothing of the live
   set; the apply thread does not lend `AEnv.RW` (the lease bucket's write).
4. **Nothing reaches the caller.** A request's reply (`appliedOk`, `InvProposer.lean:505`) carries
   no lease state.
5. **No lower bound on reads.** `lessor.Grant.spec` (exact: `L ++ [id]`, errors iff `id = 0`,
   `ttl > MaxLeaseTTL` or `id ∈ L`) returns no fact of the lessor's history; `lessorRdBody` does not
   say that a live id stays live; `kv_lease_served` fixes `lessorLb γl 0` once; the client's
   `etcdLeaseLeasesSpec` says only `Nodup`, `etcdLeaseGrantSpec` only `id ≠ 0`.

Also on the path: `EtcdServer.LeaseGrant` (`v3_server.go:434-456` at the pin: `r.ID = Next() &
(2^63-1)` until nonzero, `requireAuthInfo`, `raftRequest`, the response's type assertion), unproved;
the snapshot walk's empty-lease-bucket premise `hlease` (`SnapApplyWalk.lean:67`), false once a
grant is applied (a single member is never sent a snapshot, but `run`'s proof is generic);
`kv_lease_served` without the Grant method.

`notes/leases-plan.md`'s own L3b/L3c tie the model's lease table to the lessor's live set
(`leasesLive`: `L = lt.ids`, `ApplyKV` carrying the table) and move the server's results to
`kvModelSt γk Lq`; the example does not need that tie (below, S1).

## Scope questions (for the user)

- **S1. How far the apply side goes.** (a) *Narrow* (recommended): the grant admitted through the
  request path and the apply thread, its fact taken from the lessor's history (a persistent
  "`id` live from index `i`", `leaseLiveFrom`), handed to the caller through the reply; the KV
  model's table stays untied to the lessor (L3b's tie, leased puts and the results at
  `kvModelSt γk Lq` later). (b) *Full L3b/L3c*: the table tied to the lessor, leased puts and
  transactions admitted, the server's results restated at the table; the example on top.
- **S2. Expiry.** A lease the example grants must not expire before `Leases` runs (TTL 600 s; the
  run takes seconds). (a) *A named deployment premise* (recommended): `opaque leasesNoExpiry : Prop`,
  as `leasePeersOk`, a hypothesis of `leasegrant_safe`, under which `lessorOk`'s `ExpiredLeasesC`
  carries nothing (a restated trust-boundary contract). (b) The same as an unconditional trusted
  change to `lessorOk` (no premise in the result).

**Decided (the user, 2026-11-02):** S1 (a), narrow; S2 (a), the named premise `leasesNoExpiry`.

## Stages

Draft → Review (an independent spec reviewer) → Test (the Go test) → the `axiom` skill on every new
or restated trusted statement → Probe → Freeze (the user) → Prove.

## Draft (2026-11-02)

Statements in code, proofs `sorry` where not done; the build passes. Commits on `lease-grant`:
the example and its translation; D1-D2 (wired through the server, proved but for one `sorry`); the
grant's specs (D4-D5) and the example's theorem (statements, `sorry`); D3's statements and the wire
model's owned `ID`.

### D1. Expiry apart from the grant guard (done, proved)

- `lease.leasesNoExpiry : Prop` (`LessorBackend.lean`, opaque): the deployment premise "no lease the
  run grants expires before it ends". Why true here: the TTL is 600 s (`grantTTL`), the run takes
  seconds; Go would otherwise expire it (`lessor.go` `revokeExpiredLeases`, `findExpiredLeases`).
- `lessorExpiredC lp GA` (restated trusted contract, `NewLessor`'s post): a slice on `expiredC`
  carries `⌜¬ leasesNoExpiry⌝ ∗ ∃ id, GA id` (was `∃ id, GA id`). True of Go: the loop sends only a
  non-empty slice of expired leases (`lessor.go:652`), which under the premise does not exist.
  `lessor.ExpiredLeasesC.spec` (proved, generic) and `lessorOk`'s `ExpiredLeasesC` clause follow.
- `srvGrantGuard lg on := ⌜leasesNoExpiry ∧ lg = true ∧ on = false⌝` (was `False`), `lg` the new
  `KVNames.lg` (default `false`: every existing example unchanged). `run`'s expiry arms are dead in
  every cluster (`srvGrantGuard_expired`); with `lg = false` or auth on the guard is `False`
  (`srvGrantGuard_false`), so `lookupNil_of_guard` keeps the auth layer's `srvLessorNil`.
- `NewServer.specM`/`specG`'s post: `srvLessorNil srv` → `□ (⌜on = true⌝ → srvLessorNil srv)` (its
  only user, `authkv`'s `startServer`, is auth on).

### D2. The lessor's monotone mode (done, proved; `run`'s lease-granting snapshot case a premise)

- `LessorRdNames := GName × GName × Bool`: the third component the **mode**, pinned with the names;
  `lessorRdBody` gains `⌜γr.2.2 = true → histMono hs⌝` (no lease leaves a later lease map).
- New (`InvLessor.lean`): `histMono`, `lessorModeIs γl mono`, `lessorRevocable γl` (mode `false`),
  `leaseGrantedAt γl i id` (mode `true` and `id` live at index `i`); laws `leaseGrantedAt_lb`
  (`lessorLb γl i`), `leaseGrantedAt_of_live`, `lessorModeIs_pin`, `lessorModeIs_agree`,
  `leaseGrantedAt_listed` (`lessorRdInv ∗ leaseGrantedAt γl i id ∗ leaseIdsAt γl j ids ∗ ⌜i ≤ j⌝ ⊢
  |={E}=> ⌜id ∈ ids⌝`); `histMono_snoc` (`LessorHist.lean`). All proved.
- `lease.NewLessor.spec` (axiom, restated): a new argument `mono : Bool`, post `lessorModeIs γl mono`
  (ghost only: the history is `[(∅, ∅)]`, monotone trivially).
- `lease.lessor.Recover.spec` (axiom, restated): pre `lessorRevocable γl` (its `(∅, ∅)` snapshot drops
  the live leases, which a monotone history forbids). The least change: `Recover` is called only on
  the snapshot path, which in a cluster that grants leases is not proved anyway (its image has
  leases: `specSnap`'s `hlease` is false there).
- `lease.lessor.Revoke.spec` (proved): pre `lessorRevocable γl`. Revocations stay out of the
  workload (`rqOk .leaseRevoke = False`): the apply chain's `revokeClause` and `revokeRes`/
  `revokeResAfter` carry it (no user constructs them: the arms are dead).
- `lease.lessor.Grant.spec` (proved): success post `leaseLiveFrom γl 0 id l` (the snapshot `Grant`
  appends, `closers_grant`).
- The server: `NewServer` creates the lessor at mode `ρ.rd.kv.lg`; `srvSnapRO` keeps
  `lessorModeIs E.γ.leases γr.kv.lg`; `applyAll.specSnap` takes `γr.kv.lg = false` (as it takes
  `E.cmp = false`), `applySnapshot.specSnap` and the walk take `lessorRevocable E.γ.leases`; `run`'s
  snapshot job splits on `lg`. The case `lg = true` (the snapshot job in a cluster that grants
  leases; a single member is never sent a snapshot) is not proved, and is a **premise**, not an
  inline `sorry` (which would be in the trust base of every result resting on `run`, granting or
  not; the coordinator's review, 2026-11-02): `runSnapLgOk` (`InvRun.lean`, the job's triple at
  `lg = true`) enters as `ρ.rd.kv.lg = true → runSnapLgOk`, a pure row `%Hslg` of `NewServer`'s
  precondition (`spec`/`specM`/`specG`), carried as `diskOk` is (`srvBuilt`, `srvBuiltG`,
  `isServerBuilt(On)`, `isServerRun(On)`) to `run_job_snap`'s premise `hslg`. The examples' boot
  bundle `memberBoot`/`memberBootOn` gets the same conjunct, which the allocations discharge by
  their names' `lg = false` (`srvClusterBoot(On)_alloc` now state `γk.lg = false`,
  `srvMemberBoot(On)_alloc` `ρ.rd.kv.lg = γk.lg`; `memberBoot_of` takes `γk.lg = false`).
  `runSnapLgOk_open` (`EtcdServer__run.lean`, **new `sorry`**) discharges it; only
  `leasegrant.Main.wp_proof` takes it (a premise `hslg`, `MainLinked` passes it).

### D3. The grant through the request path and the apply thread (statements in code)

(Revised by the review, 2026-11-02: the `lg` siblings and second specs are gone, S6/B1; see
"Review (2026-11-02)" for the in-place design and why it is not yet in code.)

- trusted (`isApplyLessor`'s Grant clause, `Contracts.lean`; derived for the real lessor in
  `LessorDerive.lean`, proved): post `(Post ∨ Pre) ∗ (∃ L' ⊇ L, leaseOwn L' ∗ leaseRevokers L' ∗
  (err ≠ nil ∨ ∃ id' ∈ L', leaseTTLIs l id'))` → exact: `err ≠ nil ∧ ¬(id ≠ 0 ∧ ttl ≤ MaxLeaseTTL ∧
  id ∉ L)` with `Pre` and `L` unchanged, or `err = nil ∧ id ≠ 0 ∧ ttl ≤ MaxLeaseTTL ∧ id ∉ L` with
  `Post`, `L ++ [id]`, `leaseTTLIs l id` and `leaseLiveFrom γ.leases 0 id l`.
  `applierV3backend.LeaseGrant.wp_proof` (proved) adapted; its spec unchanged. Its docstring (M2)
  now says the clause consumes `RW` (the accounting in a granting cluster is B2, open).
- Not changed: `rqOk`, `reqPropOk(W)`, `plainCover`, `dispatchAnswer` (its `LeaseGrant` arm stays
  `True`), `dispatch.spec`, `raftRequest.spec`, `processInternalRaftRequestOnce.spec`, `appliedOk`,
  `hlease` (kept with the snapshot job's `lg = false`, D2). Removed (S6): `grantKindOk`, `rqOkG`,
  `plainCoverG`, `reqPropOkWG`, `grantAnswerIs`, `grantReplyOk`, `dispatch.specGrant` and
  `raftRequest.specGrant` with their `sorry`s `wp_grant`.

### D4. `EtcdServer.LeaseGrant` (statement, `sorry`)

- `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__LeaseGrant.lean`, vocabulary
  `LeaseGrant.lean` (`srvGrantsLeases E ρ := ρ.rd.kv.lg ∧ E.authOn = false`, two scope
  restrictions, S1; `leaseGrantReqOwn r ttl id` with `ID` owned, `leaseGrantedResp E resp`: id `≠ 0`,
  `TTL`, `Error`, the header's revision `rv ≠ 0` with `srvRevLb E.γ rv` and `txn.respHdrOwn`, and
  `leaseGrantedAt E.γ.leases i id`, M3). Its proof waits on B1 (over `raftRequest.spec`, which
  excludes grants). Why true of
  Go (`v3_server.go:434-456`): the loop writes `Next() & (2^63-1)` while `r.ID == 0`;
  `requireAuthInfo` is `nil` with auth off; `raftRequest` returns the apply's `*LeaseGrantResponse`.
  **`EtcdServer.LeaseGrant.wp_proof` (new `sorry`).**
- `v3rpc.lessorGrantOkL` (`api/v3rpc/InvLeaseGrant.lean`), the sibling of `raftLessor`'s grant
  conjunct, and **`v3rpc.lessorGrantOkL_of_server` (new `sorry`)**.
- `leaseGrantedResp` (internal): restated by the review's M3 (the receiver's need, `srvRevLb` and
  `respHdrOwn`, in place of `certOk`/`appliedWit`/`appliedHdr` at a log; `ρ` dropped).
- The wire model (2026-11-02; until then `raftLessor` was unsatisfiable by the Go server, which
  writes `r.ID` when it is `0`):
  - trusted: `pbLeaseGrantRequest` (`client/v3/InvLease.lean`): `recv r m := TTL ↦□ m.1 ∗ ID ↦□
    m.2` → `recv r m := TTL ↦□ m.1`, `recvOwn r m := ID ↦ m.2` (as `UserAdd`'s password).
  - frozen: `_Lease_LeaseGrant_Handler.spec`: `GrpcSpec`, `grpcHandlerOk` → `GrpcSpecMd`,
    `grpcHandlerOwnOkMd` (as `Compact`'s); `quotaLeaseServer.LeaseGrant.spec`: `grpcHandlerOk` →
    `grpcHandlerOwnOk`, pre `+ Req.recvOwn r m`; `LeaseServer.LeaseGrant.spec`: pre `+
    leaseGrantReqIdOwn r m.2`. Proofs adapted (proved).
  - internal: `v3rpc.leaseGrantReqIs r m`: `TTL ↦□ ∗ ID ↦□` → `TTL ↦□`; new `leaseGrantReqIdOwn r
    id := ID ↦ id`; `lessorGrantOk`'s and `lessorGrantOkL`'s pre `+ leaseGrantReqIdOwn r m.2`;
    `quotaLease_grantHandlerOk_of`, `etcd_leaseGrantHandlerOk`, `etcd_leaseGrantMethodOk`
    (`grpcHandlerOk` → `grpcHandlerOwnOk`; proved).

### D5. The client's and the served side (statements, `sorry`)

- `etcdLeaseGrantSpecL γl`, `etcdLeaseLeasesSpecL γl` (`client/v3/InvLeaseGrant.lean`), siblings of
  the frozen `etcdLeaseGrantSpec`/`etcdLeaseLeasesSpec` (unchanged): the grant's reply carries
  `∃ i, leaseGrantedAt γl i m.id`; `Leases` takes the caller's grants `G` (each with its fact) and
  lists all of them. Why true: `EtcdServer.LeaseLeases.spec` already has the per-call bound `m`
  (`lessorLb γl m` → `leaseIdsAt γl i ids`, `m ≤ i`), the grants give `lessorLb` (`leaseGrantedAt_lb`,
  the largest index), `leaseGrantedAt_listed` does the rest.
- `common.kv_lease_grant_served` (`examples/common/ServedLeaseGrant.lean`): `kv_lease_served`'s
  premises and `srvGrantsLeases E ρ`, giving also `etcdLeaseGrantAt addr E`. **New `sorry`.**
- The example: `leasegrant.Main.spec` (leasekv's premises and `lease.leasesNoExpiry`; `leasePeersOk`
  kept: the served Lease service's `TimeToLive` handler takes it), **`leasegrant.Main.wp_proof` (new
  `sorry`)**, `MainLinked`, `Results` (`leasegrant_Main`, `leasegrant_safe`), `Adequacy`
  (`leasegrant_adequate`, with `Hlne : lease.leasesNoExpiry`). The Prove stage needs an allocation
  with `KVNames.lg = true` (`common.alloc1` makes `false`).

### Open questions of the draft (answered 2026-11-02)

1. *`Recover` requires `lessorRevocable`; snapshots in a granting cluster are `runSnapLgOk`.* Left
   as is: an **interim restriction** (a granting cluster's snapshot path is not proved; a single
   member is never sent one). The Prove stage, or a later one, lifts it.
2. *Auth off is required for the guard.* Fine: the example is auth off. Stated in `srvGrantGuard`'s
   and `srvGrantsLeases`' docstrings.
3. *The header facts.* Checked against `v3rpc.leaseHdrAns` (`hf ↦□ h ∗ hdrW h ∗ r ≠ 0 ∗ Revision h
   ↦□ r ∗ etcdReached r`): `hdrW` comes from `appliedHdr`'s `respHdrOwn`; `etcdReached r` from
   `etcdReached_of_certOk` (`certOk E.γ log` and `sint.Z r < log.length`). So `leaseGrantedResp`
   needs `certOk` and the signed bound; both added (D4).

### Trusted and frozen statements changed

`lease.NewLessor.spec` (axiom: `mono`, `lessorModeIs`, the expiry payload through
`lessorExpiredC`); `lease.lessor.Recover.spec` (axiom: `lessorRevocable`);
`lease.lessor.ExpiredLeasesC.spec`, `lease.lessor.Revoke.spec`, `lease.lessor.Grant.spec` (proved
specs); `lessorOk`'s `ExpiredLeasesC` clause and `srvGrantGuard`; `NewServer.specM`/`specG`'s
`srvLessorNil`, and (the review) the row `%Hslg : ρ.rd.kv.lg = true → runSnapLgOk` in
`NewServer.spec`/`specM`/`specG`'s precondition, since the review (S1, S4) `%Hslg : ρ.rd.kv.lg =
true → lease.leasesNoExpiry ∧ runSnapLgOk` with `runSnapLgOk` a sealed name (`@[no_expose]`, its
triple `runSnapLgOkBody`; carried by `isServerBuilt(On)`, `isServerRun(On)`, `memberBoot(On)`); `applyAll.specSnap` (`lg = false`),
`applySnapshot.specSnap` (`lessorRevocable`);
`apply.revokeClause`, `revokeRes`, `revokeResAfter`; (D3) `isApplyLessor`'s Grant clause; (the wire
model) `pbLeaseGrantRequest` (trusted), `_Lease_LeaseGrant_Handler.spec`,
`quotaLeaseServer.LeaseGrant.spec`, `LeaseServer.LeaseGrant.spec` (frozen). The client contracts are
not changed (siblings). The review (2026-11-02): `lessorOk`'s `ExpiredLeasesC` clause again (a bag of
`False`, M1; derived); the opaque `ckptEffectsOk`'s and `leasesNoExpiry`'s docstrings (their
meaning, S2, S3; statements unchanged); `isApplyLessor`'s docstring (M2). **Pending**: the `axiom`
skill's review of `ckptEffectsOk` as restated for a granting cluster (S2) and of `leasesNoExpiry`.

### Checks

`lake build` passes; `etc/gen-init.py --check` and `etc/gen-interface.py --check` (backend, raft)
pass; `etc/bounds-check.py --check` reports the example's three new matches (`spec-receipt` 2,
`spec-thread` 1 in `examples/leasegrant`: `Main.spec`'s bounds, as `leasekv`'s), not recorded;
`etc/tcb-report.py --check` reports two new `sorry`s in the trust base, `runSnapLgOk_open` and
`leasegrant.Main.wp_proof`, both reached by `leasegrant_Main`/`leasegrant_safe` only (`--roots`);
every `etc/tcb-collections/*.txt` passes `--reuse --collection <c> --check` unchanged (until the
review the open case was an inline `sorry` of `run_job_snap`, `run_job_snap_lg`, in the trust base
of every result resting on `run`);
the other three (`EtcdServer.LeaseGrant.wp_proof`, `v3rpc.lessorGrantOkL_of_server`,
`common.kv_lease_grant_served`) are reached by no root yet (not linked). Baseline not updated.

## Review (2026-11-02)

The independent review (`notes/spec-review/lease-grant-draft.md`, of `44f1b5bc7c`), each finding and
what changed.

- **B1 (second specs; the user's decision: in place, gated). Partly done.** Removed (S6): the
  siblings `rqOkG`, `plainCoverG`, `reqPropOkWG`, `grantKindOk`, `grantAnswerIs`, `grantReplyOk`,
  the second specs `dispatch.specGrant`, `raftRequest.specGrant` and their `sorry`s. **Not done:**
  `rqOk`, `reqPropOk(W)`, `dispatchAnswer` redefined in place with the grant admitted at
  `KVNames.lg = true`, and `dispatch.spec`/`processInternalRaftRequestOnce.spec`/`raftRequest.spec`
  carrying `leaseGrantedAt`. Why: the adaptation is not mechanical in three places, each a decision:
  1. *Gating.* A grant admitted by `rqOk` reaches every proof generic in `E`/`γk` (the apply chain
     `applyEntryNormal` → `applyEntries` → `apply` → `run`, its `specOff`/`specOn` variants, the
     request path's `reqPropOk` uses); a `sorry` there enters every collection. Each open grant case
     must be a premise gated on `lg` carried from `NewServer` (as `%Hslg`), through every carrier of
     the apply chain, or a disjunct of `reqPropOk` at `γk.lg` whose open case is only reached under
     it. The carrier list is long (the `%Hslg` path plus `applyEntryNormal`'s and `dispatch`'s
     callers); the plan should fix it before the edit.
  2. *`dispatchAnswer`'s grant arm.* It needs the lessor's name (`γl`) in `dispatchAnswer`,
     `dispatchResult`, `applyResultIs` (about 45 statement sites, the whole server rebuilt), and its
     proof `applierTriples`' `LeaseGrant` triple exact through the five layers (auth, quota, …).
  3. *The rest model (B2).* Below.
  Proposed design: `rqOk log rq`'s `LeaseGrant` arm `E.lg = true ∧ id ≠ 0 ∧ no admin permission`
  with `AEnv.lg` tied to `KVNames.lg` (`srvEnvOk`); `reqPropOk`'s grant disjunct at `γk.lg` (no KV
  update); `dispatchAnswer`'s arm the grant's `leaseGrantedAt E.γ.leases i id` and its header; every
  open case an `lg`-gated row of `NewServer` (`%Hslg`'s pattern), so `lg = false` results keep their
  trust base.
- **B2, the user's decision (2026-11-02): tie the lessor to the table.** A revision of S1: the
  narrow stage plus the leases plan's L3b invariant brought forward, the lessor's live set equal to
  the KV model's lease table (`L = lt.ids`, `leasesLive`), so a grant's success is a function of the
  applied log and the rest model steps exactly by `restGrant`; leased puts and the results at
  `kvModelSt γk Lq` stay later. (`notes/decisions.md`, "The lease-grant stage's choices".) The
  analysis before the decision:
- **B2 (where the apply thread's grant facts come from). Partly done.** `leasesNoExpiry` now comes
  from `NewServer` (the gated row `%Hslg`, carried to `run`; S1). Not done: the rest model's step on
  a grant entry (`restGrant`, as `restRevoke`), `E.RW`'s accounting against `isApplyLessor`'s Grant
  clause, the quota applier's `ErrNoSpace` after a grant. Why: `lease.lessor.Grant.spec` consumes the
  backend's write token with `RW` and gives neither back (the trusted `lessorBackend` per-write
  contract), while the server's `E.RW` is `srvRestRW`, never lent; and the server's rest image is
  exact (`srvRest E γr A := E.RO (restModel …)`), so a grant's lease-bucket write must step it,
  which needs either the KV model's lease table tied to the lessor's live set (L3b, left out by the
  S1 (a) choice) or the lease bucket out of the exact rest model in a granting cluster. A scope
  decision for the user. The `ErrNoSpace` case: the quota layer sets no `ErrNoSpace` today (its
  `Available` premise, `apply.backendUnderQuota`), so `granted ↔ err = nil` holds as long as that
  premise does; to be restated with B2.
- **S1.** Done: `srvGrantsLeases E ρ := ρ.rd.kv.lg = true ∧ E.authOn = false`; `NewServer`'s row
  `%Hslg : ρ.rd.kv.lg = true → lease.leasesNoExpiry ∧ runSnapLgOk` (the one gated row, with S4's
  name), carried to the apply thread (`isServerRun`'s `%Hslg`); `Main.spec` keeps `leasesNoExpiry`
  and discharges the row. The docstrings of `kv_lease_grant_served`, `EtcdServer.LeaseGrant.spec` say
  they are conditional on it through `NewServer`.
- **S2.** Done: `ckptEffectsOk`'s docstring (`InvBoot.lean`) for a granting cluster (exercised only
  with a lease and the `LeaseCheckpoint` feature on; the examples leave it off, vacuous for
  `leasegrant`); statement unchanged. **Pending: the `axiom` skill's review.**
- **S3.** Done: `leasesNoExpiry`'s docstring (`LessorBackend.lean`): "the cluster grants", the
  theorem's executions after `Main` returns (read as "nothing is ever sent on `expiredC`"), why true
  of the example (TTL 600, `lessor.go:301-303, 480-553`); `Main.spec`'s header likewise.
- **S4.** Done: `runSnapLgOk` is `@[no_expose]` over `runSnapLgOkBody` (`InvRun.lean`), opened only
  by `run` (`runSnapLgOk_elim`); its docstring says it covers multi-member clusters (a lagging
  follower may be sent a snapshot), so it is not vacuous there. Interim, as filed in D2.
- **S5.** Done: `client/v3/InvLeaseGrant.lean`'s header and both contracts, `ServedLeaseGrant.lean`'s
  header and `etcdLeaseGrantAt`: per member because `LeaseLeases` is a member-local read
  (`v3_server.go:737-749`); several endpoints would need the contracts at every member. `γl` not
  hidden behind the address (optional; left).
- **S6.** Done for the server-side siblings (B1). The client contracts: **the user's decision
  (2026-11-02): replace, derive the old.** Done: `etcdLeaseGrantSpec γl`/`etcdLeaseLeasesSpec γl`
  (`client/v3/InvLeaseGrant.lean`) are the former `…L` contracts; the old statements are renamed
  `etcdLeaseGrantSpecAny`/`etcdLeaseLeasesSpecAny` (frozen: text unchanged, a name change) with
  `etcdLeaseGrantSpec_any`, `etcdLeaseLeasesSpec_any`, `isGrpcRpc_leaseGrant_any`,
  `isGrpcRpc_leaseLeases_any` (a registration at the new is one at the old). Callers (leasekv,
  `LeaseClient`, the client's `Results`, `LeaseReadServed`) renamed only.
- **M1.** Done: `lessorOk`'s `ExpiredLeasesC` payload is `False` (`InvApplier.lean`); derived by
  `isChanBag_iff` (`LessorOk.lean`, a local law of Perennial's `isChanBag`,
  `notes/perennial-changes.md`); `run`'s two receives use it directly.
- **M2.** Done: `isApplyLessor`'s docstring (`Contracts.lean`).
- **M3.** Done: `leaseGrantedResp E resp` gives `srvRevLb E.γ rv` (from which v3rpc derives
  `etcdReached rv`) and `txn.respHdrOwn`, not `certOk`/`appliedWit`/`appliedHdr` at a log; `ρ`
  dropped.
- **M4.** Done: `EtcdServer.LeaseGrant.spec`'s docstring states the margin (`r.ID` not given back;
  Go's interceptors do not read it).
- **M5.** Left for Freeze (the coordinator's instruction): the three `bounds-check` matches of
  `examples/leasegrant`.
- **M6.** Done: `lessorLb_max`, `leaseGrantedAt_lb_max` (`InvLessor.lean`).

## Design of the server chain (2026-11-02, final)

The plan of record from here on; it replaces the plumbing-commit list (kept, shortened, under
"Superseded" below). Written as text before any more site is threaded (`notes/spec-first-plan.md`,
"Design before plumbing"): Review checks the whole chain against it, the user freezes it, then the
commits of part 3 plumb it. It follows the user's decisions: S1 narrow plus the tie (the lessor's
live set is the model's lease table, so a grant's success is a function of the applied log and the
rest model steps by a grant's record); S2 `leasesNoExpiry` a named premise (`NewServer`'s gated
row); B1 in place, gated on `lg` (one spec per function); S6 done; (c) a granting cluster makes no
claim about etcd's KV service; revocations out (`rqOk _ _ .leaseRevoke = False`); one member,
snapshots of a granting cluster behind `srvGrantOpen` (a true, unproved statement; no false
statement behind a hypothesis).

**Round 3 → final** (review `notes/spec-review/lease-grant-design-r3.md`, of `7d62260a7c`; no
blocker, freeze after S-1):

- **S-1**: `mergedObs` takes an `lg` argument, like `cmp`, and its callers pass `E.lg`. The window
  lemma then needs no `γr.kv.lg = E.lg` fact, which `srvKVInvsOn` lacks at `on = true`.
  `merged_image` (at `on = false`) converts to `imageAt`'s `γk.lg` by `srvKVInvs`' tie.
- **m-a**: `kvLeases_pre` is now stated under `γr.raft.pre = []`, and `pre` is the raft node's prefix
  (`RNNames.pre`), not the boot log.
- **m-b**: the two laws of the leased window are named in 2.0, `bkRestAtL_of_rb` and
  `restLeasesWith_mem`.
- **m-c**: the freeze list's `sorry` line now says which `sorry`s are new and which are in the
  baseline.
- **m-d**: the freeze list now names every spec whose text is unchanged but whose meaning moves at
  `lg = true`.

**Round 2 → round 3** (review `notes/spec-review/lease-grant-design-r2.md`, of `a2320120fc`; no
blockers):

- **S-A / Q7** (the receive proofs unfold the gated `srvRest` with no `lg = false` fact):
  `srvGrantable E` moves into `srvRest`'s `lg = true` arm (the reviewer's placement). `applySnapshot`
  has `lessorRevocable E.γ.leases` in its pre; against `srvGrantable`'s `lessorModeIs … true`,
  `lessorPinR_agree` refutes the leased arm on entry, so `applySnapshot.spec`'s text does not change.
  `applyEntryNormal` reads `grantPermRq` off the `srvRest` it opens. No frozen pre gains a conjunct,
  and `srvSnapRO`/`isServerM` are untouched. Q7 is resolved.
- **S-B**: `mergedObs` is gated like `imageAt`, and `mergedCreate_window` (proved) is restated at the
  leased buckets; all three are in §3's table. Corrected: only `merged_image` is a `sorry`, not
  `mergedCreate_window`.
- **S-C**: `newHeader`'s post gains `∗ mvcc.certOk E.γ log`.
- **Q8**: resolved. `kvWriter` holds exactly `soleBudget log` tokens, so no caller lends fewer.
- **m1**: commit 2 changes only `Grant.spec` and `Checkpoint.spec`. `persistTo` takes
  `leaseBackend`, and `Revoke` takes `lessorBeOn` directly. **m2**: `d` is named in
  `isApplyLessor_of_lessorInv`'s premise. **m3**: the boot prefix grants nothing. **m4**:
  `NewServer.specG` at `on = true` needs `lg = false`. **m5**: the auth-on arm uses the generic
  `srvRest` laws. **m6**: the duplicate mode conjunct is gone.
- A "Freeze list" for the user ends the section.

**Round 1 → round 2** (review `notes/spec-review/lease-grant-design.md`, of `5cc0eaa28a`):

- **B1** (a member's `minLeaseTTL` in the cluster-wide image): `AEnv.mt` is gone. The shared
  image (`srvRest` at `lg = true`, `bkRestAt`'s leased form) says only that each table id has *some*
  record `leaseEnc id t 0` (`restLeasesWith f ids`, `f` existential); the member's TTL appears only
  in the lessor's own statements (`Grant.spec`'s `∃ mt, minLeaseTTL ↦□ mt`), and the Grant clause
  returns `∃ t, RO (restGrantT id t rs)`. Every former `E.mt` use is listed in 2.0 with its new form.
  `isApplyLessor` takes no `mt` argument (70 sites saved).
- **S1** (header unprovable from `newHeader`): `newHeader.spec`'s post strengthened (2.11a): the
  header's fields owned, `Revision ↦ W64 (|log| − 1)`, `2 ≤ |log| ∧ |log| + 3 ≤ 2^63`, from
  `store.Rev` at the sole writer. The grant's answer uses `grantHdr` (`+ 3`), not `appliedHdr`
  (`+ 4`, which no grant callee gives).
- **S2** (`leaseGrantedAt` needs the mode): `srvGrantable` now carries `lessorModeIs E.γ.leases true`,
  and so does `grantPermRq`, so the backend triple converts `leaseLiveFrom` to `leaseGrantedAt`.
  (Round 2 put it in `srvSnapRO`; round 3 moved it into `srvRest`.)
- **S3**: `srvRest_applyG`'s premise is `plainCover rq ∨ grantPropOk E.lg rq` (`plainEntryM`'s).
- **S4**: `bkRestAt` keeps its text; `imageAt γk` gates it: `if γk.lg then bkRestAtL … else
  bkRestAt …` (2.14). `bkRestAt_boot` is untouched. (Round 3 gated `mergedObs` too, S-B.)
- **S5**: part 3 lists every statement that changes at `lg = false` too, with the law its callers use.
- **M1**: `lessorApplyOk`'s new text written out (2.12), both arms of `Grant.spec`.
- **M3**: one lemma each, taking `lg`: `srvClusterBoot_alloc`/`alloc1` and `kv_lease_served`; no
  `…G` copies, and `kv_lease_grant_served` becomes `kv_lease_served` at `lg = true`.
- **M4**: `dispatchIds`/`grantRest` take the outcome, as `restOut`.
- **M5**: checked (2.7): a serializable `Range` fires no client update (`rangeReadOkM`'s serializable
  arm has no `Q`); the linearizable one fires through `kv_fire_reads`, refutable.
- **Q3**: kept (a), the halves through `Apply`/`dispatch`, over the reviewer's variant (the live set
  in `RestM`); the reason is in Q3.

Notation: `lg` is `KVNames.lg = AEnv.lg` (tied in `srvKVInvs`); "gated" means `if lg then new else
old` (or `⌜lg = true⌝ → …`), so at `lg = false` the old text is a law (`_false`, by `rfl`/`simp`).
Status marks: **trusted** (the trust base names it), **frozen** (a `Spec/` statement reviewed in an
earlier stage), **draft** (this stage's), **internal** (a definition or lemma under the specs).
"Member-local": about this member's objects only; "cluster-wide": shared through the log, a
snapshot or a certificate, so equal at every member.

### 1. What admitting a grant breaks

Every invariant, definition and result on the path that rules a grant out today, and whether it is
still true once a grant is applied in an `lg = true` cluster.

| where | rules the grant out by | true after a grant (lg = true)? | disposition |
|---|---|---|---|
| `rqOk lg` (`apply/Chain.lean`) | arm `False` at `false` | yes (commit 2) | sites from `false` to `E.lg` |
| `rqShape`/`entryShape`/`logShape lg`, `entryOk`, `entryOkM` | `rqOk false` | no at `false` | `E.lg`/`γk.lg` at every server site |
| `plainLogM cmp lg`; `kvInv`'s `plainLogM γk.cmp false` | third disjunct off | no at `false` | `kvInv` at `γk.lg` |
| `reqPropOk(W)`, `reqPropOkM false`, `kv_prop_au` | no grant form | — | gated grant disjunct (2.7) |
| `kvInv`'s `ghostVar γk.st ½ (kvModelSt γk L)`, clients' `etcdKV` | — | the state steps (table): needs a client update or the whole variable | (C): the invariant owns it whole at `lg = true` (2.7, Q1) |
| `reqPropOkW`'s write forms (`□ Q (kvStateOf (kvModel γk L))`), `kv_prop_auW` by `kvModelSt_plain` | — | **false** with a lease in the table, if a client AU exists | (C): every client AU refutable, true vacuously |
| `kvDep`/`regOk` at `kvStOff`, `kv_fire_reads`, `readQs` | — | **false** likewise | same |
| `kv_revLbZ_le` (takes `etcdKV`) | — | yes (rev only) | keep (fraction-generic) |
| `EtcdServer.Put/DeleteRange/Txn/Range/Compact.spec` (frozen), client contracts (trusted) | — | true under (C) (their AU cannot exist) | keep (text unchanged) |
| `kvModel_snoc_state`, `kvModel_eqv`, `kvWork`, `cmpLogOk`, `kvRaftOf` | — | yes | keep |
| `kvTableOf_plainM`, `kvModelSt_plain`, `backendTable_plain`, `restOut_plain` | plain premise | yes, at `lg = false` | keep |
| `dispatchAnswer`'s grant arm `True` | no answer | yes, useless | keep; answer beside it (2.6, Q2) |
| `appliedOk(M)`/`resPostM`/`resultIsW` | no grant fact | yes, useless | gain `grantArM` (2.6) |
| `backendStep`'s grant arm (`applied ∨ rejected backend`) | not exact | yes | keep; the triple says which (2.11) |
| `ApplyKV`, `applyStep` | — | yes | keep |
| `kvOwn`/`leasesLive` (`∃ L`, live set hidden) | — | yes, but no tie | gated half `ltHalf E L` inside (2.10) |
| generic `respMethods` triple for `LeaseGrant` (`E.RW`, post `mPost`) | `E.RW` never lent | **false** use: the grant writes `lease`, held exactly by `E.RO` | own triple over `E.RO` (2.11) |
| `newHeader.spec` (post `h ≠ null` only) | — | true, too weak for the answer | post strengthened (2.11a) |
| `isApplyLessor`'s Grant clause (derived): consumes `RW` | — | true, unusable | over `RO` (2.12) |
| `lessorApplyOk` (trusted, `NewLessor`'s post): `wbTok ∗ RW` spent whole | — | true; but the lens needs `lessorBeOn` back | lent part returned (2.12, Q4) |
| `srvRest E γr A := E.RO (restModel …)` (no `lease` write, `restEntry_keep`) | — | **false** after a grant | gated, leased image with `∃ f` (2.9) |
| `imageAt`'s and `mergedObs`'s `bkRestAt` (cluster-wide), `bkRestAt_boot` ("lease empty"), `mergedCreate_window` | image = `restModel` | **false** after a grant | gated in `imageAt` and `mergedObs`; window at the leased buckets (2.14) |
| `srvGrantGuard`, `lessorOk`, expiry arms, `srvLessorNil` (D1) | done | yes | keep |
| `UberOn`'s guard, `srvLessorNil` (auth on) | guard `False` with auth on | yes | keep; auth on requires `lg = false` (2.13) |
| snapshot receive (`applyAll.specSnap`, `applySnapshot.spec`, `Recover`, walk's `hlease`) | premises (`applySnapshot`: `lessorRevocable`) | `hlease` false at `lg = true` | keep; `srvGrantOpen_snap` (D2), now true at any members' TTLs (B1); the leased `srvRest` arm refuted on entry (2.9) |
| boot: `restBootBk` (empty `lease`), `NewLessor`'s empty bucket | — | yes (fresh boot) | keep; restart not in scope |
| `ckptEffectsOk` (trusted, opaque) | docstring | vacuous (feature off) | keep |

Nothing else found by `grep` of `False` arms (`rqOk`, `plainCover`, `dispatchKind`), the "plain"
predicates, the exact images (`srvRest`, `restModel`, `bkRestAt`, `imageAt`, `kvModelSt`), the
`kvModelSt_plain` uses (six: `KVLemmas.lean:518,581,708`, `ReadOn.lean:390`, all inside `kvInv`
with a client AU open), `respMethods`/`reqFacts`, `E.RW`.

### 2. The chain, statement by statement (top-down)

**2.0 New vocabulary** (internal, pure unless said).
- apply: `grantIdsOk (L : List w64) (id ttl : w64) : Prop := id ≠ 0 ∧ sint.Z ttl ≤ maxLeaseTTL ∧
  id ∉ L` (`Grant.spec`'s condition); `grantGoes (c : Chain) rq : Bool` (no capped or corrupt layer);
  over the outcome `o` (M4), as `restOut`: `grantIds rq o (L) := match o, rq.leaseGrant with |
  .applied .., some g => L ++ [g.id] | _, _ => L`, and `grantRest (t : w64) rq o (r : RestM)` the same
  match with `restGrantT g.id t r`; `restGrantT id t r := r.putIn leaseName (leaseKey id) (leaseEnc
  id t 0)` (`restGrant mt id ttl = restGrantT id (grantTTL mt ttl)`, by `rfl`).
- apply: `AEnv.γlt : GName := default`; `ltHalf E L : IProp := if E.lg then ghostVar E.γlt ½ L else
  True` (the tie's half; `ltHalf_false`).
- server: `restLeasesWith (f : w64 → w64) (ids : List w64) r := ids.foldl (fun r id => restGrantT id
  (f id) r) r`; `appliedTable γr A := kvLeases γr.kv (γr.raft.pre ++ A)`. `pre` is the raft node's
  prefix (`RNNames.pre`, `InvRaftNode.lean:93`), not the boot log, which `restModel` takes
  separately (`γr.raft.raft.boot`). The table folds from `[]` over `pre ++ A`, and the KV model's
  own table folds over `A`. They agree where `pre = []`: `NewServer.lean:1932`, `runSnapLgOkBody`
  (`InvRun.lean:450`), `SnapRecvFacts.lean:335`. Law `kvLeases_pre : γr.raft.pre = [] →
  (kvLeases γr.kv γr.raft.pre).ids = []` (by `rfl`). Laws for the send window (m-b):
  `bkRestAtL_of_rb : rbData P D = (restLeasesWith f T (restModel …)).bk → bkRestAtL …`, as
  `bkRestAt_of_rb`; `restLeasesWith_mem : (restLeasesWith f T r).mem = r.mem` (`restGrantT` writes
  only `bk`; for `srvRestOwn`'s `%Hmi`). Other laws:
  `(dispatchTable c rq v3 lt).ids = grantIds rq o lt.ids` under the triple's `o ↔` fact;
  `restEntry` commutes with `restGrantT` (`restEntry_keep`, GMap extensionality);
  `restLeasesWith_snoc` (with `f' := Function.update f id t`, equal on `ids` when `id ∉ ids`).
- **Where `E.mt` was, and what it is now** (B1): §2.0's `restLeases mt` → `restLeasesWith f`
  (cluster-wide, `∃ f`); §2.9's `srvRest` → `∃ f` (it reaches `runSnapLgOkBody`, cluster-wide); §2.10's
  `grantRest E.mt` → `∃ t, grantRest t` (member-local, but nothing needs `t`); §2.12's `isApplyLessor …
  mt` → no argument, the clause's `∃ t`; §2.13's "choose `E.mt`" → gone; §2.14's `bkRestAt c0 mt` →
  `bkRestAtL` with `∃ f` (cluster-wide). The member's `minLeaseTTL` stays in `lessorCfg` and
  `Grant.spec` only.

**2.1 `leasegrant.Main.spec`, `leasegrant_safe`** (draft): unchanged. Glue: `alloc1 true` (2.3),
`kv_lease_served` at `lg = true` (2.2), the client's `Grant`/`Leases` at
`etcdLeaseGrantSpec`/`etcdLeaseLeasesSpec`. Docstring (Q1's caveat): the KV service makes no claim
in this cluster; its results hold vacuously.

**2.2 `common.kv_lease_served`** (internal lemma; one lemma, M3). Post `grpcServeTok ∗ etcdKVAt …
∗ client.etcdLeaseReadAt addr` → `grpcServeTok ∗ client.etcdLeaseReadAt addr ∗ (if ρ.rd.kv.lg then
etcdLeaseGrantAt addr E else etcdKVAt addr E ρ γr cid mid)` (law `kv_lease_served_false`: the old
post). The draft `kv_lease_grant_served` goes. Callees: as today, plus
`v3rpc.lessorGrantOkL_of_server` and the Lease service's `LeaseGrant`/`LeaseLeases` handlers at
`lg = true`. Keeping `etcdKVAt` at `lg = true` would be sound (vacuous under (C)) but is what the
user's (c) excludes.

**2.3 `srvClusterBoot_alloc`, `common.alloc1`** (internal; one lemma each, taking `lg`): the KV
state's ghost variable whole to the KV invariant at `lg = true`, the clients' half returned at
`false`: post `… ∗ (if lg then True else etcdKV γk σ0)`; `memberBoot`'s row from `Main.spec`'s
premise and `srvGrantOpen_open`. Callers at `false`: `alloc1_false`.

**2.4 `v3rpc.lessorGrantOkL_of_server`** (draft lemma; statement unchanged). Callees:
`EtcdServer.LeaseGrant.spec`, `etcdReached_of_certOk` (via `srvRevLb`). Glue: the success post
`leaseGrantedResp` gives `ID ↦□ id`, `leaseGrantedAt`, the header; the error post `applyErrIs err`.

**2.5 `EtcdServer.LeaseGrant.spec`** (draft; statement unchanged). Callees: the id generator's
`Next` (`srvGenAt`, credits `□ |==> idCred ρ.ids 1`), the tracer's specs, `requireAuthInfo.spec`
(auth off: `nil`), `raftRequest.spec`. Glue:
1. the loop writes `Next() & (2^63-1)` until non-zero (invariant `ID ↦ id`); persist `ID ↦□ id`:
   `leaseGrantIs r ⟨id, ttl⟩`, `irrNoHdrIs p rq` for `rq := {leaseGrant := some ⟨id, ttl⟩}`;
2. `reqPropOkM false … rq (fun _ _ => True)` by the grant disjunct (2.7): `grantPropOk ρ.kv.lg rq`
   from `srvGrantsLeases` and `grantKindOk`; `rqShape true rq`; `irrNoZeroEnd rq`;
3. success: `appliedOkM`'s `grantAnsM E rq' resp` (2.6): `resp = mkOk *LeaseGrantResponse r` (the
   type assertion), and at `err = nil` the fields `ID ↦□ g.id`, `TTL`, `Error`, `grantHdr x.log` (2.6)
   and `∃ i, leaseGrantedAt E.γ.leases i g.id`; `g.id = id` by `irrWireOf`; `srvRevLb E.γ rv` from
   `grantHdr`'s `idxCert`/`certOk` at its log (2.11a: the header's log is certified); `rv ≠ 0` from
   `2 ≤ |log|`: `leaseGrantedResp E r`;
4. error: `applyErrIs err`, `resp = nil`.

**2.6 `raftRequest.spec`, `processInternalRaftRequestOnce.spec`** (frozen; **text unchanged**;
definitions underneath move):
- `appliedOkM on E ρ rq' F resp L` gains `∗ grantAnsM E rq' resp` (`True` unless `dispatchKind rq' =
  .leaseGrant`); `resPostM`, `resultIsW`, `resultIsWOn` gain `∗ grantArM E ar rq out` (`∃ v, ar ↦□ v ∗
  grantAnswer E rq v.Resp' v.Err'` for a dispatched grant, else `True`): the
  `authnArM`/`authnAnsM` pattern (Q2).
- `grantAnswer E rq resp err` (apply; `γl := E.γ.leases`, `γ := E.γ`): for a grant `g`, `∃ r, ⌜resp = mkOk *LeaseGrantResponse r⌝
  ∗ ((⌜err = nil⌝ ∗ grantRespIs r g ∗ ∃ i, leaseGrantedAt γl i g.id) ∨ ⌜err ≠ nil⌝)`;
  `grantRespIs r g := ID ↦□ g.id ∗ TTL ↦□ _ ∗ Error ↦□ "" ∗ ∃ log, grantHdr log (Header r)`;
  `grantHdr log hf := respHdrOwn hf ∗ ∃ h rv, hf ↦□ h ∗ Revision h ↦□ rv ∗ idxCert γ.idx log ∗
  certOk γ log ∗ ⌜sint.Z rv = |log| − 1 ∧ 2 ≤ |log| ∧ |log| + 3 ≤ 2^63⌝`.
- Glue of both proofs: unchanged; `grantAnsM_of_ar` (as `authnAnsM_of_ar`) in `raftRequest`.

**2.7 The proposal and the KV invariant** (internal; (c) as (C), Q1).
- `reqPropOk γk rq Qr` gains `⌜grantPropOk γk.lg rq ∧ rqShape γk.lg rq ∧ irrNoZeroEnd rq ∧ Qr = fun _
  => True⌝` (no client update); `grantPropOk_false` refutes it at `false`. `reqPropOkM false` is
  `reqPropOk`; `On`/`D` unchanged (auth on is `lg = false`).
- `kvInv γ γk`: `ghostVar γk.st ½ (kvModelSt γk L)` → `ghostVar γk.st (if γk.lg then 1 else ½)
  (kvModelSt γk L)`; `plainLogM γk.cmp false L` → `plainLogM γk.cmp γk.lg L` (`kvInv_false`).
  Docstring: in a granting cluster the KV results are vacuous (Q1's caveat).
- `kv_prop_au` (statement unchanged): `kv_prop_au_grant` updates the whole variable to
  `kvModelSt γk (L ++ [e])` (`kvModel_snoc_state`), entry facts by `plainEntryM`'s third disjunct,
  `kvWork_snoc`, `cmpLogOk`; `Qr` trivial. At `γk.lg = true` the write forms (`kv_prop_auW`) open the
  client's AU, get `etcdKV γk σ` (½) against the whole variable: `False`. Likewise `kv_fire_reads`
  (the linearizable read deposits). **M5:** a serializable `Range` fires no update: `rangeReadOkM`'s
  serializable arm has no `Q` and no `kvInv` access (`ReadOn.lean:163-171`), so nothing to refute;
  `Txn`'s read-only path is `kvDep` through the same read loop. `kv_revLbZ_le` is fraction-generic.

**2.8 The shapes** (internal): `kvWork`'s, `isServerRun`'s `logShape`, `srvLogShapes`,
`reqPropOk(W)`'s `rqShape` at `γk.lg`/`E.lg` (`rqShape_mono : rqShape false rq → rqShape lg rq`);
`entryOk lg x m` (`rqOk lg`), `entryOkM on lg`. `EtcdServer.applyAll.spec` (frozen): `logShape false`
→ `logShape E.lg`; `applyEntries`/`apply`/`applyEntryNormal.spec` (frozen): `logShapeM`, `entryOkM`
at `E.lg`.

**2.9 The apply thread's rest and tie** (internal; `srvRest` the carrier).
- `srvRest E γr A := E.RO (restModel …)` → `if E.lg then (∃ f, E.RO (restLeasesWith f (appliedTable
  γr A).ids (restModel …))) ∗ ltHalf E (appliedTable γr A).ids ∗ srvGrantable E else E.RO
  (restModel …)`. Cluster-wide where it is used (`runSnapLgOkBody`, the send branch): only ids, the
  TTLs under `∃ f` (B1).
- Laws: `srvRest_false`; `srvRest_snoc`/`_nodata`; `srvRest_applyG` (one lemma, generic in `lg`;
  replaces `srvRest_apply`): premise `plainCover rq ∨ grantPropOk E.lg rq` (S3, what `plainEntryM`
  gives; `grantKindOk` excludes `noSideEffect` and admin), from `Apply`'s post (2.10) `∃ t, E.RO
  (grantRest t rq o (restOut rq v3 o rs)) ∗ ltHalf E (grantIds rq o T)` at `rs := restLeasesWith f …`,
  `T := (appliedTable γr A).ids`, gives `srvRest E γr (A ++ [m])` with `f' := update f g.id t`
  (`restLeasesWith_snoc`; `g.id ∉ T` by the triple's `o ↔ grantIdsOk`).
- `srvGrantable E := □ ((∀ id, lease.leaseGranted E.γ.leases id) ∗ lease.lessorModeIs E.γ.leases
  true)` (S2; persistent), inside `srvRest`'s leased arm only (S-A, Q7). `srvRest` is already in the
  pre and post of `applyEntryNormal`, `applyEntries`, `apply`, `applyAll` and `applySnapshot`, so no
  frozen text changes. It is kept by `srvRest_applyG` (a persistent frame), set up by `NewServer`, and
  carried by `srvGrantOpen`'s body from the pre's `srvRest`. It holds the only mode fact the leased
  arm needs, since `srvRest` has no tie in scope (m6). Why it is true: `NewServer` creates the lessor
  with guard `srvGrantGuard lg on = ⌜leasesNoExpiry ∧ lg ∧ on = false⌝`. At `lg = true` it has
  `leasesNoExpiry` (`%Hslg`) and `on = false`, and the lessor's mode is `lessorModeIs … γr.kv.lg`
  (`NewLessor`).
- **The receive side** (S-A): `applySnapshot.spec` (frozen, text unchanged) has
  `lessor.lessorRevocable E.γ.leases` in its pre. On entry, its proof refutes `srvRest`'s leased arm
  (`srvGrantable`'s `lessorModeIs … true` against the revocable mode, `lessorPinR_agree`), and then
  works at `lg = false` by `srvRest_false`: `snap_srvRest`, the walk, `SnapRecvFacts`'s lemma and
  `SnapApplyKV`'s lease-free `leasesLive` at `L := []` (with `ltHalf_false`). Each of these takes
  `E.lg = false` (from the refutation) and is otherwise unchanged.
- `applyEntryNormal.wp_proof`: opens `srvRest`, calls `Apply` with `rs`, `T` and `grantPermRq E rq`
  (from `srvRest`'s `srvGrantable` at a grant, and `grantPermRq_of_not_grant` otherwise), recloses
  by `srvRest_applyG`, and hands `grantArM` to the waiter. Its auth-on arm (`ApplyNormalOn.lean`) has
  no `lg = false` fact: it uses the generic `srvRest_applyG`/`srvRest_snoc`, not `_false` (m5).
  `apply`, `applyEntries`, `applyAll`, `run`: unchanged proofs, except the send branch (2.14).

**2.10 `apply.uberApplier.Apply.spec`, `dispatch.spec`** (frozen; text changes):
- pre: `rqOk false` → `rqOk E.lg`; `+ grantPermRq E rq` (`□ (⌜dispatchKind rq = .leaseGrant⌝ → (∀ g,
  ⌜rq.leaseGrant = some g⌝ → leaseGranted E.γ.leases g.id) ∗ lessorModeIs E.γ.leases true)`, the
  `cmpPermRq` pattern; S2); `+ ltHalf E T` (new `∀ T`).
- post: `E.RO (restAfter rq v3 rs)` → `∃ t, E.RO (grantRest t rq o (restAfter rq v3 rs))` (Apply:
  `restOut`); `+ ltHalf E (grantIds rq o T)`; `+ grantRes E rq o ar` (2.6's `grantAnswer` through
  `ar`, `True` but for a dispatched grant).
- `kvOwn E log` (text unchanged) holds the other half: `leasesLive E s := ∃ L, txn.leasesKnown L s ∗
  lease.lessorUser E.γ.leases L (leaseItemsOf s) ∗ ltHalf E L`. Only a holder of both halves changes
  `L`; every non-grant path recloses `kvOwn` with its `L` and frames `ltHalf E T`.
- Glue of `dispatch`'s grant arm: `rqOk E.lg` (⇒ `E.lg ∧ grantKindOk rq`), the grant triple (2.11),
  `grantPermRq`. A grant is dispatched only with `v3` (`uber_applier.go:126-148`); without it `o` is
  not `.applied`, so `grantIds`/`grantRest` are the identity (M4). `Apply`'s auth check passes a grant.

**2.11 The chain's grant triple** (internal: `applierTriples`; `LeaseGrant` leaves `respMethods`,
`reqFacts`'s clause goes):
```
□ ∀ (r : Loc) rq (g : LeaseGrantModel) log (T : List w64) (rs : RestM) Pre Q Post info,
  {{ ⌜rq.leaseGrant = some g ∧ dispatchKind rq = .leaseGrant⌝ ∗ leaseGrantIs r g ∗
     lease.leaseGranted E.γ.leases g.id ∗ lease.lessorModeIs E.γ.leases true ∗ ltHalf E T ∗
     E.RO rs ∗ mvcc.storeWT E.γ ∗ mPre E c (.ok ai) info log Pre Q Post ∗ ciSplit E Pre }}
    ai.LeaseGrant(r)
  {{ (resp : Loc) (err) (o), RET (resp, err); mPost E c (.ok ai) log Pre Post ∗ applyErrIs err ∗
     ⌜chainOutcome c rq o⌝ ∗ ⌜(o is .applied) ↔ err = nil⌝ ∗
     ⌜err = nil ↔ grantGoes c rq ∧ grantIdsOk T g.id g.ttl⌝ ∗
     ltHalf E (grantIds rq o T) ∗ ∃ t, E.RO (grantRest t rq o rs) ∗
     grantAnswer E rq (mkOk *LeaseGrantResponse resp) err }}
```
(`chainOutcome`: the chain's step, `backendStep`'s two grant arms at `grantGoes`, `rejected` at the
capped/corrupt layer.) Per layer:
- backend (`applierV3backend.LeaseGrant.spec`, frozen, restated to this triple). Callees: the Grant
  clause (2.12), `newHeader.spec` (2.11a), `Lease.TTL` (`leaseTTLIs`). Glue: open `kvOwn` → `L`,
  `ltHalf E L`; agree with `ltHalf E T`, `L = T`; clause with `RO rs`; on success update both halves
  to `T ++ [g.id]`, reclose `kvOwn` (`leasesKnown_mono`); `leaseLiveFrom` + `lessorModeIs … true` →
  `leaseGrantedAt` (`leaseGrantedAt_of_live`); the header by `newHeader` (2.11a).
- quota (`quotaApplierV3.LeaseGrant.spec`, restated): inner triple, `Available` true by
  `apply.backendUnderQuota` (`isQuota`'s premise; `quotaReqTy` lists the grant): `err` unchanged.
- auth (embedded): the inner triple. capped / corrupt (restated): `nil, ErrNoSpace`/`ErrCorrupt`,
  `o` rejected; halves, RO, `L` unchanged.

**2.11a `apply.applierV3backend.newHeader.spec`** (frozen; post strengthened, S1). Old post
`storeReader ∗ kvWriter E.s E.γ log ∗ ⌜h ≠ null⌝` → `… ∗ ⌜h ≠ null⌝ ∗ hdrFields h ∗ Revision h ↦
W64 (|log| − 1) ∗ mvcc.certOk E.γ log ∗ ⌜2 ≤ |log| ∧ |log| + 3 ≤ 2^63⌝` (`hdrFields`: `ClusterId`, `MemberId`, `RaftTerm`,
`LeaderId` owned: `respHdrOwn`'s body). Callees (already its proof's): `mvcc.store.Rev.spec` (through
`kvOver_rev_wp`), the cluster's and raft status's getters. Glue: the proof calls `Rev` with the sole
writer's tokens `m := soleBudget log = 2^63 − 3 − |log|`; `Rev`'s post gives `log <+: log'` and
`|log'| + m + 3 ≤ 2^63`, so `|log'| ≤ |log|`, `log' = log`, `v = |log| − 1`; `kvWriter_len` gives
`2 ≤ |log|`; the struct allocation gives the fields. `certOk E.γ log` comes from `Rev`'s post (now
kept, not dropped with `-`; exact because `log' = log`; not derivable from `kvWriter`, S-C), and
`idxCert` from `kvWriter_cert`. `kvWriter` holds exactly `soleBudget log` tokens
(`SoleWriter.lean:89-91`), so the argument holds for every caller (Q8, resolved). Callers (51 sites / 36 files): a stronger post; their
intro patterns drop the new conjuncts.

**2.12 The lessor contract** (trusted `lessorApplyOk`; derived `isApplyLessor`):
- `isApplyLessor le s γ P f RO RW` (signature unchanged): its Grant clause pre `… ∗ leaseGranted
  γ.leases id ∗ RW` → `… ∗ leaseGranted γ.leases id ∗ RO rs` (`∀ rs`); post error arm `+ RO rs`,
  success arm `+ ∃ t, RO (restGrantT id t rs)`, conditions as `grantIdsOk L id ttl`.
  `isApplyLessor_of_lessorInv`: its backend premise names `d` (m2): `∀ d, ⌜γ.kb = some d⌝ →
  lessorBackend lp P f (storeWT γ) (lessorBeOn lp d.be) (storeRT γ) Rb`. `NewServer` and
  `SnapApplyOptsLemmas.lean:178-202` instantiate `lessorApplyOk`'s `RW := lessorBeOn lp d.be`
  (`rwLens` is reflexive), where today they pass the server's write right. Proof: over `Grant.spec`
  with `Rb := storeRb γ` from the RO lens
  (`revokeClause_of_lessorInv`'s); the put `Rb (rbSet rb leaseName … (leaseEnc id (grantTTL mt ttl)
  0))` back into `RO (restGrantT id (grantTTL mt ttl) rs)` (`grant_bk`), `t := grantTTL mt ttl`.
- `lessorBackend lp P f T R Rb` → `lessorBackend lp P f T Ln R Rb` (new `Ln`, the lent part): lens
  `□ (T -∗ ∃ dq, b ↦{dq} … ∗ (… -∗ T))` → `□ (Ln -∗ ∃ dq, lF "b" lp ↦{dq} b ∗ (lF "b" lp ↦{dq} b -∗ Ln))`.
- `lessorApplyOk lp` (trusted; `NewLessor`'s post): `lessorBackend lp Pk #f (wbTok d.γB ∗ RW)
  (bkRTx …) (rbPart d.γB (· = lease))` → `lessorBackend lp Pk #f (wbTok d.γB) RW (bkRTx …)
  (rbPart d.γB (· = lease))`: the counted token spent, the lent part `RW` (with `rwLens RW
  (lessorBeOn lp d.be)`) given back. True of Go: `persistTo(le.b)` reads the field before
  `BatchTx()`, and `LockInsideApply`/`Unlock` do not write it (`lease.go:55-61`).
- `lease.lessor.Grant.spec` (frozen): pre `T ∗ R ∗ Rb rb` → `T ∗ Ln ∗ R ∗ Rb rb`; post both arms
  `R ∗ Ln ∗ …` (error arm: `Rb rb`, as now; success arm: `Rb (rbSet …)`, as now; `T` spent in both).
  `Checkpoint.spec` likewise. These two are all (m1): `Lease.persistTo.spec` takes `leaseBackend b`
  with `b` passed in, and `lessor.Revoke.spec` takes `lessorBeOn` directly and already returns it.

**2.13 `NewServer.spec`/`specM`/`specG`** (frozen; text: one row each). `%Hslg` unchanged. `specM
true` and `specG on cmp` at `on = true` (m4) take `ρ.rd.kv.lg = false`. Proof: allocate `E.γlt` at
`[]`, one half into the boot's `leasesLive` with `leaseOwn γl [] ∅` and one into `srvRest E γr []` at
`f := fun _ => 0` (by `kvLeases_pre`, m3), and `srvGrantable E` (2.9) into the same `srvRest`.

**2.14 The snapshot side**. Receive: unchanged, `srvGrantOpen_snap` (its body's `applyRes` now holds
the gated `srvRest`, with `∃ f`: true whatever the members' minimum TTLs, B1). Send (`applyAll`'s
`msgSnapC` branch, `SnapSendBranch.lean`): the image is cluster-wide (`imageAt`, the snapshot
certificates, `snapDirInv`). `imageAt γk bootLog i L A D`: conjunct `bkRestAt γk.c0 bootLog L D` →
`(if γk.lg then bkRestAtL γk bootLog L D else bkRestAt γk.c0 bootLog L D)` (S4), with `bkRestAtL γk
bootLog L D := ∃ f, ∀ n ∈ restBuckets, D.lookup n = (restLeasesWith f (kvLeases γk L).ids (restModel
γk.c0 bootLog L)).bk.lookup n`. `bkRestAt`, `bkRestAt_boot`, `SnapRecvFacts`, `KVModelRestore` keep
their text and proofs (the receive side at `lg = false`, 2.9). The send branch's own observation is
gated the same way (S-B):
- `mergedObs` (`SnapSendBranch.lean:516-524`) takes a new argument `lg` (S-1), as it takes `cmp`:
  `mergedObs γr cmp lg ai A log D`. Its conjunct `bkRestAt γr.kv.c0 γr.raft.raft.boot (pre ++ A) D` →
  `if lg then bkRestAtL γr.kv bootLog (pre ++ A) D else bkRestAt …` (law `mergedObs_false`, by
  `rfl`). Its three users pass `E.lg` beside `E.cmp`: `EtcdServer__applyAll.lean:381`,
  `ApplyAllSnap.lean:458`, and the window's statement. A gate on `γr.kv.lg` would not do: the window
  is used at `on = true` (`EtcdServer__applyAll.lean:767`), where `srvKVInvsOn` has no `γr.kv.lg =
  E.lg`. (Rejected alternative: add that tie to `srvKVInvsOn`, which is one more definition and the
  on-mode boot's constructor.)
- `mergedCreate_window` (proved, generic in `on`): restated with the window at the gated buckets
  `(restLeasesWith f T (restModel …)).bk`, where `f` and `T` come from `srvRest`'s leased arm, and
  `T := []` at `E.lg = false`. Both arms, gated on the same `E.lg`, share one proof: unfold
  `srvRest`, pass those buckets to `srvBeSnapOk_window`, conclude by `bkRestAtL_of_rb`/`bkRestAt_of_rb`
  (with `restLeasesWith_mem`), and reclose.
- `merged_image` (`on = false`, `isServer`) keeps the S2 `sorry` (the file's only one, `:755`). It
  converts `mergedObs … E.lg` to `imageAt`'s `γk.lg` by `srvKVInvs`' `γr.kv.lg = E.lg`, and its
  `sorry` now also covers the leased image. It is still true: the observed ids are
  `kvLeases γk (pre ++ A)`, which is `imageAt`'s `L`.

**2.15 The trust base after the design**. Trusted, restated: `lessorApplyOk` (`NewLessor`'s post,
2.12: the lent part returned), for the `axiom` skill's pass of the `NewLessor` axiom (with
`ckptEffectsOk`, `leasesNoExpiry`, pending). Derived, restated: `isApplyLessor`. `srvGrantOpen`
keeps one field (`snap`). New `sorry`s: none beyond `srvGrantOpen_open` and the drafts
(`EtcdServer.LeaseGrant.wp_proof`, `lessorGrantOkL_of_server`, `leasegrant.Main.wp_proof`).

### 3. The size, the statements that change at `lg = false`, and the commits

**Sites** (`grep -c` over `Proof/ Spec/`, sites / files): `rqOk false` 17/10, `rqShape false`
21/10, `logShape false` 13/9, `entryShape false` 5/3, `entryOk` 15/10, `logShapeM` 15/3, `plainLogM
γk.cmp false` 5/4; `leasesLive` 29/13; `respMethods` 17/10, `reqFacts` 15/10, the four
`LeaseGrant.spec`s 16/13, `applierTriples` 49/31; `newHeader.spec` 51/36; `dispatch.spec` 4/4,
`Apply.spec` 12/6; `restAfter` 21/11, `restOut` 16/8; `srvRest` proofs unfolding it 18/8 (among
them the receive side's `snap_srvRest`, the walk, `SnapRecvFacts`, `SnapApplyKV`); `imageAt` 15;
`mergedObs` 10/3, `mergedCreate_window` 13/4; `kvInv` openers ≈10; `reqPropOk` 31/10; `appliedOkM`
32/16, `resPostM` 12/6, `resultIsW` 33/12; `NewServer.specG` 3/2; `lessorBackend` 11/9,
`lessorApplyOk` 18/9, `lease.lessor.Grant.spec` 16/10, `lease.lessor.Checkpoint.spec` 13/10 (commit 2:
≈60 sites in ≈30 files, m1); allocs 32/9. Not touched: `kvOwn` (288/73), `ApplyKV` (549/92),
`dispatchAnswer`/`dispatchResult`/`applyResultIs` (184), `isApplyLessor`'s signature (70/31),
`bkRestAt` (29/4), `srvKVInvs` (167), `srvSnapRO`, `isServerM`, `applySnapshot.spec`'s text
(36/21 uses). Roughly 470 edited sites, most mechanical.

**Statements that change at `lg = false` too** (S5; each new part is reached only through a grant,
which `rqOk false` excludes), with the law their `lg = false` callers use:

| statement | change at every `lg` | law for `lg = false` callers |
|---|---|---|
| `lessorApplyOk`, `lessorBackend`, `Grant.spec`, `Checkpoint.spec` | `Ln` returned | none: proofs re-done once (`persistTo`, `Revoke` unchanged, m1) |
| `isApplyLessor`'s Grant clause | `RO` for `RW` | none (no `lg = false` caller calls `Grant`) |
| the four `LeaseGrant.spec`s, `applierTriples`' grant entry | new triple | none (unreachable at `rqOk false`) |
| `newHeader.spec` | stronger post | none (more conjuncts; intro patterns) |
| `dispatch.spec`, `Apply.spec` | `+ grantPermRq`, `+ ltHalf`, `grantRest`, `grantRes` | `grantPermRq_of_not_grant`, `ltHalf_false`, `grantRest_not_applied` (`= r`), `grantRes_not_grant` |
| `appliedOkM`, `resPostM`, `resultIsW(On)` | `+ grantArM`/`grantAnsM` | `grantArM_not_grant` (constructors), dropped by users |
| `leasesLive` (now over `E`) | `+ ltHalf E L` | `ltHalf_false` (`True`) |
| `kvInv`'s ≈10 openers | fraction `if γk.lg then 1 else ½` | `kvInv_false`; `kv_prop_auW` splits on `γk.lg`; `kv_revLbZ_le` fraction-generic |
| `srvRest`'s users with no `lg` fact: `applySnapshot.wp_proof`, `snap_srvRest`, the walk, `SnapRecvFacts`'s lemma, `SnapApplyKV` | the leased arm carries `srvGrantable` | refute it on entry (`lessorRevocable` vs `lessorModeIs … true`, `lessorPinR_agree`), then `srvRest_false`, `ltHalf_false` |
| `applyEntryNormal`'s auth-on arm (`ApplyNormalOn.lean`) | gated `srvRest` | the generic `srvRest_applyG`/`srvRest_snoc` (no `lg` fact there, m5) |
| `mergedObs` (new argument `lg`; 3 users pass `E.lg`) | gated `bkRestAt` | `mergedObs_false` (`rfl`) |
| `mergedCreate_window` (proved) | window at `(restLeasesWith f T (restModel …)).bk` | one proof for both arms; at `false`, `T = []` and `restLeasesWith f [] r = r` |
| `merged_image` (`sorry`) | premise `mergedObs` gated | none: still the S2 `sorry`, now covering the leased image too |
| `NewServer.specM true`, `specG` at `on = true` | `+ ρ.rd.kv.lg = false` | callers (`memberBootOn`) allocate at `lg = false` |
| `kv_lease_served`, `srvClusterBoot_alloc`, `alloc1` | take `lg` | `_false` (old post) |
| `rqOk`/shapes/`plainLogM`/`kvInv`'s plain log, `srvRest`, `imageAt`, `reqPropOk` | gated | `_false` by `rfl`/`simp` |

**Commits**, each a full build with the checks of the last section (`tcb-report --check` new only
`srvGrantOpen_open` and the drafts; every collection unchanged; `gen-init`, `gen-interface`):
1. **Pure** (new modules): 2.0's definitions and laws.
2. **Lease package** (rebuilds lease and above; ≈60 sites): `lessorBackend`'s `Ln`, `lessorApplyOk`,
   `Grant.spec` and `Checkpoint.spec` returning it, `isApplyLessor_of_lessorInv`'s premise with `d`
   named (m2) and its instantiations.
3. **Apply package and the apply thread** (one full server rebuild): `AEnv.γlt`, `ltHalf`,
   `leasesLive E`, `newHeader.spec`, `isApplyLessor`'s RO clause and derivation, the grant triple and
   the five layers, `dispatch.spec`/`Apply.spec`, `grantAnswer`/`grantRes`; server side in the same
   commit: `srvRest` gated with `srvGrantable` in its leased arm, `srvRest_applyG`, the receive
   side's refutation, `entryOk`/`logShape` at `E.lg`, `applyEntryNormal` (both arms), `NewServer`'s
   allocations, `imageAt`'s and `mergedObs`'s gates, `mergedCreate_window` and the send branch.
4. **The request path** (full server rebuild): `kvInv` (C), `reqPropOk`'s grant disjunct,
   `kv_prop_au_grant` and the refutations, `plainLogM γk.cmp γk.lg`, `kvWork`'s shapes,
   `grantArM`/`grantAnsM`, `NewServer.specM true`'s and `specG`'s (`on = true`) `lg = false`,
   `srvClusterBoot_alloc lg`.
5. **Leaves** (cheap): `EtcdServer.LeaseGrant.wp_proof`, `lessorGrantOkL_of_server`,
   `kv_lease_served lg`, `alloc1 lg`, `leasegrant.Main.wp_proof`.
Commits 3 and 4 may be merged to save one full rebuild; kept apart for review.

### 4. Open questions (for the user)

- **Q1. The KV state of a granting cluster.** (A) L4's client update for a grant; then
  `Put`/`DeleteRange`/`Txn`/`Range.spec` need `ρ.kv.lg = false` (frozen texts change). (B) Drop the
  table from the clients' state (L3a's state half undone; L6 puts it back). (C) The KV invariant owns
  the state's ghost variable whole at `lg = true`; any client AU is refutable; every KV result true,
  vacuously, text unchanged; L4's update not used. **Recommended: (C)** (reviewer agrees), with the
  vacuity said in the docstrings of `kvInv`, `%Hslg` and `leasegrant_safe`.
- **Q2. Where the grant's answer travels.** (i) In `dispatchAnswer`, with `γl` (≈184 sites). (ii)
  Beside it, `grantRes`/`grantArM`/`grantAnsM` (`authnArM` precedent, ≈15). **Recommended: (ii).**
- **Q3. The tie's carrier.** (a) Two halves of a ghost variable gated on `lg`: one in `kvOwn`'s
  `leasesLive`, one beside the image in `srvRest` and through `Apply`/`dispatch` (`∀ T`, `ltHalf E T`
  in and `ltHalf E (grantIds …)` out). (a') The reviewer's variant: the live set in `RestM` (`lids`),
  its half inside the server's `E.RO`; `Apply`/`dispatch` gain no `T`. (b) The live set explicit in
  `ApplyKV`/`kvOwn` (≈300 statement sites). **Chosen: (a).** (a') moves the half inside the abstract
  `E.RO`, so the backend triple, which must update both halves, needs a lens through `RO` to the half:
  either a new law on `AEnv`'s `RO` given at `NewServer`, or the half as a new argument of
  `isApplyLessor` (70 sites / 31 files, the cost B1 just removed), and the server's `RO` a wrapper of
  `srvRestOwn` (29 sites). (a) costs a gated conjunct on two frozen specs (16 sites), `True` at
  `lg = false`; the triples carry the half in the open. (b) when leased puts need the live set in
  every triple (L3b/L6).
- **Q4. Getting `lessorBeOn` back from `Grant`.** (a) The `Ln` argument of `lessorBackend` (2.12;
  true of Go). (b) Lend `E.RW` per grant (breaks the exact image). **Recommended: (a)**, with the
  `axiom` skill's pass of `NewLessor`.
- **Q5. The snapshot send path.** (a) `imageAt` gated, `bkRestAtL` with `∃ f` (2.14). (b) A second
  sealed field (re-meets commit 1's circularity). **Recommended: (a).**
- **Q6. Auth on with `lg = true`.** Required `lg = false` (recommended), or a stage of its own.
- **Q7 (resolved, round 3). Where `srvGrantable` reaches `applyEntryNormal`.** Inside `srvRest`'s
  leased arm (2.9; the reviewer's placement). No frozen text changes, and it also gives the receive
  proofs their refutation of the leased arm.
- **Q8 (resolved, round 3). `newHeader`'s `log' = log`.** `kvWriter` holds exactly `soleBudget log`
  tokens by definition, so every caller of the spec lends `Rev` that budget (2.11a).

### Freeze list (for the user)

**Trusted statements changed** (one, for the `axiom` skill's pass of `lease.NewLessor`):
- `lessorApplyOk lp`: `lessorBackend lp Pk #f (wbTok d.γB ∗ RW) (bkRTx …) (rbPart d.γB (· = lease))`
  → `lessorBackend lp Pk #f (wbTok d.γB) RW (bkRTx …) (rbPart d.γB (· = lease))`: the counted token
  is spent and the lent part `RW` is given back (2.12).

**Frozen specs changed:**
- `lease.lessor.Grant.spec`, `lease.lessor.Checkpoint.spec`: `+ Ln` in the pre, and given back in
  every arm of the post.
- `apply.applierV3backend.newHeader.spec`: a stronger post (fields, `Revision`, `certOk`, bounds).
- `apply.uberApplier.dispatch.spec`, `apply.uberApplier.Apply.spec`: these changes:
  - `rqOk E.lg`;
  - `+ grantPermRq`;
  - `∀ T`, with `ltHalf E T` in and `ltHalf E (grantIds …)` out;
  - `∃ t, RO (grantRest t …)`;
  - `+ grantRes`.
- The four `LeaseGrant.spec`s of the applier chain: restated to the grant triple (2.11).
- `EtcdServer.applyAll.spec` (`logShape E.lg`); `applyEntries`/`apply`/`applyEntryNormal.spec`
  (`logShapeM`/`entryOkM` at `E.lg`).
- `NewServer.specM true` and `specG` at `on = true`: `+ ρ.rd.kv.lg = false`.
- **Text unchanged, meaning changed at `lg = true`** (m-d). Each means the same at `lg = false`.
  They are grouped by the definition that moves underneath them:
  - over `reqPropOk`/`appliedOkM`/`resPostM` (the grant disjunct, `grantArM`):
    - `raftRequest`, `processInternalRaftRequestOnce`;
    - the auth specs `EtcdServer.{UserAdd, UserDelete, UserGet, UserList, UserGrantRole,
      UserRevokeRole, RoleAdd, RoleDelete, RoleGet, RoleList, RoleGrantPermission,
      RoleRevokePermission, AuthEnable, AuthDisable, AuthStatus}`.
  - over `kvInv` (its gated fraction), directly or through `isServerReq`/`isServerM`:
    - `NewServer.spec`, `examples/compactkv/checkCompactRev.spec`;
    - the KV specs `Put`/`DeleteRange`/`Txn`/`Range`/`Compact`;
    - `MemberList`, `Start`/`start`, `HardStop`, `stop`, `Serve`, `serveClient`, `restartCheck`.
  - over `isApplyLessor` (the Grant clause over `RO`): `apply.newAuthApplierV3.spec`,
    `lease.NewLessor.spec`.
  - over `lessorApplyOk`: `lease.NewLessor.spec`, `EtcdServer.applySnapshot.spec`,
    `lease.lessor.Recover.spec` (docstring only).
  - over `srvRest` (gated, with `srvGrantable`): `applySnapshot`, and `applyAll`/`applyEntries`/
    `apply`/`applyEntryNormal`, beyond their listed changes.
  - over `kvOwn` (`leasesLive`'s `ltHalf`): every applier-chain triple (`applierSpec`, 56 files),
    gated, so `True` at `lg = false`.
- Drafts of this stage, statements unchanged: `EtcdServer.LeaseGrant.spec`, `leasegrant.Main.spec`.

**New named hypotheses:** none. Those already named are unchanged:
- `leasesNoExpiry` (S2, `%Hslg`);
- `srvGrantOpen`, one field, `srvGrantOpen_snap`. It is true of Go: a received snapshot's lease
  bucket holds records for exactly the committed table's ids, whatever TTLs the leader stored, which
  `∃ f` absorbs. `Recover` rebuilds the lessor from those ids, and with revocations, checkpoints
  and expiry out, the table and the lessor's history stay monotone.
- `apply.backendUnderQuota`, as today. It is true of Go only with the backend under its quota;
  without it, quota's `LeaseGrant` reports `ErrNoSpace` for a granted lease.

**`sorry`s after the plumbing** (m-c), against `etc/tcb-baseline.txt`:
- New (what `tcb-report --check` reports): `srvGrantOpen_open`, and the Prove stage's drafts
  `EtcdServer.LeaseGrant.wp_proof`, `v3rpc.lessorGrantOkL_of_server` and
  `leasegrant.Main.wp_proof`. `kv_lease_grant_served` goes, and `kv_lease_served lg` is proved.
- Already in the baseline: `merged_image` (S2). Its statement now also covers the leased image.

**Open questions, with recommendations:**
- Q1: (C), the KV invariant owns the KV state whole at `lg = true`, so the KV results are vacuous
  there (as docstrings say).
- Q2: (ii), the answer beside `dispatchAnswer`.
- Q3: (a), the halves through `Apply`/`dispatch`.
- Q4: (a), the `Ln` argument.
- Q5: (a), `imageAt`/`mergedObs` gated over `∃ f`.
- Q6: auth on requires `lg = false`.

Q7 and Q8 are resolved, and the reviewer agrees with Q1-Q6.

**Plumbing size:** about 470 edited sites in five commits, most of them mechanical. Commits 3 and 4
each need a full server rebuild; merging them saves one.

## Superseded: the plumbing-commit list (2026-11-02)

Replaced by the design above as the plan of record; kept shortened for its record of what is done.

- **Done** (each a full build; `tcb-report.py --check` new only `srvGrantOpen_open` and
  `leasegrant.Main.wp_proof`; every collection unchanged; `gen-init`, `gen-interface` unchanged):
  commit 1 `75676e772c` (`AEnv.lg`, tied in `srvKVInvs`; the bundle `srvGrantOpen`, one field
  `srvGrantOpen_snap`, not carried into `isServerApplyAll`: its body names `isServerApplyAll`,
  circular); commit 2 `7a83c345aa` (`rqOk lg`, grant arm `grantKindOk` at `true`, every site at
  `false`); commit 3a `e410475e10` (`plainEntryM`/`plainLogM` and `rqShape`/`entryShape`/`logShape`
  take `lg`, every site at `false`; `plainCover`/`plainReq` not changed: the admission is
  `plainEntryM`'s third disjunct `grantPropOk`).
- **The blocker** 3a's survey found, now resolved by the design's Q1: admitting a grant into the KV
  invariant made the KV results (`reqPropOkW`'s write forms, `kvDep`/`regOk`, `kv_fire_reads`, the
  server's `Put`/`DeleteRange`/`Txn`/`Range` and the client contracts) false after a granted lease,
  their state lease-free where the invariant's has the table (`kvModelSt_plain` holds only of a
  grant-free log). Options then: (a) results at the full state (the leases plan's L3d), (b)
  lease-blind KV clients, (c) no KV client updates in a granting cluster. The user chose (c); the
  design realizes it as Q1 (C).
- **The rest of the old list**, as planned then and changed by the design: commit 3b (the grant
  disjunct with the client update `kvOpAu γk (.leaseGrant id ttl) Q`, L4's decision: replaced by
  2.7's disjunct without update, Q1); an apply-side bundle `srvGrantOpenApply` for `dispatch`'s grant
  case (not needed: 2.9-2.12 prove it); `dispatchAnswer` with `γl` (replaced by `grantRes`/`grantArM`
  beside it, Q2); the tie as `⌜L = (kvLeases γk A).ids⌝` in the apply thread's invariant with `E.RW`
  lent per grant (replaced by `ltHalf` and the Grant clause over `E.RO`, Q3/Q4); the quota's
  `ErrNoSpace` after a grant as a disjunct of the answer (dead under `isQuota`'s existing
  `Available` premise, 2.11); then the Prove stage's leaves (the design's commit 5).

## Freeze (2026-11-02, the user's)

The design above, its Freeze list and Q1-Q6 as recommended, frozen after review rounds 1-3 and the
axiom reviews (`notes/axiom-review/lessor-apply-ok.md`: `lessorApplyOk` survives, current and
proposed; `lease-grant-lessor.md`: `NewLessor`'s mode/history/payload, `Recover`'s `lessorRevocable`,
`ckptEffectsOk`, the wire model survive; `leasesNoExpiry` refuted as worded, its docstring restated to
"no lease of any lessor the program creates", with two corrections: two `RequestTimeout`s, and
`Renew`/checkpoints among what moves an expiry later). The bounds' three `examples/leasegrant`
entries approved with it. Next: the plumbing, in the design's commit order, then Prove.

**Amendment: (A), the user's, 2026-11-03; axiom review pending.** §2.0's "`restEntry` commutes with
`restGrantT`" was false as stated for a conf change (the "Plumbing" section's problem). The trusted
`membership.membersOfBk` becomes a definition over an opaque `membership.membersOf` of the `members`
and `members_removed` buckets only, and the axiom `membership.membersOfBk_empty` is restated over
`membersOf` (old → new text in "Plumbing", "(A)"). No other frozen statement changes.

**Amendment: (B), the user's, 2026-11-03.** §2.10 said "A grant is dispatched only with `v3`
…; without it `o` is not `.applied`, so `grantIds`/`grantRest` are the identity". False:
`dispatchStep` (`apply/InvUber.lean:70`) is `o = .applied log false` when `v3 = false`, so
`grantIds rq o T` would append a grant that `dispatch` never ran, and `dispatch.spec`/`Apply.spec`'s
frozen posts were unprovable at `v3 = false` (found in 3b, "Plumbing").
- The fix (option 1): `grantIds`, `grantRest`, `grantIdsA`, `grantRestA` take `v3` and are the
  identity when `v3 = false` (as `dispatchTable`): `grantIds rq v3 o L`, `grantRest t rq v3 o r`,
  `grantIdsA rq v3 out L`, `grantRestA t rq v3 out r`, each gated on `dispatchKind rq =
  .leaseGrant ∧ v3 = true` (the kind check is kept: a request dispatched as another kind with a
  stray `LeaseGrant` field leaves the live set). The grant triple (2.11, below `dispatch`, always
  with `v3`) uses `grantIds rq true o T`, `grantRest t rq true o rs`.
- The two frozen posts, old → new:
  `dispatch.spec`: `ltHalf E (grantIds rq o T)` → `ltHalf E (grantIds rq v3 o T)`;
  `∃ t, E.RO (grantRest t rq o (restAfter rq v3 rs))` → `∃ t, E.RO (grantRest t rq v3 o (restAfter
  rq v3 rs))`.
  `Apply.spec`: `ltHalf E (grantIdsA rq out T)` → `ltHalf E (grantIdsA rq v3 out T)`;
  `∃ t, E.RO (grantRestA t rq out (restOut …))` → `∃ t, E.RO (grantRestA t rq v3 out (restOut …))`.
- Two deviations approved with it: the grant triple's pre (`grantPre`) has `⌜E.lg = true⌝`
  (without it both halves are `True` at `E.lg = false` and `grantIdsOk T` is unprovable;
  `dispatch` has it from `rqOk E.lg`'s grant arm); `revokeRes E rs` gains `⌜E.lg = false⌝` (a
  revocation changes `L`, and in a granting cluster the apply thread holds one half only; `rqOk
  E.lg` excludes revocations).

**Amendment: (C), the user's, 2026-11-03.** The gap: the grant's outcome fact (`(o applied) ↔
err = nil ↔ grantGoes c rq ∧ grantIdsOk T g.id g.ttl`) was only in the grant triple's post (2.11,
internal); 2.10's `dispatch.spec`/`Apply.spec` posts did not pass it on, and what they give
(`dispatchStep`, whose backend grant arm is `applied ∨ rejected .backend` whatever the table) does
not tie `o` to the model table, so `srvRest_applyG` (hence `applyEntryNormal` with a grant entry)
was unprovable (found in 3b, "Plumbing"). The fix (option 1): one pure conjunct in each post,
`grantOutOk c rq v3 T o := dispatchKind rq = .leaseGrant → v3 = true → ∀ g, rq.leaseGrant = some g
→ ((∃ l ns, o = .applied l ns) ↔ grantGoes c rq = true ∧ grantIdsOk T g.id g.ttl)` (pure, in
`apply/Chain.lean` beside `grantIds`; vacuous for other requests and at `v3 = false`).
- `dispatch.spec`'s post, old → new: `… ∗ (∃ t, E.RO (grantRest t rq v3 o (restAfter rq v3 rs))) ∗
  cPost v3 Pre Post ∗ …` → `… ∗ (∃ t, E.RO (grantRest …)) ∗ ⌜grantOutOk c rq v3 T o⌝ ∗ cPost v3 Pre
  Post ∗ …`.
- `Apply.spec`'s post, old → new: `… ∗ (∃ t, E.RO (grantRestA t rq v3 out (restOut …))) ∗ cmpOwn E
  x'.crev ∗ …` → `… ∗ (∃ t, E.RO (grantRestA …)) ∗ ⌜grantOutOkA x.chain rq v3 T out⌝ ∗ cmpOwn E
  x'.crev ∗ …`, with `grantOutOkA c rq v3 T out := match out with | .dispatched o _ => grantOutOk c
  rq v3 T o | _ => True` (`GrantRest.lean`, beside `grantIdsA`: `Apply`'s post has `out`, not `o`;
  mechanical, the `grantIdsA` pattern).
- Proved in `dispatch` from the grant triple's post (`Hst.2.1.trans Hst.2.2`), the other arms by
  `grantOutOk_nonGrant`/`_noV3`; the server's ids law is then a pure lemma.

**Amendment: (D), the user's, 2026-11-03** (review round 4, `notes/spec-review/lease-grant-design-r4.md`,
finding B1). The gap: §2.14 gated `imageAt`'s rest conjunct on `γk.lg`, but the network's image
certificate `srvImage γ i D := ∃ γk, ⌜γk.c0 = 0 ∧ γk.ch0 = … ∧ γk.log0 = …⌝ ∗ dbImage …` does not pin
the sender's `lg`, so `dbImage_kv_congr` (and with it `dbImage_of_srvImage`, `snapRecv_image`)
would need `γk.lg = γk'.lg`, which no receiver knows. The fix: `imageAt` is not gated; its rest
conjunct is the leased image at every `lg`.
- `imageAt`, old → new: `… ∧ bkRestAt γk.c0 bootLog L D ∧ …` → `… ∧ bkRestAtL γk bootLog L D ∧ …`
  (`bkRestAtL` reads `γk` only through `c0`/`ch0`, so `dbImage_kv_congr` keeps its premises).
- New law `bkRestAt_of_L : (kvLeases γk L).ids = [] → bkRestAtL γk bootLog L D → bkRestAt γk.c0
  bootLog L D`; the receiver gets the empty ids from its plain log (`kvTableOf_plainM`).
- `mergedObs` stays gated on `E.lg` (S-1); `merged_image` (the S2 `sorry`) converts both arms to
  the ungated image, still true.

## Plumbing (2026-11-02)

The design's §3 commits, as done, with their deviations and the problem found.

**(A), the user's, 2026-11-03** (the conf-change commutation below; a trusted change, one commit of
its own before commit 3; axiom review pending). In `InvRest.lean`:
- old: `opaque membership.membersOfBk : GMap GoString BktData → GMap w64 (List GoString) × GMap w64
  Bool` (opaque over the whole tracked-bucket map);
  new: `opaque membership.membersOf : Option BktData → Option BktData → GMap w64 (List GoString) ×
  GMap w64 Bool` and `def membership.membersOfBk bk := membership.membersOf (bk.lookup "members")
  (bk.lookup "members_removed")`. Every use of `membersOfBk` (`ccValidOn`,
  `MustReadMembersFromBackend.spec`, `applyConfChange`'s proof) keeps its text.
- old: `axiom membership.membersOfBk_empty (bk : GMap GoString BktData) (hm : (bk.lookup
  "members").getD ∅ = ∅) (hr : (bk.lookup "members_removed").getD ∅ = ∅) : membersOfBk bk = (∅, ∅)`;
  new (same name): `axiom membership.membersOfBk_empty (bm br : Option BktData) (hm : bm.getD ∅ = ∅)
  (hr : br.getD ∅ = ∅) : membership.membersOf bm br = (∅, ∅)`. Its one use (`ccValidOn_boot`)
  unfolds `membersOfBk` first.
- Derived (`RestLeased.lean`): `ccValidOn_restGrantT` (a lease record leaves the verdict), so
  `ccRest_restGrantT` and `restEntry_restGrantT` lose their premise.
- The trust base: no new axiom, no new opaque other than `membersOf` (the opaque moved inward);
  the collections list `axiom membership.membersOfBk_empty` by name, so their text does not change,
  but the statement under that name does (to review with the `axiom` skill: it is weaker in what it
  quantifies over and says the same of Go, `notes/axiom-review/members-empty.md` already found
  `readMembersFromBackend` reads only those two buckets and suggested this definition).

**Commit 1 (pure, new modules)** `d65faf5aa1`: `apply/GrantRest.lean` (`restGrantT`, `restGrant_eq`, `grantIdsOk`,
`grantGoes`, `grantIds`, `grantRest`, `restLeasesWith` with `_nil`/`_mem`/`_congr`/`_snoc`, and the
commutations `restGrantT_putIn`/`_delIn`, `restAfter_restGrantT`), `AppliedTable.lean`
(`appliedTable`, `kvLeases_pre`), `RestLeased.lean` (`bkRestAtL`, `bkRestAtL_of_rb`,
`ccRest_restGrantT`, `restEntry_restGrantT`). Mechanical adaptations:
- three modules, not one per side: `srvRest` (in `InvRest`) needs `appliedTable` and
  `restLeasesWith`, so these sit below `InvRest`; `bkRestAtL` needs `restModel`, so above it, and
  `InvImage` will import `RestLeased`.
- `Function.update` is not available (no Mathlib): `updFn f id t` in its place.
- `grantIds`/`grantRest` are over the chain's `Outcome` (`dispatch`'s); `Apply`'s outcome is an
  `ApplyOut`, so `grantIdsA`/`grantRestA` (a dispatched request's) for `Apply.spec`'s post.
- `ltHalf`/`AEnv.γlt` are not pure (a field of `AEnv` rebuilds the server): left to commit 3.
- The law `(dispatchTable c rq v3 lt).ids = grantIds rq o lt.ids` needs the triple's facts: left to
  commit 3, where they are.

**Commit 2 (lease package)** `a8470c1775`: `lessorBackend lp P f T Ln R Rb` (the lens over `Ln`), `lessorApplyOk`'s
new text (`(wbTok d.γB) RW`), `Grant.spec`/`Checkpoint.spec` with `Ln` in and back, their proofs.
Deviation (mechanical): `isApplyLessor_of_lessorInv`'s premise is `lessorBackend lp P f (storeWT γ)
RW₀ (storeRT γ) Rb`, not yet the design's `∀ d, ⌜γ.kb = some d⌝ → … (lessorBeOn lp d.be) …` (m2):
in commit 2 the Grant clause still takes the write right `RW`, which lends `RW₀` (`lessorBeOn lp
d.be` at both instantiations, `NewServer` and `SnapApplyOptsLemmas`, unchanged), and the returned
`Ln` is dropped. The `d`-named form belongs with the clause over `RO` (commit 3), whose lens gives
`d`.

**The problem: a conf change does not commute with a lease record (blocked commit 3; resolved by (A), the user's, 2026-11-03, above).**
- *What.* §2.0 says "`restEntry` commutes with `restGrantT` (`restEntry_keep`, GMap
  extensionality)". It does for a normal entry (`restAfter_restGrantT`, proved), but not for a conf
  change: `ccRest v3 cc r` branches on `membership.ccValidOn r.bk cc`, which is `ccValidM` of
  `membership.membersOfBk r.bk`, and `membersOfBk` is **opaque over the whole tracked-bucket map**
  (`InvRest.lean:79`). Nothing says it ignores the `lease` bucket, so `ccValidOn (restGrantT id t
  r).bk cc = ccValidOn r.bk cc` is not provable. `RestLeased.lean`'s `ccRest_restGrantT` and
  `restEntry_restGrantT` are proved under exactly that premise.
- *Where it is needed.* `applyConfChange.spec` (frozen) takes `E.RO rs` to `E.RO (ccRest v3 m rs)`.
  With `srvRest`'s leased arm, `rs = restLeasesWith f T (restModel … (pre ++ A))`, and reclosing
  `srvRest E γr (A ++ [m])` (`srvRest_snoc` in `EtcdServer.apply`'s conf-change arm) needs
  `ccRest v3 m (restLeasesWith f T r) = restLeasesWith f T (ccRest v3 m r)`. The server's policy
  (`ccApplyOk`: an `AddNode` of a configured member) does not help: the verdict is still
  `membersOfBk` of a different map. Every later commit (3-5) rests on the gated `srvRest`.
- *Options.*
  (A) Make `membersOfBk` a function of the two membership buckets:
  `membersOfBk bk := membersOfBkM (bk.lookup "members") (bk.lookup "members_removed")`, the opaque
  moved inward, and `membersOfBk_empty` restated over it. True of Go (`readMembersFromBackend` reads
  only those buckets, as the axiom's docstring already says); then `ccValidOn` ignores `lease` and
  the commutation is proved. A change to a trusted (opaque) definition and to an axiom's statement,
  so the `axiom` skill's pass and the user's approval; no new axiom.
  (B) Interleave the records: the leased image `restModelL f` folds each applied grant's record at
  its entry (`restEntryL`: `restEntry`, then the record if the entry is a grant that succeeds at the
  table before it), so a conf change is validated on the leased buckets and no commutation is needed.
  No trust change, but `srvRest`'s leased arm, `bkRestAtL` and `imageAt` (2.9, 2.14) are restated.
  (C) A trust-boundary axiom that `membersOfBk` ignores the `lease` bucket: excluded (no new axiom).
  Recommended: (A), the smallest change and true of Go; (B) if the trust base must not move.

**Commit 3, split** (2026-11-03): commit 3 is one full server rebuild by design; it is done in
buildable parts, each a full build with the checks, the design's statements unchanged.
- **3a (done)**: `AEnv.γlt : GName := default`, `ltHalf E L` with `ltHalf_false` (2.0, in
  `apply/Chain.lean`: they need `AEnv`, not pure); `hdrFields h` (2.11a's id fields, `Chain.lean`);
  `newHeader.spec`'s post strengthened as 2.11a (`⌜h ≠ null⌝ ∗ hdrFields h ∗ Revision h ↦ W64
  (|log| − 1) ∗ certOk E.γ log ∗ ⌜2 ≤ |log| ∧ |log| + 3 ≤ 2^63⌝`) and its proof. Mechanical
  adaptations: the proof calls `store.Rev.spec` itself (`storeReader_toC`/`_of` around it), not the
  readers' corollary `Rev.specR`, which drops `certOk` (changing `specR` would move the mvcc result
  `mvcc_store_Rev_frozen`); the callers' intro patterns: `⟨Hrd, Hsw, -⟩` unchanged (the last `-`
  drops the new conjuncts), `⟨Hrd, Hsw, %Hh⟩` → `⟨Hrd, Hsw, %Hh, -⟩` (`LeaseRevoke`,
  `LeaseCheckpoint`, `LeaseGrant`); `NewServer.lean`'s anonymous `AEnv` literal gains `default` for
  `γlt` (3b allocates it there).
- **Not separable**, so left for the next part (3b): `isApplyLessor`'s Grant clause over `RO`
  with `isApplyLessor_of_lessorInv`'s `d`-named premise (the backend `LeaseGrant` proof is the
  clause's only caller and has only `E.RW` until it gets the grant triple, 2.11); the
  `dispatchTable` ids law (needs the triple's `chainOutcome`/`o ↔` facts).
- **The rest of commit 3, 3b, one part** (not split further: the server's callers of
  `Apply.spec`/`dispatch.spec` must supply `ltHalf E T` at any `E.lg`, and only the gated `srvRest`
  holds that half, so the apply package's new specs and the server side build only together). The
  apply package: `leasesLive E` with `ltHalf E L` (29 sites / 13 files); `grantHdr`/`grantAnswer`/
  `grantRes`; the grant triple (2.11) in `applierTriples` (out of `respMethods`/`reqFacts`), its five
  layers; the RO Grant clause and its derivation (2.12, with the `d`-named premise);
  `dispatch.spec`/`Apply.spec` (2.10), the `dispatchTable` ids law. The server side: `srvRest` gated
  with `srvGrantable`, `srvRest_applyG`, the receive side's refutation, `entryOk`/`logShape` at
  `E.lg`, `applyEntryNormal` (both arms), `NewServer`'s allocations (`E.γlt` at `[]`),
  `imageAt`'s/`mergedObs`' gates, `mergedCreate_window` and the send branch.

**Checks after each of commits 1 and 2**: the full build; `tcb-report.py --check` reports as new only
the two `sorry`s already on the branch (`srvGrantOpen_open`, `leasegrant.Main.wp_proof`); all 46
collections unchanged; `gen-init.py --check` and `gen-interface.py --check` (backend, raft) clean.

**Commit 3b, partial** (2026-11-03, WIP on branch `lease-grant-3b`, not squashed: it does not
build as a whole, and it is blocked on the problem below).

*Done, building* (`apply.Link` builds; `SnapApplyOptsLemmas`, `NewServer` build):
- `apply/Chain.lean`: `ltHalf_agree` (at `E.lg`), `ltHalf_update`; `leasesLive E` with `ltHalf E L`
  (`kvOwn_lend` adapted); `grantHdr`, `grantRespIs`, `grantAnswer`, `grantPre`/`grantPost` (2.11's
  triple, named), the triple as `applierTriples`' 6th conjunct (after `LeaseRevoke`); `LeaseGrant`
  out of `respMethods`/`reqFacts`. The pure grant vocabulary moved for import order: `restGrantT`,
  `grantIdsOk`, `restLeasesWith`, `updFn` and their laws to `apply/RestLease.lean`; `grantGoes`,
  `grantIds`, `grantRest` to `Chain.lean`; `GrantRest.lean` keeps `grantIdsA`/`grantRestA` (its
  header docstring is stale).
- `apply/Contracts.lean`: `isApplyLessor`'s Grant clause over `RO rs` (2.12); `LessorDerive.lean`:
  `isApplyLessor_of_lessorInv` with the `d`-named premise (`Rb := rbPart d.γB (· = leaseName)`,
  `Ln := lessorBeOn lp d.be`) and an `RW` lens giving `d`; `RW₀`/`Rb` parameters gone;
  `Results.lean`'s `lessor_apply_contract` and both instantiations (`NewServer`,
  `SnapApplyOptsLemmas`) restated.
- The four grant layers (`applierV3backend`, `quotaApplierV3`, `applierV3Capped`,
  `applierV3Corrupt` `__LeaseGrant`): specs restated to `grantPre`/`grantPost`, proofs done; the
  compositions (`newApplierV3Backend`, `newQuotaApplierV3`, `newApplierV3Capped`,
  `newApplierV3Corrupt`, `newAuthApplierV3`) supply the clause; the `leasesLive` and
  `applierTriples` patterns in the other apply proofs adapted.
- `NewServer.lean`: allocates `E.γlt` at `[]` (`ghostVar_alloc`, split in halves), one half in the
  boot's `leasesLive`; the other (`HltS`) is unused until the gated `srvRest` takes it.

*Failing* (the server `Link` build): `SnapApplyKVLemmas.lean:123` (the receive side builds
`leasesLive` at `L = []`: needs `ltHalf E []`, i.e. `E.lg = false` from the gated `srvRest`'s
refutation, 2.9); `SnapApplyWalk.lean:379` (destructs the old `leasesLive`: one more component, and
the same `E.lg = false`). Modules downstream of those were not reached.

*Not started*: `dispatch.spec`/`Apply.spec` (2.10, blocked below), `grantRes`, the `dispatchTable`
ids law; the server side: `srvRest` gated with `srvGrantable`, `srvRest_applyG`, the receive
side's refutation, `entryOk`/`logShape` at `E.lg`, `applyEntryNormal`, `imageAt`/`mergedObs`
gates, `mergedCreate_window`, the send branch.

*Deviations* (internal; mechanical unless said):
- `grantIds`/`grantRest` are gated on `dispatchKind rq = .leaseGrant` (not only on
  `rq.leaseGrant = some g`): otherwise a put carrying a stray `leaseGrant` field would add a record;
  `backendTable` is gated the same way. `grantIds_applied`/`grantRest_applied` take the kind.
- `grantPre` has `⌜E.lg = true⌝`: at `E.lg = false` both halves are `True` and do not tie the
  lessor's `L` to `T`, so `grantIdsOk T` is unprovable. `dispatch` gets it from `rqOk E.lg`'s grant arm.
- `revokeRes` gains `⌜E.lg = false⌝`: a revocation changes `L`, and in a granting cluster the
  apply thread holds only one half. The design missed it; `rqOk` excludes revocations when
  `E.lg`, so the callers have it.
- `grantRespIs` has `∃ e, Error ↦□ e` and `∃ t, TTL ↦□ t`; `chainOutcome c rq o` is
  `chainStep backendStep c rq log o`.

*The problem: 2.10 at `v3 = false` (resolved: amendment (B), the user's, 2026-11-03, option (1); the
`v3` argument is in `Chain.lean`/`GrantRest.lean`).*
- *What.* 2.10 says "without [v3] `o` is not `.applied`, so `grantIds`/`grantRest` are the
  identity". False: `dispatchStep` (`apply/InvUber.lean:70`) is `if preV3Kind … ∨ v3 = false then
  o = .applied log false`, so a grant dispatched without `v3` has `o = .applied log false`, and
  `grantIds rq o T = T ++ [g.id]` though nothing was granted (`ar = null`). The frozen posts
  `ltHalf E (grantIds rq o T)` and `∃ t, E.RO (grantRest t rq o …)` are then unprovable (the
  lessor's `L` and the store did not change). The model `dispatchTable` already ignores a grant at
  `v3 = false`.
- *Options.* (1) give `grantIds`/`grantRest` (and `grantIdsA`/`grantRestA`) the `v3` argument,
  identity when `v3 = false`: the text of `dispatch.spec`/`Apply.spec` changes (`grantIds rq v3 o
  T`), matching `dispatchTable`. (2) keep the four definitions and gate the specs' posts on `v3`
  (`if v3 then … else ltHalf E T ∗ E.RO …`). (3) keep the text and gate `grantIds` on
  `o = .applied _ true`-like information: not available, `Outcome.applied` carries no `v3`.
  Recommended: (1). Either way `grantRes` is vacuous when `ar = null`.

**3b, after amendment (B)** (2026-11-03, WIP on `lease-grant-3b`):
- *Done, building* (`apply.Link` builds): (B) itself (`grantIds rq v3 o L`, `grantRest t rq v3 o r`,
  `grantIdsA`/`grantRestA` with `v3`, gated on `dispatchKind rq = .leaseGrant ∧ v3 = true`; laws
  `_noV3`; the triple at `v3 := true`); `grantPermRq` (+ `_persistent`, `_of_not_grant`, in
  `Chain.lean`); `grantRes E rq o ar` and `grantResA` (`InvUber.lean`); `chainStep_grant_logAfter`
  (`DispatchLemmas.lean`: a grant leaves the KV log, any chain); `dispatch.spec` and `Apply.spec`
  restated to 2.10 with (B) and their proofs (`dispatch`'s grant arm calls the triple). Mechanical:
  `grantRes` is gated on `dispatchKind rq = .leaseGrant ∧ ar ≠ null` (so `True` at `v3 = false`,
  where `ar = null`), its `o` unused (2.10's text names it); the new post conjuncts sit inside
  `∃ o` (they mention `o`), after `kvOwn`/`chainClass`; `Apply.spec`'s module imports `GrantRest`.
- *The problem (found 2026-11-03; stops the server side, the user's decision).* `srvRest`'s
  leased arm (2.9) is `… ltHalf E (appliedTable γr A).ids …` with the image at those ids, so
  `srvRest_applyG` must show `grantIds rq v3 o T = (appliedTable γr (A ++ [m])).ids`, i.e. the
  design's "`(dispatchTable c rq v3 lt).ids = grantIds rq o lt.ids` under the triple's `o ↔` fact".
  But that fact (`(o applied) ↔ err = nil ↔ grantGoes c rq ∧ grantIdsOk T g.id g.ttl`) is only in
  the grant triple's post (2.11, internal); 2.10's `dispatch.spec`/`Apply.spec` posts do not pass it
  on. What they give, `dispatchStep c rq v3 log o`, is `chainStep backendStep`, whose backend grant
  arm is `o = .applied log false ∨ o = .rejected .backend` (either, whatever the table), and the
  other new conjuncts (`ltHalf`, `grantRest`, `grantRes`) do not tie `o` to the model table. So
  `srvRest_applyG`, hence `applyEntryNormal` with a grant entry (which `entryOk E.lg` admits, 2.8),
  is unprovable from the frozen 2.10 text. Options:
  (1) add a pure conjunct to both posts, e.g. `⌜apply.grantOutOk c rq v3 T o⌝` with `grantOutOk c
  rq v3 T o := dispatchKind rq = .leaseGrant → v3 = true → ∀ g, rq.leaseGrant = some g → ((∃ l ns,
  o = .applied l ns) ↔ grantGoes c rq = true ∧ grantIdsOk T g.id g.ttl)` (`Apply`: over `out`,
  at `x.chain`); proved in `dispatch` from the triple's post (one line), and the ids law is then
  pure (`leaseGrantOk lt` is `grantIdsOk lt.ids`; `chainTable` at a grant is the backend's at
  `grantGoes`). Recommended: the smallest, and true of the code.
  (2) make the model relation exact for a grant: `backendStep`'s grant arm takes the lessor's
  condition, which needs the live set as an argument of `dispatchStep`/`chainStep` (a model
  change reaching every user of `dispatchStep`, ≈90 sites).
  (3) state the half after the call by the table: `ltHalf E (dispatchTable c rq v3 ⟨T⟩).ids`; but
  `grantRest` still depends on `o`, so the image needs the same fact: no gain over (1).
- *Not started* (unchanged from the list above): the server side (gated `srvRest` with
  `srvGrantable`, its laws, `srvRest_applyG`, the receive side's refutation, `entryOk`/`logShape`
  at `E.lg`, `applyEntryNormal`, `NewServer`'s `srvRest` half, `imageAt`/`mergedObs` gates,
  `mergedCreate_window`, the send branch); the two failing files above
  (`SnapApplyKVLemmas.lean:123`, `SnapApplyWalk.lean:379`) and `applyEntryNormal`'s calls of
  `Apply.spec` (new arguments `T`, the half, `grantPermRq`; the post's `∃ t` RO) are where the
  server build fails now.

**3b, done** (2026-11-03, squashed onto `lease-grant`; the full build, `tcb-report.py --check` (new
only the two `sorry`s already on the branch, `srvGrantOpen_open` and `leasegrant.Main.wp_proof`), the 46
collections, `gen-init.py --check`, `gen-interface.py --check` (backend, raft) clean). After (B),
(C) (`grantOutOk`/`grantOutOkA` in `dispatch.spec`/`Apply.spec`'s posts, proved in `dispatch`) and
(D) (`imageAt`'s rest conjunct `bkRestAtL` for every lg, `bkRestAt_of_L` back at empty ids):
- *The server side.* `InvRest.lean`: `srvGrantable`, `srvRest` gated (2.9), `srvRest_false`,
  `srvRest_revocable` (the receive side's refutation); helpers `srvRestAt` (`srvRest_eq_at`), `srvIds
  E T := if E.lg then T else []`, `srvGrantIf` (persistent), `srvRestAt_open` (⊣⊢: one form at both
  `E.lg`), `srvRest_open`/`srvRest_close`, `srvRest_snoc` (premise: the table unchanged),
  `srvRest_nodata`, `srvRest_applyG`, `srvGrantIf_perm`, `srvRest_init` (`NewServer`). `AppliedTable.lean`:
  the ids law, pure (`dispatchTable_ids`, `dispatchTableA_ids` from `grantOutOk`), and
  `appliedTable_snoc`/`_nodata`/`_cc`/`_nonLease`, `chainTable_*`. `ApplyCmpArm.lean`:
  `srvRest_applyP`/`srvRest_applyP0` (a plain request or compaction), `srvGrantIf_permP`.
  `RestLeased.lean`: the transfer lemmas across `restLeasesWith` (`restLeasesWith_lookup_other`,
  `membersOfBk_`/`ccValidOn_`/`ccRaftEff_`/`membersDecode_`/`ccRest_restLeasesWith`).
- *Callers.* `applyEntryNormal` (both arms) opens with `srvRest_open`, calls `Apply.spec` with
  `T := srvIds E …`, the half and `grantPermRq` (`srvGrantIf_permP`), recloses with
  `srvRest_applyP` (the auth-on KV arm's `kvSpecL` triple has no grant conjuncts: `srvRest_applyP0`);
  admin entries through `srvRest_admin` (restated over `srvRest_snoc`, S3). `EtcdServer.apply`'s
  conf-change arms (S2): `rs := restLeasesWith f (srvIds …) r` to `applyConfChange`, its premises by the
  transfer lemmas, reclosed by `ccRest_restLeasesWith` and `appliedTable_cc`. The receive side (S4):
  `applySnapshot` derives `E.lg = false` by `srvRest_revocable`; `kvOwn_snap`, `snap_applyKV`,
  `snap_srvRest`, `srvSnapApplied_of_walk`, `snapRecv_image` take `hlg : E.lg = false`; `ApplyAllSnap`
  derives it from its `lessorRevocable`. The send side: `mergedObs … lg` gated, `mergedCreate_window`
  through `srvRest_open`/`close`, `bkRestIf_of_rb`. `NewServer` (S1): `specM`/`specG` gain the pure
  premise `on = true → ρ.rd.kv.lg = false` (the Freeze row; `memberBootOn` gains the conjunct
  `ρ.rd.kv.lg = false`, which `MainAlloc` discharges and `startServer` passes); the boot's `srvRest`
  by `srvRest_init` with `HltS`, and `srvGrantable` at `lg = true` from `NewLessor`'s
  `lessorGuard`/`lessorModeIs` (`on = false` by the new premise). `M2StorageDraftB2`'s congruence
  through `kvLeases`.
- *Deviations* (mechanical): `apply.Apply.specRec` gains `T`, `rqOk E.lg`, `grantPermRq E rq ∗ ltHalf E
  T` and the post's `ltHalf`/`∃ t RO`/`grantOutOkA`/`grantResA`; `srvRest_applyG`'s premises (M3:
  `hch : x.chain = γr.kv.ch0`, `hg`, `hr : ∀ r, restOut = restAfter`); instances
  (`apply.Assumptions`, `lease.Assumptions`) as binders per theorem, not section variables.
- *Left (not done in 3b).* `entryOk`/`logShape` at `E.lg` (2.8): the KV invariant is still
  `plainLogM … false`, so no grant entry reaches `applyEntryNormal`; its callers pass `rqOk E.lg` by
  `apply.rqOk_of_false`. With 2.8, `applyEntryNormal`'s grant arm uses `srvRest_applyG` and
  `srvGrantIf_perm` (both proved). M1's lemmas are for commit 4.

**Where the plumbing stopped** (2026-11-03): 3b done (above); next: commits 4 and 5 (and 2.8).
