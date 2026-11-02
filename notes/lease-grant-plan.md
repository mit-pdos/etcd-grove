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

## Design of the server chain (2026-11-02)

The plan of record from here on; it replaces the plumbing-commit list (kept, shortened, under
"Superseded" below). Written as text before any more site is threaded (`notes/spec-first-plan.md`,
"Design before plumbing"): Review checks the whole chain against it, the user freezes it, then the
commits of part 3 plumb it. It follows the user's decisions: S1 narrow plus the tie (the lessor's
live set is the model's lease table, so a grant's success is a function of the applied log and the
rest model steps exactly by `restGrant`); S2 `leasesNoExpiry` a named premise (`NewServer`'s gated
row); B1 in place, gated on `lg` (one spec per function, `lg = false` meaning what it means on
`lean`); S6 done; (c) a granting cluster makes no claim about etcd's KV service; revocations out
(`rqOk _ _ .leaseRevoke = False`); one member, snapshots of a granting cluster behind
`srvGrantOpen` (a true, unproved statement; no false statement behind a hypothesis).

Notation: `lg` is `KVNames.lg = AEnv.lg` (tied in `srvKVInvs`); "gated" means a definition of the
form `if lg then new else old` (or a conjunct `⌜lg = false⌝ → …`), so that at `lg = false` the old
text is a law (`_false` lemma by `rfl`/`simp`), not a re-proof. Status marks: **trusted** (an axiom
or a contract the trust base names), **frozen** (a `Spec/` statement reviewed in an earlier stage),
**draft** (this stage's, not frozen), **internal** (a definition or lemma under the specs).

### 1. What admitting a grant breaks

Every invariant, definition and result on the path that rules a grant out today, and whether it is
still true once a grant is applied in an `lg = true` cluster. "Gate" = restated in place, gated;
"keep" = true as is.

| where | rules the grant out by | true after a grant (lg = true)? | disposition |
|---|---|---|---|
| `rqOk lg` (`apply/Chain.lean`) | arm `False` at `false` | yes (3a, commit 2) | sites move from `false` to `E.lg` |
| `rqShape`/`entryShape`/`logShape lg`, `entryOk`, `entryOkM` (`InvApplier`, `ApplyNormalOn`) | `rqOk false` | no at `false` | `E.lg`/`γk.lg` at every server site |
| `plainLogM cmp lg`, `kvInv`'s `plainLogM γk.cmp false` | third disjunct off | no at `false` | `kvInv` at `γk.lg` |
| `reqPropOk(W)`, `reqPropOkM false`, `kv_prop_au` | no grant form | — | gated grant disjunct (2.7) |
| `kvInv`'s `ghostVar γk.st ½ (kvModelSt γk L)` with clients' `etcdKV` | — | the state steps on a grant (table): needs a client update or the whole variable | (C): the invariant owns it whole at `lg = true` (2.7, Q1) |
| `reqPropOkW`'s write forms (`□ Q (kvStateOf (kvModel γk L))`), `kv_prop_auW` by `kvModelSt_plain` | — | **false** once a lease is in the table, if a client AU exists | (C) makes every client AU refutable at `lg = true`: true, vacuous |
| `kvDep`/`regOk` at `kvStOff`, `kv_fire_reads`, `readQs` | — | **false** likewise | same, (C) |
| `kv_revLbZ_le` (takes `etcdKV`) | — | yes (rev only), and vacuous under (C) | keep |
| `EtcdServer.Put/DeleteRange/Txn/Range/Compact.spec` (frozen), the client contracts (trusted) | — | true under (C) (their AU is refutable); never registered at `lg = true` | keep (text unchanged) |
| `kvModel_snoc_state`, `kvModel_eqv`, `kvWork`, `cmpLogOk`, `kvRaftOf` | — | yes (a grant changes no mvcc log; `kvTable` steps) | keep |
| `kvTableOf_plainM`, `kvModelSt_plain`, `backendTable_plain`, `restOut_plain` | premise plain at `lg = false` | yes, at `lg = false` only | keep; callers at `lg = false` |
| `dispatchAnswer`'s grant arm `True` | no answer | yes but useless | keep; the answer travels beside it (2.6, Q2) |
| `appliedOk(M)`/`resPostM`/`resultIsW` | no grant fact | yes but useless | gain `grantAns…` (2.6) |
| `backendStep`'s grant arm (`applied log ∨ rejected backend`) | not exact | yes (log unchanged either way) | keep; success is the tie's, not the outcome's |
| `ApplyKV`, `applyStep` | — | yes | keep (no `ids` field: Q3) |
| `kvOwn`/`leasesLive` (`∃ L`, live set hidden) | — | yes, but loses the live set: no tie | gated half `ltHalf E L` inside (2.10, Q3) |
| `applierTriples`' generic `respMethods` triple for `LeaseGrant` (`reqFacts`: `leaseGranted ∗ E.RW`; post `mPost`, no rest step) | `E.RW` never lent; no answer | **false** use: the grant writes the lease bucket, which `E.RO` holds exactly | own triple, over `E.RO` (2.11) |
| `isApplyLessor`'s Grant clause (trusted contract, derived): consumes `RW` | — | true, unusable (no RW to lend; RO not stepped) | restated over `RO` (2.12) |
| `lessorApplyOk`/`lessorBackend` (the `NewLessor` axiom's backend contract): per-write token `wbTok ∗ RW` spent | — | true; but `Grant` then loses `lessorBeOn`, which the RO lens must get back | lent part returned (2.12, Q4) |
| `srvRest E γr A := E.RO (restModel …)` (`restModel` never touches `lease`, `restEntry_keep`) | — | **false** after a granted lease (bucket has the record) | gated: leases image + tie half (2.9) |
| `srvGrantGuard`, `lessorOk`, expiry arms, `srvLessorNil` (D1) | done | yes | keep |
| `UberOn`'s `lookupNil_of_guard`, `srvLessorNil` (auth on) | guard `False` with auth on | yes at auth on | keep; auth on requires `lg = false` (2.13) |
| snapshot receive: `applyAll.specSnap` (`lg = false`), `applySnapshot.specSnap`/`Recover` (`lessorRevocable`), walk's `hlease` | premises | `Recover` would reload leases; `hlease` false | keep; `srvGrantOpen_snap` (D2) |
| snapshot send: `SnapSendBranch`, `bkRestAt`, `InvImage`'s "lease bucket empty" | image = `restModel` | **false**: the image has the lease records | `bkRestAt` over the leased image (2.14, Q5) |
| boot: `restBootBk` (empty `lease`), `NewLessor`'s empty-bucket premise | — | yes (fresh boot) | keep; restart of a granting cluster is not in scope |
| `ckptEffectsOk` (trusted, opaque) | docstring | vacuous in the example (feature off) | keep (S2 done; `axiom` pass pending) |

Nothing else found: `grep` of `False` arms (`rqOk`, `plainCover`, `dispatchKind` cases), "plain"
predicates (`plainCover`, `plainReq`, `plainEntry*`, `plainLog*`: a grant is not `plainCover`, the
generic apply lemmas over it never meet one), exact images (`srvRest`, `restModel`, `bkRestAt`,
`kvModelSt`), `kvModelSt_plain`-style lemmas (6 uses), `respMethods`/`reqFacts`, `E.RW`.

### 2. The chain, statement by statement (top-down)

**2.0 New vocabulary** (internal, pure unless said).
- apply: `grantIdsOk (L : List w64) (id ttl : w64) : Prop := id ≠ 0 ∧ sint.Z ttl ≤ maxLeaseTTL ∧ id ∉ L`
  (the clause's condition, named); `grantGoes (c : Chain) (rq) : Bool` (no corrupt or capped layer:
  `chainTable`'s path); `dispatchIds (c rq v3) (L) : List w64 := if dispatchKind rq = .leaseGrant ∧
  v3 ∧ grantGoes c rq then (match rq.leaseGrant with | some g => if grantIdsOk L g.id g.ttl
  then L ++ [g.id] else L | none => L) else L`; `grantRest (mt) (c rq v3) (L) (r : RestM)` the same
  case split with `restGrant mt g.id g.ttl r`.
- apply: `AEnv.mt : w64 := 0` (the lessor's `minLeaseTTL`), `AEnv.γlt : GName := default`;
  `ltHalf (E) (L) : IProp := if E.lg then ghostVar E.γlt ½ L else True` (the tie's half).
- server: `restLeases (mt) (lt : LeaseTable) (r) := lt.foldl (fun r p => restGrant mt p.1 p.2 r) r`;
  `appliedTable (γr) (A) := kvTableOf γr.kv.c0 γr.kv.ch0 [] (γr.raft.pre ++ A)`. Laws:
  `(dispatchTable c rq v3 lt).ids = dispatchIds c rq v3 lt.ids` (from `backendTable`, `leaseGrantOk`
  ⇔ `grantIdsOk`); `restEntry` commutes with `restGrant` (`restEntry_keep`: no `lease` write);
  `restLeases mt (lt ++ [(id, ttl)]) r = restGrant mt id ttl (restLeases mt lt r)`;
  `restLeases_mem` (members unchanged).

**2.1 `leasegrant.Main.spec`, `leasegrant_safe`** (draft): unchanged. Glue unchanged in shape:
alloc at `lg = true` (2.3), `kv_lease_grant_served`, the client's `Grant`/`Leases` at
`etcdLeaseGrantSpec`/`etcdLeaseLeasesSpec`.

**2.2 `common.kv_lease_grant_served`** (draft). Old post `grpcServeTok ∗ etcdKVAt addr E ρ γr cid
mid ∗ client.etcdLeaseReadAt addr ∗ etcdLeaseGrantAt addr E` → new: **without `etcdKVAt`** ((c): no
KV contract is registered; no KV call reaches the member in the closed world). Callees:
`kv_lease_served`'s steps (the gRPC slot, `raftLeaseRead_server`, the lower bound `0`), plus
`v3rpc.lessorGrantOkL_of_server` and the Lease service's `LeaseGrant`/`LeaseLeases` handler lemmas
at `etcdLeaseGrantSpec`/`etcdLeaseLeasesSpec` (the latter over `EtcdServer.LeaseLeases.spec`,
`leaseGrantedAt_lb_max`, `leaseGrantedAt_listed`). Glue: `kv_lease_served`'s proof minus the KV
registrations; `hG : srvGrantsLeases E ρ` feeds `lessorGrantOkL_of_server`.

**2.3 The allocation at `lg = true`** (internal, new): `srvClusterBootG_alloc` (beside
`srvClusterBoot_alloc`, which states `γk.lg = false`): the same ghost state with `γk.lg = true`, the
KV state's ghost variable kept **whole** for the KV invariant (no `etcdKV` returned, (C)), and
`memberBoot`'s row `lg = true → leasesNoExpiry ∧ srvGrantOpen` from `Main.spec`'s premise and
`srvGrantOpen_open`. A `common.alloc1G` for the example.

**2.4 `v3rpc.lessorGrantOkL_of_server`** (draft lemma; statement unchanged). Callees:
`EtcdServer.LeaseGrant.spec`, `etcdReached_of_certOk` (via `srvRevLb`), `leaseHdrAns`'s pieces.
Glue: call the spec with `S`'s lent readers; the success post `leaseGrantedResp` gives `ID ↦□ id`,
`leaseGrantedAt`, the header for `leaseGrantAns`; the error post `applyErrIs err`.

**2.5 `EtcdServer.LeaseGrant.spec`** (draft; statement unchanged). Callees: the id generator's
`Next` (`srvGenAt`, credits from `□ |==> idCred ρ.ids 1`), the tracer's specs (as `Put`'s),
`requireAuthInfo.spec` (auth off: `nil`), `raftRequest.spec`. Glue:
1. the loop writes `Next() & (2^63-1)` until non-zero: invariant `ID ↦ id`, exit `id ≠ 0`; persist
   `ID ↦□ id`, giving `leaseGrantIs r ⟨id, ttl⟩`, so `irrNoHdrIs p rq` for `rq := {leaseGrant :=
   some ⟨id, ttl⟩}` (`rq.id = 0`, `irrDepthOk rq`: one level);
2. `reqPropOkM false … rq (fun _ _ => True)` by the new grant disjunct (2.7): `grantPropOk ρ.kv.lg rq`
   from `srvGrantsLeases` and `grantKindOk` (no admin or side-effect field, `id ≠ 0`),
   `rqShape true rq` (`grantKindOk` is log-free), `irrNoZeroEnd rq` (no range);
3. success: `appliedOkM false E ρ rq' F resp L` now carries `grantAnsM E rq' resp` (2.6): `resp =
   mkOk *LeaseGrantResponse r` (the type assertion), and, `err = nil`, the response's `ID ↦□ g.id`,
   `TTL`, `Error`, `appliedHdr x.log` with `Revision ↦□ rv`, `sint.Z rv = x.log.length - 1`, and
   `∃ i, leaseGrantedAt E.γ.leases i g.id`; `g.id = id` by `irrWireOf`; `x'.log = x.log` (the grant
   leaves the log) with `idxCert`/`certOk` at `x'.log` give `srvRevLb E.γ rv`; `rv ≠ 0` from
   `appliedHdr`'s `2 ≤ x.log.length` — this is `leaseGrantedResp E r`;
4. error: `applyErrIs err`, `resp = nil`.

**2.6 `raftRequest.spec`, `processInternalRaftRequestOnce.spec`** (frozen; **text unchanged**). Their
definitions move:
- `appliedOkM on E ρ rq' F resp L` gains `∗ grantAnsM E rq' resp` (`True` unless `dispatchKind rq' =
  .leaseGrant`); `resPostM`, `resultIsW`, `resultIsWOn` gain `∗ grantArM E ar rq out` (the answer
  read through the result `ar`: `∃ v, ar ↦□ v ∗ grantAnswer E.γ.leases rq v.Resp' v.Err' x.log` for a
  dispatched grant, else `True`). The pattern of `authnArM`/`authnAnsM` (Q2).
- `grantAnswer γl rq resp err log` (apply, internal): for a grant `g`, `∃ r, resp = mkOk
  *LeaseGrantResponse r ∗ ((⌜err = nil⌝ ∗ grantRespIs r g log ∗ ∃ i, leaseGrantedAt γl i g.id) ∨
  ⌜err ≠ nil⌝)`, `grantRespIs` the fields of 2.5.3.
- Glue of both proofs: unchanged (they pass `reqPropOkM` to the proposal and the waiter's payload
  through); `grantAnsM_of_ar` (as `authnAnsM_of_ar`) in `raftRequest`.

**2.7 The proposal and the KV invariant** (internal; the decision (c) as (C), Q1).
- `reqPropOk γk rq Qr` gains a third disjunct `⌜grantPropOk γk.lg rq ∧ rqShape γk.lg rq ∧
  irrNoZeroEnd rq ∧ Qr = fun _ => True⌝` (no client update); `reqPropOk_off`'s pattern gives the
  old reading at `γk.lg = false` (`grantPropOk_false`). `reqPropOkM`/`reqPropOkOn`/`reqPropOkD`:
  `M false` is `reqPropOk`, the others unchanged (auth on is `lg = false`, 2.13).
- `kvInv γ γk`: `ghostVar γk.st ½ (kvModelSt γk L)` → `ghostVar γk.st (if γk.lg then 1 else ½)
  (kvModelSt γk L)`; `plainLogM γk.cmp false L` → `plainLogM γk.cmp γk.lg L`. At `lg = false` the
  old text (law `kvInv_false`).
- `kv_prop_au` (statement unchanged): the new disjunct `kv_prop_au_grant`: at the commit, `L ++ [e]`,
  update the whole variable to `kvModelSt γk (L ++ [e]) = kvOpStep (.leaseGrant id ttl) σ`
  (`kvModel_snoc_state`), the entry facts by `plainEntryM`'s third disjunct, `kvWork_snoc` (no
  puts), `cmpLogOk` (no compaction); `Qr` trivial. The write forms (`kv_prop_auW`) at `γk.lg = true`:
  opening the client's AU gives `etcdKV γk σ` (½), against the invariant's whole variable: `False`
  (`ghostVar_valid`); at `false` the old proof. Same for `kv_fire_reads` (a deposit's `kvReadAu`) and
  `kv_revLbZ_le`. So `EtcdServer.Put`, `DeleteRange`, `Txn`, `Range`, `Compact` keep their text and
  stay true at `lg = true` (their client update cannot exist there).

**2.8 The shapes** (internal): `kvWork`'s, `isServerRun`'s `logShape`, `srvLogShapes`,
`reqPropOk(W)`'s `rqShape` from `false` to `γk.lg`/`E.lg` (`rqShape_mono : rqShape false rq →
rqShape lg rq` for the old forms); `entryOk x m` → `entryOk lg x m` (`rqOk lg`), `entryOkM on lg`.
`EtcdServer.applyAll.spec` (frozen): `logShape false` → `logShape E.lg` (3a's `false` reverted to the
meaning B1 intended); `applyEntries`/`apply`/`applyEntryNormal.spec` (frozen): `logShapeM`,
`entryOkM` at `E.lg` (text: one argument).

**2.9 The apply thread's rest and tie** (internal; `srvRest` is the carrier, so the apply-thread
specs' text does not change).
- `srvRest E γr A := E.RO (restModel c0 boot (pre ++ A))` → `if E.lg then E.RO (restLeases E.mt
  (appliedTable γr A) (restModel …)) ∗ ltHalf E (appliedTable γr A).ids else E.RO (restModel …)`.
  Laws: `srvRest_false`; `srvRest_snoc`/`srvRest_nodata` as before; `srvRest_applyG` (new; replaces
  `srvRest_apply`'s `plainCover` premise by `rqOk E.lg`): after `Apply` with its post (2.10),
  `E.RO (grantRest E.mt ch rq v3 T (restOut rq v3 out rs)) ∗ ltHalf E (dispatchIds ch rq v3 T)` at
  `rs := restLeases …`, `T := (appliedTable γr A).ids` is `srvRest E γr (A ++ [m])` (2.0's laws).
- `srvKVInvs E γr` gains `srvGrantable E := □ (⌜E.lg = true⌝ → ∀ id, lease.leaseGranted E.γ.leases
  id)` (persistent). Why true: `NewServer` creates the lessor with guard `srvGrantGuard lg on = ⌜
  leasesNoExpiry ∧ lg ∧ ¬ on⌝` (`lessorGuard`), and at `lg = true` has `leasesNoExpiry` (`%Hslg`) and
  `on = false`.
- `applyEntryNormal.wp_proof` (spec text unchanged but `entryOkM`): opens `srvRest`, calls `Apply`
  with `rs`, `T`, `grantPermRq E rq` (from `srvGrantable` and `rqOk E.lg`: a grant kind only at
  `lg = true`), recloses `srvRest (A ++ [m])` by `srvRest_applyG`, hands `grantArM` to the waiter
  with the result (`resultIsW`). `apply`, `applyEntries`, `applyAll`, `run`: unchanged proofs (they
  pass `srvRest`), but the snapshot-send branch (2.14).

**2.10 `apply.uberApplier.Apply.spec`, `dispatch.spec`** (frozen; text changes):
- pre: `⌜rqOk false log rq ∧ …⌝` → `⌜rqOk E.lg log rq ∧ …⌝`; `+ grantPermRq E rq` (`□ (⌜dispatchKind rq
  = .leaseGrant⌝ → ∀ g, ⌜rq.leaseGrant = some g⌝ → lease.leaseGranted E.γ.leases g.id)`, the
  pattern of `cmpPermRq`); `+ ltHalf E T` (new `∀ T`).
- post: `E.RO (restAfter rq v3 rs)` → `E.RO (grantRest E.mt c rq v3 T (restAfter rq v3 rs))` (Apply:
  through `restOut`); `+ ltHalf E (dispatchIds c rq v3 T)`; `+ grantRes E rq v3 log ar` (Apply:
  `applyGrantRes E rq v3 x.log ar out`, `True` but for a dispatched grant: 2.6's `grantAnswer` read
  through `ar`).
- `kvOwn E log` (text unchanged) now holds the other half: `leasesLive E s := ∃ L, txn.leasesKnown L
  s ∗ lease.lessorUser E.γ.leases L (leaseItemsOf s) ∗ ltHalf E L` (was over `E.γ`). The two halves
  agree (`L = T`) wherever both are held, and only a holder of both changes `L`: every non-grant
  path recloses `kvOwn` with its `L` and leaves `T`. This is the tie, without naming `L` in the
  ≈300 statements that pass `kvOwn` (Q3).
- Callees of `dispatch`'s grant arm: `rqOk E.lg` (⇒ `E.lg = true ∧ grantKindOk rq`), the chain's
  grant triple (2.11), `grantPermRq`. Glue: `LeaseGrant` is dispatched only with `v3` (first
  `switch`, then `!shouldApplyV3`); without `v3` the result is `nil`, `dispatchIds`/`grantRest` the
  identity; every other arm frames `ltHalf E T`.
- `Apply`'s glue: its auth check passes a grant (`needAdminPermission rq = false`); frames the rest.

**2.11 The chain's grant triple** (internal: `applierTriples`; `LeaseGrant` leaves `respMethods`,
`reqFacts`'s `LeaseGrant` clause goes):
```
□ ∀ (r : Loc) (rq) (g : LeaseGrantModel) (log) (T : List w64) (rs : RestM) (Pre Q Post) (info),
  {{ ⌜rq.leaseGrant = some g ∧ dispatchKind rq = .leaseGrant⌝ ∗ leaseGrantIs r g ∗
     lease.leaseGranted E.γ.leases g.id ∗ ltHalf E T ∗ E.RO rs ∗ mvcc.storeWT E.γ ∗
     mPre E c (.ok ai) info log Pre Q Post ∗ ciSplit E Pre }}
    ai.LeaseGrant(r)
  {{ (resp : Loc) (err), RET (resp, err); mPost E c (.ok ai) log Pre Post ∗ applyErrIs err ∗
     ltHalf E (chainIds c rq T) ∗ E.RO (chainRest E.mt c rq T rs) ∗
     grantAnswer E.γ.leases rq (mkOk *LeaseGrantResponse resp) err log ∗
     ⌜err = nil ↔ grantGoes c rq ∧ grantIdsOk T g.id g.ttl⌝ }}
```
(`chainIds`/`chainRest`: `dispatchIds`/`grantRest` without the `v3` test.) Per layer
(`newApplierV3*.lean` prove `applierTriples` for each):
- backend (`applierV3backend.LeaseGrant.spec`, frozen, restated to this triple): callees the
  Grant clause (2.12), `newHeader` (the KV's `Rev()` at the sole writer: `rv = |log| - 1`), `Lease.TTL`
  (`leaseTTLIs`). Glue: open `kvOwn` → `L`, `ltHalf E L`; agree with `ltHalf E T` → `L = T`; clause
  with `RO rs`; on success update both halves to `T ++ [g.id]` (`ghostVar_update_halves`), reclose
  `kvOwn` (`leasesKnown` grows: `leasesKnown_mono`); the response's fields; `appliedHdr` as `Put`'s.
- quota (`quotaApplierV3.LeaseGrant.spec`, restated): inner triple, then `Available` is `true`
  (`isQuota`'s premise, the chain's quota comment): `err` unchanged, so `err = nil ↔ granted` holds
  (the `ErrNoSpace`-after-grant branch is dead under the existing premise, not a new one).
- auth (embedded, no override): the inner triple.
- capped / corrupt (`applierV3Capped/Corrupt.LeaseGrant.spec`, restated): `nil, ErrNoSpace` /
  `nil, ErrCorrupt`; `grantGoes = false`: halves, RO, `L` unchanged. (Not reached from `ch0`, which
  has neither layer; stated for the generic chain.)

**2.12 The lessor contract** (trusted contract, derived for the real lessor):
- `isApplyLessor le s γ P f RO RW` → `isApplyLessor le s γ P f RO RW mt` (new argument, the
  server's `E.mt`); its Grant clause: pre `… ∗ leaseGranted γ.leases id ∗ RW` → `… ∗ leaseGranted
  γ.leases id ∗ RO rs` (new `∀ rs`); post error arm `+ RO rs`, success arm `+ RO (restGrant mt id ttl
  rs)`; conditions written `grantIdsOk L id ttl`. True of Go: `Grant` puts exactly `leaseEnc id
  (grantTTL mt ttl) 0` under `leaseKey id` (`lessor.go:311`, `persistTo`), on success only.
- `isApplyLessor_of_lessorInv` (proof): over `lease.lessor.Grant.spec` with `Rb := storeRb γ`
  from the RO lens (the revoke clause's lens, `revokeClause_of_lessorInv`), `mt` agreed from
  `lF "minLeaseTTL" lp ↦□ mt` (a new premise, from `lessorCfg` at `NewServer`), the put's
  `Rb (rbSet …)` turned back into `RO (restGrant …)` by the lens (`grant_bk`).
- **`lease.lessorBackend`/`lessorApplyOk`** (trusted: the `NewLessor` axiom's contract): its write
  token `wbTok ∗ RW` with `rwLens RW (lessorBeOn lp be)` is spent whole today; the lens needs
  `lessorBeOn` back. Restated: the token `wbTok` spent, the lent part `RW` returned by `Unlock`. True
  of Go: a write through `le.b.BatchTx()` does not change `le.b`. `lease.lessor.Grant.spec`,
  `Checkpoint.spec`, `persistTo` (proved) give it back (Q4).

**2.13 `NewServer.spec`/`specM`/`specG`** (frozen; text: one row). `%Hslg` unchanged; `specM true`
(auth on) takes `ρ.rd.kv.lg = false` (its guard is `False`: no grant there; `memberBootOn` already
allocates `lg = false`). Proof: allocate `E.γlt` at `[]` (both halves at `lg = true`: one into the
boot's `leasesLive` with `NewLessor`'s `leaseOwn γl [] ∅`, one into `srvRest E γr []`); choose
`E.mt` from `lessorCfg`; prove `srvGrantable E` (2.9).

**2.14 The snapshot side**. Receive: unchanged, `srvGrantOpen_snap` (its body names `applyRes`,
which now holds the new `srvRest`: still true, still sealed). Send (`applyAll`'s `msgSnapC` branch,
`SnapSendBranch.lean`, live in multi-member clusters): it reads `srvRest` as the image and states
`bkRestAt c0 bootLog L D` (`rbData D = (restModel …).bk`, so "the lease bucket empty",
`InvImage.lean:187`), false at `lg = true`. Restated (Q5): `bkRestAt c0 mt bootLog L D := rbData D =
(restLeases mt (kvTableOf c0 ch0 [] L) (restModel …)).bk`; the "empty" law takes a plain log. The
two S2 `sorry`s there (`mergedCreate_window`, `merged_image`) keep their role, at true statements.

**2.15 The trust base after the design**. Restated trusted: `isApplyLessor`'s Grant clause (2.12),
`lessorApplyOk`/`lessorBackend` (lent part returned, 2.12); both for the `axiom` skill's pass
(with `ckptEffectsOk`, `leasesNoExpiry`, pending). `srvGrantOpen` keeps one field (`snap`): every
other `lg = true` obligation is proved from callees. New `sorry`s: none beyond `srvGrantOpen_open`
and the Prove stage's drafts (`EtcdServer.LeaseGrant.wp_proof`, `lessorGrantOkL_of_server`,
`kv_lease_grant_served`, `leasegrant.Main.wp_proof`).

### 3. The size, and the commits

Sites (`grep -c` over `Proof/ Spec/`, sites / files) per changed definition: `rqOk false` 17/10,
`rqShape false` 21/10, `logShape false` 13/9, `entryShape false` 5/3, `entryOk` 15/10, `logShapeM`
15/3, `plainLogM γk.cmp false` 5/4 (to `lg`); `leasesLive` 29/13 (and the ≈13 proofs that open it,
which carry `ltHalf`); `isApplyLessor` 70/31 (`mt`); `respMethods` 17/10, `reqFacts` 15/10, the four
`LeaseGrant.spec`s 16/13, `applierTriples` 49/31 (the new triple; the layer proofs' intro
patterns); `dispatch.spec` 4/4, `Apply.spec` 12/6; `restAfter` 21/11, `restOut` 16/8 (wrapped by
`grantRest` at the two specs and `srvRest_applyG`); `srvRest` def 1, proofs unfolding it 18/8;
`bkRestAt` 29/4; `kvInv` def 1, proofs opening it ≈10 (off mode); `reqPropOk` 31/10;
`appliedOkM` 32/16, `resPostM` 12/6, `resultIsW` 33/12 (defs; constructors ≈10); `srvKVInvs` 1 def
(167 uses, unchanged); `lessorBackend`/`lessorApplyOk` 11/9 + 18/9; `lease.lessor.Grant.spec` 16/10;
allocs 32/9. Not touched: `kvOwn` (288/73), `ApplyKV` (549/92), `dispatchAnswer`/`dispatchResult`/
`applyResultIs` (58+38+88). Roughly 450 edited sites, most mechanical.

Commits, each a full build with the checks of the last section (`tcb-report --check` new only
`srvGrantOpen_open` and the drafts; every collection unchanged; `gen-init`, `gen-interface`):
1. **Pure** (new modules, no rebuild above them): 2.0's apply and server definitions and laws.
2. **Lease package** (rebuilds lease and everything above, once): `lessorBackend`'s lent part,
   `lessorApplyOk`, `Grant.spec`/`Checkpoint.spec`/`persistTo` returning it.
3. **Apply package and the apply thread** (one full server rebuild): `AEnv.mt`/`γlt`, `ltHalf`,
   `leasesLive E`, `isApplyLessor … mt` with the RO Grant clause and its derivation, the grant
   triple and the five layers, `dispatch.spec`/`Apply.spec`, `grantAnswer`/`grantRes`; on the server
   side in the same commit (it cannot build otherwise): `srvRest` gated, `srvRest_applyG`,
   `srvKVInvs`' `srvGrantable`, `entryOk`/`logShape` at `E.lg`, `applyEntryNormal`, `NewServer`'s
   allocations, `bkRestAt` and the send branch.
4. **The request path** (full server rebuild): `kvInv` (C), `reqPropOk`'s grant disjunct,
   `kv_prop_au_grant` and the refutations, `plainLogM γk.cmp γk.lg`, `kvWork`'s shapes,
   `grantArM`/`grantAnsM` in `resultIsW`/`resPostM`/`appliedOkM`, `NewServer.specM true`'s
   `lg = false`, the `lg = true` allocation.
5. **Leaves** (cheap): `EtcdServer.LeaseGrant.wp_proof`, `lessorGrantOkL_of_server`,
   `kv_lease_grant_served` (post without `etcdKVAt`), `alloc1G`, `leasegrant.Main.wp_proof`.
Commits 3 and 4 may be merged to save one full rebuild; kept apart for review.

### 4. Open questions (for the user)

- **Q1. The KV state of a granting cluster** (how (c) is realized). (A) As L4 decided: a grant
  carries its client update `kvOpAu γk (.leaseGrant id ttl) Q`; `LeaseGrant.spec` takes `□ ∀ id,
  kvOpAu …`, the served side keeps `etcdKV` and makes it; but then a write's AU exists at `lg = true`
  and `Put`/`DeleteRange`/`Txn`/`Range.spec` are false there: each needs a premise `ρ.kv.lg = false`
  (frozen texts change, every caller threads it). (B) Drop the table from the clients' state
  (`kvModelSt := kvStateOf (kvModel γk L)`, L3a's state half undone): every KV result true at any
  `lg`, no update for grants; L6 must put it back. (C) The KV invariant owns the state's ghost
  variable whole at `lg = true`; a grant steps it without a client; any client AU is refutable, so
  every KV result is true (vacuously) with its text unchanged; L4's client update is not used.
  **Recommended: (C)** (smallest; exactly "no claim about the KV service"; L6 later replaces it by
  (a) of the blocker).
- **Q2. Where the grant's answer travels.** (i) In `dispatchAnswer`'s arm, with the lessor's name
  (the review's B1; `dispatchAnswer`/`dispatchResult`/`applyResultIs` gain `γl`, ≈184 sites).
  (ii) Beside it, `grantRes`/`grantArM`/`grantAnsM` (the `authnArM` precedent; ≈15 statement sites).
  **Recommended: (ii).**
- **Q3. The tie's carrier.** (a) Two halves of a ghost variable gated on `lg`: one in `kvOwn`'s
  `leasesLive`, one beside the rest image in `srvRest` and through `Apply`/`dispatch` (`ltHalf`). (b)
  The live set explicit in the apply state (the leases plan's L3b: `ApplyKV.ids`, `kvOwn E log L`,
  every applier triple's `mPre`/`mPost`/`kvPost`: ≈300 statement sites, ≈80 files). **Recommended:
  (a)**; (b) when leased puts need the live set in every triple (L3b/L6).
- **Q4. Getting `lessorBeOn` back from `Grant`.** (a) Restate the trusted `lessorApplyOk` so the
  write's lent part returns at `Unlock` (true of Go). (b) Keep `RW`: lend `E.RW` per grant, which
  steps the backend's client half outside `E.RO`, so `srvRest` is not exact (the rejected
  alternative of B2). **Recommended: (a)**, with the `axiom` skill's pass.
- **Q5. The snapshot send path.** (a) `bkRestAt` over the leased image (true; the S2 `sorry`s keep
  their role). (b) A second sealed field `srvGrantOpen_send` for `applyAll`'s branch at `lg = true`
  (no restatement of `bkRestAt`, but the field must name `applyAll`'s branch, which sits inside
  `isServerApplyAll`'s user: the circularity commit 1 met). **Recommended: (a).**
- **Q6. Auth on with `lg = true`.** Required `lg = false` (2.13; recommended: the grant guard is
  `False` there and no example needs it), or supported (a stage of its own).

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
