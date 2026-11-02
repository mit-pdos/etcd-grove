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

## B1/B2 in place, with the tie: the work, in commits that each build (2026-11-02; next)

**Where it stopped** (2026-11-02, second agent): commit 3a done (the `lg` parameters at `false`, COMMIT3A); commit 3b blocked on a decision (below, "The blocker"). Before that: commits 1 and 2 done (checks after 2: full build, `tcb-report.py --check` new only `srvGrantOpen_open` and `leasegrant.Main.wp_proof`, every collection `--reuse --check` unchanged, `gen-init.py --check`, `gen-interface.py --check` backend and raft unchanged) (`75676e772c`, `7a83c345aa`), each a full
build; commit 3 not started (below, what it needs, found by the survey of its consumers). Every
commit: full build, `etc/tcb-report.py --check` (only `srvGrantOpen_open`, until commit 1
`runSnapLgOk_open`, and `leasegrant.Main.wp_proof` new) and every collection `--reuse --check`
unchanged.

**Done, with the deviations:**

- *Commit 1* (`75676e772c`): `apply.AEnv.lg : Bool := false` (the server's `E`: `ρ.rd.kv.lg`).
  Deviation: tied in `srvKVInvs` beside the retention (`⌜γr.kv.cret = E.cret ∧ γr.kv.lg = E.lg⌝`),
  not `srvEnvOk`, which has no names. `runSnapLgOk` renamed the bundle `srvGrantOpen` (one field
  so far, `srvGrantOpen_snap`; `srvGrantOpen_open` the `sorry`). Deviation: **not carried into
  `isServerApplyAll`**: the snapshot field's triple (`runSnapLgOkBody`) mentions
  `isServerApplyAll` (`InvRun` imports `InvApplyAll`), so the bundle inside it is circular; and
  `applyEntryNormal.spec` sees `isServerM`, not `isServerApplyAll`. The apply thread's grant fields
  need a bundle of their own (commit 3, below).
- *Commit 2* (`7a83c345aa`): `rqOk (lg : Bool) log rq`, the grant arm `match lg with | true =>
  grantKindOk rq | false => False` (`grantKindOk`: dispatched to `LeaseGrant`, no admin or
  side-effect-free field, id `≠ 0`), every other arm unchanged; laws `rqOk_false_leaseGrant`,
  `rqOk_of_false`, `rqOk_leaseGrant`. Deviation: **every statement site passes `false`**, not
  `E.lg` (`dispatch.spec`, `uberApplier.Apply.spec`, `applyFnKVL`/`ApplyKVL`/`ApplyRec`,
  `InvApplier`'s and `ApplyNormalOn`'s entry facts, `rqShape`, `DispatchKVL`): `dispatch`'s proof
  cannot take a grant until its grant arm (commit 4: `leaseGranted`, `E.RW`), so a site at `E.lg`
  would be unprovable at `lg = true`. `rqOkM` keeps its signature, over `rqOk false`. The proofs
  are unchanged (the arm reduces to `False` at the literal). `plainCover` not changed (commit 3,
  where its grant arm gets a meaning).

**The previous agent's question, answered (the user, 2026-11-02; `notes/leases-plan.md` L4):** a
grant takes its own client update, `kvOpAu γk (.leaseGrant id ttl) Q`, as puts take theirs; the
model's table steps on it (`kvTable`, L3a, done; `kvOpStep`'s grant checks `leaseGrantOk`). So a
grant entry changes the clients' state `kvModelSt γk L` (its `leases`), and the KV invariant fires
the grant's update at the commit.

**Commit 3a (done, COMMIT3A):** the `lg` parameters, every site at `false` (meaning unchanged):

- `plainEntryM (cmp lg : Bool)`, `plainLogM (cmp lg : Bool)` (`KVModelDefs.lean`): a third disjunct
  `grantPropOk lg rq` (new: `lg = true ∧ apply.grantKindOk rq`), the compaction form's pattern;
  `plainEntryM_lg_false` gives the old two-disjunct reading at `lg = false`; `plainEntryM_false`,
  `plainLogM_false` at `false false`; `plainEntryM_of`, `plainLogM_of`, `plainLogM_append` generic
  in `lg`; `kvTable_plainM`, `kvTableOf_plainM`, `kvModelSt_plain`, `kv_fire_reads`, the restore
  lemmas (`KVModelRestore`), `ApplyCmpArm`'s, `M2ApplyDraft`'s at `lg = false`. The KV invariant
  `kvInv` (and `BuildAlloc`'s, `KVApply`'s statements) at `plainLogM γk.cmp false`.
- `rqShape (lg)`, `entryShape (lg)`, `logShape (lg)` (`WorkloadDefs.lean`): `rqOk lg`; every site at
  `false`, among them the statements `EtcdServer.applyAll.spec` (`Spec/`, frozen: text `logShape` →
  `logShape false`, meaning unchanged), `ModeSpecs`' `applyAll`/`applyEntries` instances, `kvWork`,
  `reqPropOk(W)`'s and `reqPropOkOn`'s `rqShape`, `isServerRun`'s `logShape`, `srvLogShapes`.
- **Deviation:** `plainCover`/`plainReq` not changed (planned: an `lg` parameter on `plainCover`).
  The admission is `plainEntryM`'s disjunct, as the compaction's (`plainCover` is what the generic
  apply-side proofs cover, `backendTable_plain` and the like, none of which a grant meets), so the
  95 + 26 sites of `plainCover`/`plainReq` stay as they are.

**The blocker found by commit 3a's survey (2026-11-02): a granting cluster's KV results.** Admitting
a grant entry into the KV invariant at `lg = true` (`plainLogM γk.cmp γk.lg L`) makes every
existing KV result false there, not just unproved:

- `reqPropOkW`'s write forms promise `□ Q (kvStateOf (kvModel γk L))` (the lease-free state of the
  log's model), while the update fires `Q σ` at the invariant's `σ = kvModelSt γk L =
  kvStateOf (kvModel γk L) (kvLeases γk L)`; `kv_prop_auW` bridges them by `kvModelSt_plain`, true
  only of a grant-free log. After a granted lease the two states differ (`leases`), and `Q` is the
  client's, arbitrary (it may read `σ.leases`).
- So `EtcdServer.Put.spec`/`DeleteRange`/`Txn` (post `Q (kvStateOf x.log)`), the client contracts
  (`putReplied`'s `Q (kvStateOf x.log)`, trusted), and the reads (`kvDep`/`regOk` at `kvStOff γk L
  = kvStateOf (kvModel γk L)`, `kv_fire_reads` by `kvModelSt_plain`) are false in a cluster that
  has applied a grant. A named hypothesis for them in `srvGrantOpen` would be false (it would make
  `leasegrant_safe` vacuous), so commit 3's grant disjunct cannot be added to `reqPropOk` and the
  invariant soundly until they are restated. (`leasegrant` serves the KV service too, through
  `kv_lease_grant_served`, so they are reached there.)

This is `notes/leases-plan.md`'s L3a finding ("a reply's state must come from the committed log
`Lq` ... those results move to `kvModelSt γk Lq` when grants are admitted"), which S1 (a) deferred
and the L4 decision (the grant's own client update) makes due now. **Options, for the user:**

- **(a) The results at the full state** (L3d's move, brought forward): the write forms' and the
  read deposits' result at `kvModelSt γk L` (then `kv_prop_auW`'s proof drops `kvModelSt_plain`;
  `reqPropOk_shape`/`kv_qinv` by `kvModel_eqv`'s table half); the server's KV specs and the client
  contracts (`putReplied`, `txnReplied`, `rangeReplyOk`'s `Q`, trusted) at the committed table:
  `Q (kvStateOf x.log lt)` with `lt` the table of the committed log the entry met, which needs the
  apply side to know it (`ApplyKV.leases`, or the tie of step 5 exported with `appliedOk`). At
  `lg = false` `lt = []` (plain logs). The most work; the right end state (the leases plan wants it).
- **(b) Lease-blind KV clients in a granting cluster:** the KV forms at `lg = true` carry only a
  `Q` that ignores the table (`∀ σ lt, Q σ ⊣⊢ Q {σ with leases := lt}`), a premise of the KV
  client contracts in a granting cluster (trusted change; a client of the example's KV service
  never reads the table). Less work; restricts the KV contracts where leases are granted.
- **(c) No KV client updates in a granting cluster:** the write forms and read deposits require
  `γk.lg = false`; at `lg = true` the served KV service registers only the `…Any`-style contracts
  (no `Q`), so `kv_lease_grant_served` states less. Least work; the example's theorem says nothing
  of the KV service's results.

Until then, commit 3b (the grant disjunct of `reqPropOk(W)`/`On`/`M`/`D`, `kvInv` at `γk.lg`,
`kv_prop_au`'s grant case: fire `kvOpAu γk (.leaseGrant id ttl) Q` at the commit, the state stepped
by `kvModel_snoc_state`, which already covers every request) waits; the rest below is unchanged.

**Commit 3, what it needs** (the survey of `reqPropOk`'s consumers, 2026-11-02; larger than planned):

- `reqPropOk`'s consumer `kv_prop_au` (`KVLemmas.lean`) puts the entry into the KV invariant, whose
  per-entry facts exclude a grant: `plainLogM γk.cmp` (`plainCover`'s grant arm `False`),
  `logShape`'s `rqShape` (`∀ log, rqSmall log rq → rqOk false log rq`), `entryClaim`, and the KV
  state `ghostVar γk.st (kvModelSt γk L)`. So the grant disjunct needs, in the same commit:
  `plainCover`/`plainReq`/`plainEntryM`/`plainLogM` and `rqShape`/`entryShape`/`logShape` at
  `γk.lg` (95 + 33 + 32 sites; every KV-model lemma over a plain log at `lg = false` or stepping
  `backendTable`), `kvModelSt` of a grant entry (the table's step, `leaseGrantOk`).
- The KV state's step: if a grant changes `kvModelSt` (its lease table), the invariant needs the
  clients' half of `etcdKV`, so the disjunct carries an update, `kvOpAu γk (.leaseGrant id ttl) Q`
  (as the write forms; `KVOp.leaseGrant` exists), its `Qr` the client's result; if the table is
  not in `KVState`, a step of the model only. To decide before the edit.
- The apply thread: a grant entry at `lg = true` reaches `applyEntryNormal`, whose `entryOkM` gives
  `rqOk false` (commit 2) to `dispatch`: its grant case is an open field until commit 4, in a
  sealed bundle **not** mentioning `isServerApplyAll` (say `srvGrantOpenApply`, before
  `InvApplier`; `srvGrantOpen := srvGrantOpenApply ∧ runSnapLgOkBody`), carried by what
  `applyEntryNormal` sees (`isServerM`'s fields or a premise of its spec, gated on `γr.kv.lg`), and
  `entryOkM`/`InvApplier`'s entry fact at `γr.kv.lg`.
- The request path (`processInternalRaftRequestOnce`, `raftRequest`, `reqPropOkM`/`On`/`D`) carries
  the disjunct; at `lg = false` it is refuted (`reqPropOk_off`'s pattern).

1. **`AEnv.lg` and the bundled row.** Add `lg : Bool := false` to `apply.AEnv` (`Chain.lean:372`, as
   `cmp := false`); `srvEnvOk` ties it to `ρ.rd.kv.lg`. Replace `runSnapLgOk` by one sealed bundle
   `@[no_expose] def srvGrantOpen : Prop` (`InvRun.lean`): `runSnapLgOkBody` ∧ the open grant cases
   of commits 3-5 as they are added (each a named field, `srvGrantOpen_snap`, ...), the row
   `%Hslg : ρ.rd.kv.lg = true → lease.leasesNoExpiry ∧ srvGrantOpen`, carried as now
   (`isServerBuilt(On)`, `isServerRun(On)`, `memberBoot(On)`), and in addition into `isServerApplyAll`
   (the apply thread's `applyEntryNormal`, which needs it for a grant entry). `runSnapLgOk_open`
   becomes `srvGrantOpen_open` (one `sorry`, leasegrant only).
2. **`rqOk` in place** (126 sites, 26 files, most in `uberApplier__dispatch.lean` (44),
   `DispatchKVL.lean` (23), `DispatchAdmin.lean` (13)): `rqOk (lg : Bool) log rq`, the
   `.leaseGrant` arm `lg = true ∧ grantKindOk rq` (`dispatchKind = .leaseGrant`, no admin permission,
   the grant's `id ≠ 0`; the id's freshness and the TTL bound are not premises: the tie makes the
   outcome a function of the table), every other arm unchanged; `rqOk false log rq ↔` the old
   (`rqOk_false`, by `rfl` per arm). Mechanical: every site passes `E.lg` (or `false` where it has
   no `E`); the proofs' `.leaseGrant` case was `False.elim`, now `hlg ▸` on `E.lg = false`, except in
   `dispatch` (commit 4). `plainCover`'s grant arm likewise behind `lg` (`KVModelDefs.lean:72`), its
   lemmas (`backendTable_plain`) take `lg = false` or are restated to `backendTable` stepping.
3. **`reqPropOk(W)` in place** (`InvRequest.lean:574, 733`; and `reqPropOkOn`/`reqPropOkM`/`D`):
   a disjunct `⌜γk.lg = true ∧ grantKindOk rq⌝ ∗ Qr = (the grant's table step)`; the request path
   (`raftRequest`, `processInternalRaftRequestOnce`) carries it unchanged for `lg = false`.
4. **`dispatchAnswer` with the lessor's name** (143 sites of `dispatchAnswer`/`dispatchResult`/
   `applyResultIs`; `InvUber.lean:299`): a parameter `γl`, the `.leaseGrant` arm (was `_ => True`)
   `∃ r, resp = *LeaseGrantResponse r ∗ (err = nil ∗ grant's fields ∗ leaseGrantedAt γl i id ∨
   err ≠ nil ∗ (the table refuses it, ¬ leaseGrantOk lt id ttl, or the quota's ErrNoSpace))`.
   **`ErrNoSpace`**: the quota applier answers `ErrNoSpace` after a successful grant when the
   backend's size is over the quota (`quota.go`'s `Available` checked after the call); the server's
   `apply.backendUnderQuota` premise is what makes that branch dead, so the arm states
   `granted ↔ err = nil` *under* `backendUnderQuota` (the fact the proof has, through `isQuota`'s
   `Available` premise), and the disjunct is otherwise `err = ErrNoSpace ∧ granted`. Proof: the five
   layers' `LeaseGrant` triples exact (`applierTriples`), `isApplyLessor`'s Grant clause (already
   exact) at `L = lt.ids` (the tie, 5). Open case in a granting cluster: a field of `srvGrantOpen`.
5. **The tie (B2).** In the apply thread's invariant (`applyRes`/`srvApplyInv`), the lessor's live
   set is the table: `leaseOwn γl L I ∗ ⌜L = (kvLeases γk A).ids⌝` (the leases plan's `leasesLive`),
   true at boot (both empty). The grant entry steps the rest model by `restGrant mt id ttl`
   (`RestLease.lean:31`, with `minLeaseTTL` named in `ReqNames`) exactly when `leaseGrantOk` (the
   table's step `backendTable`), and `E.RW`: the Grant clause consumes the lease bucket's write
   right; in a granting cluster the apply thread lends it per grant from `srvRestRW` and gets it
   back after the batch (`lessorBackend`'s `T` split: `storeWT` ∗ `lessorBeOn`), which needs
   `lease.lessor.Grant.spec` to return `lessorBeOn` (a change to a proved spec; its proof gives it
   back already after `Unlock`). `revokeClause`'s `restRevoke` is the pattern.
6. **The specs carrying the grant.** `dispatch.spec`, `processInternalRaftRequestOnce.spec`,
   `raftRequest.spec`: their result's `dispatchAnswer` at `E.γ.leases` gives the grant's
   `leaseGrantedAt` (no second spec). Then `EtcdServer.LeaseGrant.wp_proof` over `raftRequest.spec`,
   `lessorGrantOkL_of_server`, `kv_lease_grant_served`, `leasegrant.Main.wp_proof` (the Prove stage).

