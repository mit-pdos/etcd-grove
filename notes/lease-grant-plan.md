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

## Design of the server chain (2026-11-02, round 2)

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
- **S2** (`leaseGrantedAt` needs the mode): `srvGrantable` now carries `lessorModeIs E.γ.leases true`
  and sits in `srvSnapRO` beside `lessorModeIs` (M2), not in `srvKVInvs`; `grantPermRq` carries it
  too, so the backend triple converts `leaseLiveFrom` to `leaseGrantedAt`.
- **S3**: `srvRest_applyG`'s premise is `plainCover rq ∨ grantPropOk E.lg rq` (`plainEntryM`'s).
- **S4**: `bkRestAt` keeps its text; `imageAt γk` gates it: `if γk.lg then bkRestAtL … else
  bkRestAt …` (2.14). `bkRestAt_boot` and the receive proofs at `lg = false` are untouched.
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
| `imageAt`'s `bkRestAt` (cluster-wide), `bkRestAt_boot` ("lease empty") | image = `restModel` | **false** after a grant | gated in `imageAt` (2.14) |
| `srvGrantGuard`, `lessorOk`, expiry arms, `srvLessorNil` (D1) | done | yes | keep |
| `UberOn`'s guard, `srvLessorNil` (auth on) | guard `False` with auth on | yes | keep; auth on requires `lg = false` (2.13) |
| snapshot receive (`applyAll.specSnap`, `Recover`, walk's `hlease`) | premises | `hlease` false at `lg = true` | keep; `srvGrantOpen_snap` (D2), now true at any members' TTLs (B1) |
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
  (f id) r) r`; `appliedTable γr A := kvLeases γr.kv (γr.raft.pre ++ A)`. Laws:
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
- `srvRest E γr A := E.RO (restModel …)` → `if E.lg then ∃ f, E.RO (restLeasesWith f (appliedTable
  γr A).ids (restModel …)) ∗ ltHalf E (appliedTable γr A).ids else E.RO (restModel …)`. Cluster-wide
  where it is used (`runSnapLgOkBody`, the send branch): only ids, the TTLs under `∃ f` (B1).
- Laws: `srvRest_false`; `srvRest_snoc`/`_nodata`; `srvRest_applyG` (one lemma, generic in `lg`;
  replaces `srvRest_apply`): premise `plainCover rq ∨ grantPropOk E.lg rq` (S3, what `plainEntryM`
  gives; `grantKindOk` excludes `noSideEffect` and admin), from `Apply`'s post (2.10) `∃ t, E.RO
  (grantRest t rq o (restOut rq v3 o rs)) ∗ ltHalf E (grantIds rq o T)` at `rs := restLeasesWith f …`,
  `T := (appliedTable γr A).ids`, gives `srvRest E γr (A ++ [m])` with `f' := update f g.id t`
  (`restLeasesWith_snoc`; `g.id ∉ T` by the triple's `o ↔ grantIdsOk`).
- `srvGrantable E := □ (⌜E.lg = true⌝ → (∀ id, lease.leaseGranted E.γ.leases id) ∗
  lease.lessorModeIs E.γ.leases true)` (S2), a conjunct of `srvSnapRO` beside `lessorModeIs E.γ.leases
  γr.kv.lg` (M2). Why true: `NewServer` creates the lessor with guard `srvGrantGuard lg on`, and at
  `lg = true` has `leasesNoExpiry` (`%Hslg`) and `on = false`; the mode is `lessorModeIs … γr.kv.lg`.
- `applyEntryNormal.spec`/`applyEntries`/`apply` (frozen) gain the persistent `srvGrantable E` in the
  pre (from `applyAll`'s `srvSnapRO`; `srvGrantable_false` at `lg = false`). Alternative: a field of
  `isServerM` (more sites).
- `applyEntryNormal.wp_proof`: opens `srvRest`, calls `Apply` with `rs`, `T`, `grantPermRq E rq`
  (from `srvGrantable` and `rqOk E.lg`), recloses by `srvRest_applyG`, hands `grantArM` to the waiter.
  `apply`, `applyEntries`, `applyAll`, `run`: unchanged proofs but the send branch (2.14).

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
W64 (|log| − 1) ∗ ⌜2 ≤ |log| ∧ |log| + 3 ≤ 2^63⌝` (`hdrFields`: `ClusterId`, `MemberId`, `RaftTerm`,
`LeaderId` owned: `respHdrOwn`'s body). Callees (already its proof's): `mvcc.store.Rev.spec` (through
`kvOver_rev_wp`), the cluster's and raft status's getters. Glue: the proof calls `Rev` with the sole
writer's tokens `m := soleBudget log = 2^63 − 3 − |log|`; `Rev`'s post gives `log <+: log'` and
`|log'| + m + 3 ≤ 2^63`, so `|log'| ≤ |log|`, `log' = log`, `v = |log| − 1`; `kvWriter_len` gives
`2 ≤ |log|`; the struct allocation gives the fields. The `idxCert`/`certOk` of `grantHdr` come from
`Rev`'s post (now kept, not dropped with `-`). Callers (51 sites / 36 files): a stronger post; their
intro patterns drop the new conjuncts.

**2.12 The lessor contract** (trusted `lessorApplyOk`; derived `isApplyLessor`):
- `isApplyLessor le s γ P f RO RW` (signature unchanged): its Grant clause pre `… ∗ leaseGranted
  γ.leases id ∗ RW` → `… ∗ leaseGranted γ.leases id ∗ RO rs` (`∀ rs`); post error arm `+ RO rs`,
  success arm `+ ∃ t, RO (restGrantT id t rs)`, conditions as `grantIdsOk L id ttl`.
  `isApplyLessor_of_lessorInv`: over `Grant.spec` with `Rb := storeRb γ` from the RO lens
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
  `Checkpoint.spec`, `persistTo` (proved) likewise; `Revoke`'s clause (same contract) gets `Ln` back.

**2.13 `NewServer.spec`/`specM`/`specG`** (frozen; text: one row). `%Hslg` unchanged; `specM true`
takes `ρ.rd.kv.lg = false`. Proof: allocate `E.γlt` at `[]` (one half into the boot's `leasesLive`
with `leaseOwn γl [] ∅`, one into `srvRest E γr []` at `f := fun _ => 0`); `srvGrantable E` (2.9) into
`srvSnapRO`.

**2.14 The snapshot side**. Receive: unchanged, `srvGrantOpen_snap` (its body's `applyRes` now holds
the gated `srvRest`, with `∃ f`: true whatever the members' minimum TTLs, B1). Send (`applyAll`'s
`msgSnapC` branch, `SnapSendBranch.lean`): the image is cluster-wide (`imageAt`, the snapshot
certificates, `snapDirInv`). `imageAt γk bootLog i L A D`: conjunct `bkRestAt γk.c0 bootLog L D` →
`(if γk.lg then bkRestAtL γk bootLog L D else bkRestAt γk.c0 bootLog L D)` (S4), with `bkRestAtL γk
bootLog L D := ∃ f, ∀ n ∈ restBuckets, D.lookup n = (restLeasesWith f (kvLeases γk L).ids (restModel
γk.c0 bootLog L)).bk.lookup n`. `bkRestAt`, `bkRestAt_boot`, `SnapRecvFacts`, `KVModelRestore` keep
their text and proofs (the receive side at `lg = false`). The send branch at `lg = true` reads
`bkRestAtL` off `srvRest`'s `∃ f`. The S2 `sorry`s (`mergedCreate_window`, `merged_image`) keep
their role.

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
`Apply.spec` 12/6; `restAfter` 21/11, `restOut` 16/8; `srvRest` proofs unfolding it 18/8; `imageAt`
15; `kvInv` openers ≈10; `reqPropOk` 31/10; `appliedOkM` 32/16, `resPostM` 12/6, `resultIsW` 33/12;
`srvSnapRO` constructors (few; 1 def); `lessorBackend` 11/9, `lessorApplyOk` 18/9,
`lease.lessor.Grant.spec` 16/10; allocs 32/9. Not touched: `kvOwn` (288/73), `ApplyKV` (549/92),
`dispatchAnswer`/`dispatchResult`/`applyResultIs` (184), `isApplyLessor`'s signature (70/31),
`bkRestAt` (29/4), `srvKVInvs` (167). Roughly 450 edited sites, most mechanical.

**Statements that change at `lg = false` too** (S5; each new part is reached only through a grant,
which `rqOk false` excludes), with the law their `lg = false` callers use:

| statement | change at every `lg` | law for `lg = false` callers |
|---|---|---|
| `lessorApplyOk`, `lessorBackend`, `Grant`/`Checkpoint`/`Revoke`'s clause, `persistTo` | `Ln` returned | none: proofs re-done once (Revoke's user gets `Ln` back, drops it) |
| `isApplyLessor`'s Grant clause | `RO` for `RW` | none (no `lg = false` caller calls `Grant`) |
| the four `LeaseGrant.spec`s, `applierTriples`' grant entry | new triple | none (unreachable at `rqOk false`) |
| `newHeader.spec` | stronger post | none (more conjuncts; intro patterns) |
| `dispatch.spec`, `Apply.spec` | `+ grantPermRq`, `+ ltHalf`, `grantRest`, `grantRes` | `grantPermRq_of_not_grant`, `ltHalf_false`, `grantRest_not_applied` (`= r`), `grantRes_not_grant` |
| `appliedOkM`, `resPostM`, `resultIsW(On)` | `+ grantArM`/`grantAnsM` | `grantArM_not_grant` (constructors), dropped by users |
| `leasesLive` (now over `E`) | `+ ltHalf E L` | `ltHalf_false` (`True`) |
| `kvInv`'s ≈10 openers | fraction `if γk.lg then 1 else ½` | `kvInv_false`; `kv_prop_auW` splits on `γk.lg`; `kv_revLbZ_le` fraction-generic |
| `srvSnapRO`, `applyEntryNormal`/`applyEntries`/`apply` pre | `+ srvGrantable` | `srvGrantable_false` (`⊣⊢ True`) |
| `kv_lease_served`, `srvClusterBoot_alloc`, `alloc1` | take `lg` | `_false` (old post) |
| `rqOk`/shapes/`plainLogM`/`kvInv`'s plain log, `srvRest`, `imageAt`, `reqPropOk` | gated | `_false` by `rfl`/`simp` |

**Commits**, each a full build with the checks of the last section (`tcb-report --check` new only
`srvGrantOpen_open` and the drafts; every collection unchanged; `gen-init`, `gen-interface`):
1. **Pure** (new modules): 2.0's definitions and laws.
2. **Lease package** (rebuilds lease and above): `lessorBackend`'s `Ln`, `lessorApplyOk`,
   `Grant`/`Checkpoint`/`persistTo`/the revoke path returning it.
3. **Apply package and the apply thread** (one full server rebuild): `AEnv.γlt`, `ltHalf`,
   `leasesLive E`, `newHeader.spec`, `isApplyLessor`'s RO clause and derivation, the grant triple and
   the five layers, `dispatch.spec`/`Apply.spec`, `grantAnswer`/`grantRes`; server side in the same
   commit: `srvRest` gated, `srvRest_applyG`, `srvSnapRO`'s `srvGrantable`, `entryOk`/`logShape` at
   `E.lg`, `applyEntryNormal`/`applyEntries`/`apply`, `NewServer`'s allocations, `imageAt`'s gate and
   the send branch.
4. **The request path** (full server rebuild): `kvInv` (C), `reqPropOk`'s grant disjunct,
   `kv_prop_au_grant` and the refutations, `plainLogM γk.cmp γk.lg`, `kvWork`'s shapes,
   `grantArM`/`grantAnsM`, `NewServer.specM true`'s `lg = false`, `srvClusterBoot_alloc lg`.
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
- **Q7 (new). Where `srvGrantable` reaches `applyEntryNormal`.** A conjunct of its pre (and of
  `applyEntries`/`apply`, passed from `applyAll`'s `srvSnapRO`), or a field of `isServerM`.
  **Recommended: the pre** (three frozen specs, one persistent conjunct; `isServerM` has more users).
- **Q8 (new, to check in the plumbing). `newHeader`'s `log' = log`.** The argument (2.11a) uses that
  the sole writer lends `Rev` exactly `soleBudget log` tokens; if a caller lends fewer, the post weakens
  to `log <+: log'` and the answer's revision to "at least". Its present proof passes `soleBudget log`.

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
