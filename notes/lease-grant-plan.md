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
grant's specs (D4-D5) and the example's theorem (statements, `sorry`).

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

### D2. The lessor's monotone mode (done, proved but `run_job_snap_lg`)

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
  snapshot job splits on `lg`: **`run_job_snap_lg` (new `sorry`)**, the snapshot job in a cluster
  that grants leases (an interim restriction like `run_job_snap_cmp`; a single member is never sent
  a snapshot).

### D3. The grant through the request path and the apply thread (not drafted in code)

Not wired: admitting the grant changes the shared apply path (`rqOk`, the dispatch arms,
`reqPropOkW`, `plainCover`), which every server result rebuilds and re-proves, and
`snapRecv_image`'s `hlease` (the image's lease bucket empty) stops holding. What the Prove stage
changes: `plainCover`/`reqPropOkW` admit `{LeaseGrant: r}` when `γk.lg = true` (with
`leasesNoExpiry`, `r.ID ≠ 0`); `rqOk .leaseGrant` the same; `isApplyLessor`'s Grant clause exact
(`L ++ [id]`) and carrying `Grant.spec`'s `leaseLiveFrom`; the apply thread lends the lease bucket's
`AEnv.RW`; the reply (`appliedOk`) carries `leaseGrantedAt E.γ.leases i id`; `hlease` replaced by
"the lease bucket is the grants'" or kept with the snapshot job's `lg = false`. The KV model's
lease table stays untied (S1 (a)).

### D4. `EtcdServer.LeaseGrant` (statement, `sorry`)

- `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__LeaseGrant.lean`, vocabulary
  `LeaseGrant.lean` (`srvGrantsLeases E ρ := ρ.rd.kv.lg ∧ E.authOn = false ∧ leasesNoExpiry`,
  `leaseGrantReqOwn r ttl id` with `ID` owned, `leaseGrantedResp`: id `≠ 0`, `TTL`, `Error`, the
  header at the applied log with a revision of it, `leaseGrantedAt E.γ.leases i id`). Why true of
  Go (`v3_server.go:434-456`): the loop writes `Next() & (2^63-1)` while `r.ID == 0`;
  `requireAuthInfo` is `nil` with auth off; `raftRequest` returns the apply's `*LeaseGrantResponse`.
  **`EtcdServer.LeaseGrant.wp_proof` (new `sorry`).**
- `v3rpc.lessorGrantOkL` (`api/v3rpc/InvLeaseGrant.lean`), the sibling of `raftLessor`'s grant
  conjunct, and **`v3rpc.lessorGrantOkL_of_server` (new `sorry`)**.
- Found: `lessorGrantOk`'s `leaseGrantReqIs` and the wire model `pbLeaseGrantRequest.recv` have the
  request's `ID` read-only, but `EtcdServer.LeaseGrant` writes it when it is `0` (the client always
  sends `0`): `raftLessor` is unsatisfiable by the Go server as stated. Not changed (it is the
  trusted wire model): the Prove stage moves `ID` to `recvOwn` (as `UserAdd`'s password).

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

### Trusted and frozen statements changed

`lease.NewLessor.spec` (axiom: `mono`, `lessorModeIs`, the expiry payload through
`lessorExpiredC`); `lease.lessor.Recover.spec` (axiom: `lessorRevocable`);
`lease.lessor.ExpiredLeasesC.spec`, `lease.lessor.Revoke.spec`, `lease.lessor.Grant.spec` (proved
specs); `lessorOk`'s `ExpiredLeasesC` clause and `srvGrantGuard`; `NewServer.specM`/`specG`'s
`srvLessorNil`; `applyAll.specSnap` (`lg = false`), `applySnapshot.specSnap` (`lessorRevocable`);
`apply.revokeClause`, `revokeRes`, `revokeResAfter`. The client contracts are not changed (siblings).

### Checks

`lake build` passes; `etc/gen-init.py --check` and `etc/gen-interface.py --check` (backend, raft)
pass; `etc/bounds-check.py --check` reports the example's three new matches (`spec-receipt` 2,
`spec-thread` 1 in `examples/leasegrant`: `Main.spec`'s bounds, as `leasekv`'s), not recorded;
`etc/tcb-report.py --check` reports two new `sorry`s in the trust base, `run_job_snap_lg` (every
result that rests on `run`, as `run_job_snap_cmp`) and `leasegrant.Main.wp_proof` (the example's);
the other three (`EtcdServer.LeaseGrant.wp_proof`, `v3rpc.lessorGrantOkL_of_server`,
`common.kv_lease_grant_served`) are reached by no root yet (not linked). Baseline not updated.
