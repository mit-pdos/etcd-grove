# Spec review: the lease-grant stage's Draft (branch `lease-grant`, `44f1b5bc7c`)

Reviewer: an independent spec reviewer, read-only (no build, no `lean-check`). Compared with `lean`
through `git diff lean...lease-grant`. Go at the pin: `/shared/etcd-goose-lean-wk` (`09669450f`).
Judged by `.claude/skills/spec/PRINCIPLES.md` and the examples `compaction-in-place.md`,
`reply-size.md`, `compact-client.md`, `lease-grpc.md`, `lease-keepalive.md`, `watch-compaction.md`.
Line numbers are at `HEAD` of `lease-grant`.

## Answers to the four questions

**(1) Is a granted ID listed by a later `LeaseLeases` on the same member, and does the chain say so?**
In Go, yes, on the same member, in every interleaving with the lessor's own goroutines, provided
nothing revokes the lease. The reasons:

- `raftRequest` returns only after the local apply thread ran `applierV3backend.LeaseGrant`
  (`apply/backend.go:83-92`), which put the lease into `leaseMap` (`lease/lessor.go:281-324`).
- `LeaseLeases` reads `s.lessor.Leases()`, which is `leaseMap` under `RLock`
  (`v3_server.go:737-749`, `lessor.go:472-478`; `checkLeaseLeases` is `nil` with auth off).
- Only `Revoke` (`lessor.go:326`) and `Recover` (`lessor.go:600`) take a lease out of `leaseMap`.
  `Checkpoint` writes only `remainingTTL`, `Demote` only sets the expiry to forever, and `Promote`
  only refreshes it.
- `Revoke` is reached through the apply of a `LeaseRevoke`. That comes from a client, or from
  `run`'s receive on `expiredC` (the expiry path).
- `Recover` is reached only from the snapshot apply.

The chain states this: `etcdLeaseGrantSpecL γl` (`client/v3/InvLeaseGrant.lean:47`) carries
`∃ i, leaseGrantedAt γl i id`. `etcdLeaseLeasesSpecL γl` (`:63`) lists every handed-in grant. Both are
at one member's lessor names `E.γ.leases` (`etcdLeaseGrantAt`, `ServedLeaseGrant.lean`). The main
thread's client has one endpoint, so the chain says exactly "same member". It is also right not to
claim more: `LeaseLeases` is a member-local, non-linearizable read, so on another member that has not
applied the grant the lease is not listed (S5).

Two things outside the chain:

- The "nothing revokes" half rests on the closed world: no client other than `Main`'s, and
  `rqOk .leaseRevoke = False`. All the examples share this. A foreign process on
  `127.0.0.1:23956` that calls `LeaseRevoke` would falsify the Go property.
- The server-side links are not yet sound statements: the open `sorry`s cannot be proved as stated
  (B1, B2).

**(2) Is `leasesNoExpiry` well placed and honestly stated?** It is honest about the clock, with two
gaps in the docstring and one placement problem.

Honest about the clock:

- Expiry is `l.expired()` against an expiry set at grant (`refresh(0)`: now + TTL), and reset only
  forward. `Promote` uses `refresh(extend)`, and with fewer than `leaseRevokeRate` leases does
  nothing else (`lessor.go:480-532`).
- `minLeaseTTL` only raises a TTL (`lessor.go:301-303`).
- `Demote` sets the expiry to forever, and a single member does not change leader.
- Checkpoints do not remove leases.

So with TTL 600, a revocation needs more than 600 s between the grant's apply and `Leases`' read.
`Leases` runs under `RequestTimeout`. The gaps:

- **Docstring gap 1 (S3).** "the run" is not the theorem's executions. `leasegrant_safe` covers every
  `n`-step execution, including steps of the server goroutines after `Main` returned. Go has no such
  steps: the process exits. The premise is used as "no slice is ever sent".
- **Docstring gap 2 (S3).** "leases the run grants" should be "leases the cluster grants". With a
  snapshot, `Recover` reloads leases another member granted.
- **Placement (S1).** The premise sits in three specs' preconditions (`srvGrantsLeases`, so
  `EtcdServer.LeaseGrant.spec`, `raftRequest.specGrant`, `kv_lease_grant_served`) and in `Main.spec`.
  Yet the one place that needs it as a hypothesis, the apply thread minting `leaseGranted`, does not
  get it (B2). It belongs on the producer (`NewServer`, gated by `lg`), carried to the apply thread.

**(3) Is any new trusted statement stronger than Go?**

- **`NewLessor`'s `mono`:** no. It is ghost state only; the history is `[(∅, ∅)]`, and the axioms
  touching the lessor in mode `true` (`Promote`, `Demote`, the loop) never change `leaseMap`.
- **`NewLessor`'s `⌜¬ leasesNoExpiry⌝` payload:** true, with gap 2 above. A slice is sent only when
  `findExpiredLeases` found an expired lease of the map (`lessor.go:640-665, 728-750`). The map holds
  only leases granted after a fresh, empty `lease` bucket (`NewLessor`'s and `Recover`'s premise
  `(r.lookup "lease").getD ∅ = ∅`).
- **`Recover`:** a new premise weakens the axiom, which is fine.
- **The wire model's `recvOwn` (`ID ↦`):** true.
  - grpc decodes into a fresh `new(LeaseGrantRequest)`.
  - The unary interceptors read no field of a `LeaseGrantRequest`: `isRPCSupportedForLearner` is a
    type switch, and `logUnaryRequestStats` takes `default` for `*LeaseGrantResponse`
    (`v3rpc/interceptor.go:47-180`).
  - The quota check reads only the type (`storage/quota.go:142`).
- **`isApplyLessor`'s exact Grant clause:** it is derived from the proved `lessor.Grant.spec`
  (`LessorDerive.lean`), not assumed, and matches `lessor.go:281-324`. But it consumes `RW` (B2).
- **The restated `lessorOk`:** its expiry payload is `False` whatever `lg`, `on` (M1). It is derived,
  not assumed.
- **`ckptEffectsOk`:** an opaque trusted premise whose own docstring says this stage must revisit it,
  and the Draft does not (S2).

**(4) Does anything give out a counted resource it did not take?** No new statement does:

- `NewLessor`'s new output is `lessorModeIs` (persistent ghost).
- `recvOwn` is a heap points-to of a fresh allocation.
- `dispatch.specGrant` returns the `E.RW` it took.
- `EtcdServer.LeaseGrant.spec` returns `srvLeadTimeReader s ∗ E.RD`, which it took.
- `idCred` is pure (`idutil/Defs.lean:281`).

The `List.replicate actualMaxReaders lessorRdOf` in `NewLessor` predates this stage: these are the
creator's slots of a lock `newLessor` makes. `kv_lease_grant_served` takes a `threadTok` for the gRPC
slot, as `kv_lease_served` does.

No Go bug found. The quota applier answering `ErrNoSpace` after a grant it made
(`apply/quota.go:54-61`) is upstream's design, as for `Put`, and is excluded by
`apply.backendUnderQuota` here. Nothing to file in `issues/`.

## Findings, by severity

### Blockers

**B1. `raftRequest.specGrant` and `dispatch.specGrant` are second specs of proved functions, and
`raftRequest.wp_grant` cannot be proved over the callees it names.**

- *Principles:* "One spec per function; special cases are instances" (hard rule: "A step that would
  start a family goes to the user first"); "Sound"; "check a reuse option has a consumer"
  (`watch-compaction.md`).
- *Where:*
  - `Proof/go_etcd_io/etcd/server/v3/etcdserver/LeaseGrant.lean:104` (`raftRequest.specGrant`).
  - `EtcdServer__raftRequest.lean:246` (`wp_grant`).
  - `Spec/.../apply/uberApplier__dispatch.lean:76` (`dispatch.specGrant`).
  - `apply/uberApplier__dispatch.lean` (`wp_grant`, new `sorry`).
- *Evidence:*
  - `raftRequest.wp_grant` takes `processInternalRaftRequestOnce.spec`, the same callee as `wp_proof`.
    That spec's precondition is `reqPropOkM … rq Qh` (no grant disjunct), and its success post is
    `resPostM`/`appliedOk`.
  - `appliedOk` (`InvProposer.lean:505`) gives `dispatchAnswer`, whose `LeaseGrant` arm the plan
    keeps `True` ("Not changed: `appliedOk`", plan D3).
  - So nothing `raftRequest` receives from the wait registry can yield `grantReplyOk … ∗
    leaseGrantedAt`: the statement is unprovable over its stated hypotheses.
  - Proving it needs a `processInternalRaftRequestOnce.specGrant`, a grant arm in the registry's
    payload, and the apply thread's `applyAll`/`applyEntryNormal` calling `dispatch.specGrant`. That
    is a family running down the request path.
  - Meanwhile `rqOkG`, `plainCoverG` and `reqPropOkWG` are defined but appear in no statement, only in
    docstrings (`Chain.lean:338`, `KVModelDefs.lean:88`, `InvRequest.lean:594`). The admission of a
    grant into the raft log and the apply is therefore not stated anywhere yet.
  - The lease-revoke stage extended `dispatch.spec` in place (`revokeClause`, `revokeRes`), not by a
    sibling.
- *Callers affected:* `EtcdServer.LeaseGrant.wp_proof` and, through it, `lessorGrantOkL_of_server`,
  `kv_lease_grant_served`, `leasegrant.Main`.
- *Restatement:* follow `compaction-in-place.md`: one spec per function, the new mode a redefinition
  in place.
  - `dispatchAnswer`'s `.leaseGrant` arm becomes `grantAnswerIs` (it needs `E.γ.leases`, so
    `dispatchAnswer` gains `E` or the lessor's name). The arm is dead at `lg = false` through `rqOk`.
  - `rqOk`'s `.leaseGrant` arm takes the cluster's `lg` (`rqOk` gains `lg`, or the arm reads it from
    the log's names) and becomes `lg = true ∧ grantKindOk rq`.
  - `reqPropOk`'s plain form admits a grant at `γk.lg`.
  - `raftRequest.spec` and `dispatch.spec` then cover grants. `EtcdServer.LeaseGrant.wp_proof` takes
    `raftRequest.spec`, and gets `grantReplyOk` from `appliedOk` by a law.
  - Prove that `lg = false` means the old statements (laws, not `rfl`).
  - If the siblings are kept, the user decides (it starts a family). The Draft must then also state
    the missing `processInternalRaftRequestOnce` and apply-thread siblings, so that `wp_grant`'s
    hypotheses can give its post.

**B2. `dispatch.specGrant` cannot be proved as stated: it has no source for `leaseGranted`, and its
frame keeps the lease bucket's state unchanged across a write to it.**

- *Principles:* "Sound"; "Read the definitions of the resources a spec takes" (`pilot-review-2.md`).
- *Where:* `Spec/.../apply/uberApplier__dispatch.lean:76-95`.
- *Evidence:*
  - **No source for `leaseGranted`.**
    - The backend's grant (`applierV3backend.LeaseGrant.spec`, `reqFacts "LeaseGrant"`,
      `Chain.lean:1155`) takes `lease.leaseGranted E.γ.leases g.id`, which is `∃ GA, lessorGuard γl GA
      ∗ □ GA id` (`InvLessor.lean:600`).
    - For the server, `GA = srvGrantGuard lg on = ⌜leasesNoExpiry ∧ lg = true ∧ on = false⌝`
      (`InvApplier.lean:479`).
    - `specGrant`'s premises give `E.authOn = false` and `lessorModeIs E.γ.leases true`, but neither
      `lg = true` nor `leasesNoExpiry`, and the mode does not imply the guard. So the arm cannot mint
      `□ GA id`.
    - Nor does anything carry `leasesNoExpiry` to the apply thread. `rqOkG`'s and `reqPropOkWG`'s
      grant disjuncts have `lg` but not it, and `NewServer` does not take it.
  - **The frame `E.RO rs`, `E.RW` unchanged.**
    - `Grant` writes the lease record (`lessor.go:311`, `l.persistTo(le.b)`). The rest model tracks
      it: `restGrant mt id ttl` exists (`apply/RestLease.lean:31`), and the revoke arm states its
      effect, `revokeResAfter … E.RO (if err = nil then restRevoke id rs else rs)`
      (`Chain.lean:1091`).
    - `specGrant`'s post `E.RO rs ∗ … ∗ E.RW` claims the bucket unchanged.
    - `isApplyLessor`'s Grant clause consumes `RW` and returns neither it nor the written bucket
      (`Contracts.lean:364-377`; `LessorDerive.lean` drops `Rb (rbSet …)` with `-`). So `E.RW` cannot
      come back through the contract.
    - The plan's D3 notes the server-side split as Prove-stage work. The *statement* should already
      carry the effect, so its callers are written against the right post.
- *Callers affected:* the apply thread's grant path (B1), hence `EtcdServer.LeaseGrant`.
- *Restatement:*
  - Add `(∀ g, rq.leaseGrant = some g → lease.leaseGranted E.γ.leases g.id)` to the precondition. The
    server's apply thread proves it from the guard, with `leasesNoExpiry` and `lg = true` from S1.
    The apply package stays ignorant of `srvGrantGuard`.
  - Return `E.RO (grantRest rq o rs)`, where `restGrant mt g.id g.ttl rs` applies exactly when
    `lessor.Grant` succeeded. That is not "when `err = nil`": the quota applier can report
    `ErrNoSpace` after a grant (`apply/quota.go:54-61`). It agrees with `err = nil` only under
    `backendUnderQuota`; say which.
  - Make `isApplyLessor`'s Grant clause return `RW` with the put stated (as `lessor.Grant.spec` does
    with `Rb (mvcc.rbSet …)`), as `revokeClause` returns `RO (restRevoke id rs)`.

### Should fix

**S1. `leasesNoExpiry` is a premise of operations that do not need it, and missing where it is
needed.**

- *Principle:* "A workload premise about a resource's later operations goes on the resource's only
  producer, carried by the resource" (`reply-size.md`); "No unneeded premise".
- *Where:*
  - `srvGrantsLeases` (`LeaseGrant.lean:38`), used by `EtcdServer.LeaseGrant.spec` (`:48` of the spec
    file), `raftRequest.specGrant`, `lessorGrantOkL_of_server` and `kv_lease_grant_served`
    (`ServedLeaseGrant.lean:54`).
  - Missing at the apply thread (B2).
- *Evidence:*
  - `LeaseGrant`'s caller, a gRPC goroutine, has nothing to do with expiry. Its post's
    `leaseGrantedAt` rests on the lessor's mode (`lessorModeIs … true`, already pinned at
    `NewServer`).
  - The only consumer of the premise as a hypothesis is the minting of `GA id` in the apply thread.
  - `run`'s dead receive needs no hypothesis: `srvGrantGuard_expired` refutes the payload by itself.
- *Restatement:*
  - Add one row to `NewServer`'s precondition, `"%Hlne" ∷ ⌜ρ.rd.kv.lg = true → lease.leasesNoExpiry⌝`
    (as `%Hslg`), carried into the apply thread's resources (`isServerApplyAll` or the guard's
    holder).
  - Drop the conjunct from `srvGrantsLeases`, which becomes `ρ.rd.kv.lg = true ∧ E.authOn = false`:
    two scope restrictions, marked as such.
  - `Main.spec` keeps `lease.leasesNoExpiry`, discharging the row. The docstrings of
    `kv_lease_grant_served`, `LeaseGrant` and the results say they are conditional on it.

**S2. `ckptEffectsOk` is not revisited, though its docstring says this stage must.**

- *Principles:* "Sound" (trusted premise); "Know what it rests on".
- *Where:* `Proof/go_etcd_io/etcd/server/v3/etcdserver/InvBoot.lean:196-206`: "Neither call is
  exercised while the server's grant guard is `False` … the lease-grant work must revisit both."
- *Evidence:*
  - With a granted lease of TTL 600 > `checkpointInterval` (300 s default), `Grant` on a primary
    lessor schedules a checkpoint when `le.cp != nil` (`lessor.go:318-321, 753-770`).
  - After 300 s the loop calls the checkpointer, which proposes `LeaseCheckpoint` through
    `raftRequest` (`server.go:394-406`). That is outside the verified request path, now live in a
    granting cluster.
  - In the example the feature gate is the default (`examples/common/common.go:96`,
    `features.LeaseCheckpoint` off), so `le.cp == nil` and no checkpoint is ever proposed.
  - The premise is opaque; its docstring is its only meaning, and it is now stale.
- *Restatement:* rewrite the docstring. It is exercised in a granting cluster with the
  `LeaseCheckpoint` feature on; the examples' configuration leaves it off (so for `leasegrant` it
  holds vacuously). Then add `ckptEffectsOk` to the list of trusted statements this stage restates,
  for the `axiom` skill's pass.

**S3. `leasesNoExpiry`'s docstring: say what "the run" and "the run grants" are in the theorem's
terms.**

- *Principles:* "Sound: a trust-boundary axiom true of the library's … behavior"; "Know the margin".
- *Where:* `Proof/go_etcd_io/etcd/server/v3/lease/LessorBackend.lean:50-61`, and `Main.spec`'s
  header.
- *Evidence:*
  - `leasegrant_adequate` (`Adequacy.lean:118-142`) quantifies over every `RealNsteps n` execution,
    including those where `Main` has returned and the server goroutines go on. Go has no such states.
  - The trusted payload (`LessorBackend.lean:135`) claims that every slice sent in any of these
    executions refutes the premise. With the premise assumed, the theorem's conclusion for post-`Main`
    states uses "nothing is ever sent", not "nothing before the run ends".
  - Through `Recover` (`runSnapLgOk`'s case, `lessor.go:600-609`), a member's map can hold leases
    another member granted.
- *Restatement:* "No lease granted in the cluster expires, by the clock the lessor's loop reads, while
  the program runs. The program's run ends when `Main` returns (Go exits); the theorem's executions
  that continue the other goroutines after that are not Go's, and the premise is read over them too.
  True of `examples/leasegrant`: the only lease is granted with TTL 600 s, and the read that must list
  it runs within `RequestTimeout` of the grant's apply (the expiry is set to at least the grant's
  apply plus the TTL, and `Promote`, `Demote` and `minLeaseTTL` only move it later,
  `lessor.go:301-303, 480-553`)." Keep the exclusions.

**S4. `runSnapLgOk` in `NewServer.spec`'s precondition puts an internal triple into a client-facing
spec.**

- *Principles:* "The spec of an API, not of an implementation"; "Local"; "Every premise has a source
  the client sees".
- *Where:* `Spec/.../NewServer.lean:263, 452, 658`; definition `InvRun.lean:443` (an exposed `def`
  over `ApplyCtx`, `isServerApplyAll`, `taEntriesAddr`, `rnAdvChan`, …).
- *Evidence:* the gating by `lg` is right: an inline `sorry` would have entered every collection.
  But the row exposes `applyAll`'s snapshot-job triple to every reader of `NewServer.spec`. Each
  example's proof carries it, `memberBoot` gained a conjunct, and its body changes whenever
  `applyAll.specSnap`'s does: a frozen spec now moves with an internal one.
- *Restatement:* keep the row, but make the obligation a name only. Either mark `runSnapLgOk`
  `@[no_expose]` (as `ownRaftPhys`), or declare `opaque leaseSnapRestoreOk : Prop` with a docstring
  and a lemma `leaseSnapRestoreOk → runSnapLgOk` inside the package. The client then sees a named
  scope restriction, as `storage.diskOk`. File the restriction in the plan as interim (done) and in
  STATUS.
  - *Uncertain:* whether `runSnapLgOk` is true. It quantifies over every `ApplyCtx`, multi-member
    clusters included. In Go the snapshot holds a superset of the member's applied leases when no
    revocation is admitted, so it is plausible. With `Recover` requiring `lessorRevocable` and an
    empty lease bucket, it is not provable from today's axioms.

**S5. The client contracts carry one member's ghost name. Say why, since the principle forbids it by
default.**

- *Principles:* "A client's certificate is the cluster's" (`compact-client.md`); "Know the margin";
  "The spec of an API, not of an implementation".
- *Where:* `client/v3/InvLeaseGrant.lean:47, 63`; `ServedLeaseGrant.lean` (`etcdLeaseGrantAt addr E`).
- *Evidence:* `leaseGrantedAt γl i id` is taken from one call's reply into a later call, at
  `γl = E.γ.leases`. Here this is forced by Go: `LeaseLeases` is a local read (`v3_server.go:737-749`,
  no read index). On a lagging member the lease is not listed, so a cluster-level certificate would
  be false.
- *Restatement:* keep it, and say it in the file header and in `etcdLeaseGrantAt`'s docstring:
  per-member because Go's listing is member-local; with several endpoints `isGrpcRpcs` would need it
  at every member, which no granting cluster gives. Optionally hide `γl` behind the address (a
  persistent `leaseGrantedOn addr id` with the law "a `Leases` at `addr` lists it"), so that `Main`'s
  proof never names `E.γ.leases`.

**S6. The `lg` siblings (`rqOkG`, `plainCoverG`, `reqPropOkWG`, and the client contracts' `…L`) are
mode-indexed copies.**

- *Principles:* "A new mode redefines the shared predicates in place, not mode-indexed copies"
  (`compaction-in-place.md`); "One spec, a gated row, not two specs" (`authinfo.md`).
- *Evidence:*
  - The first three have no consumer yet (B1). Once wired in, each needs a carrier through every
    statement that names the original.
  - `etcdLeaseGrantSpecL` beside `etcdLeaseGrantSpec`, and `etcdLeaseLeasesSpecL` beside
    `etcdLeaseLeasesSpec`, are two contracts per method by mode. `…SpecL` at `G = []` implies the
    old `etcdLeaseLeasesSpec`.
- *Restatement:* fold into B1's in-place redefinition. For the client, either keep the frozen
  contracts and derive them from the `…L` ones (laws, `G := []`, dropping the grant fact), stating
  the departure, or add the grant fact to the frozen reply as a row gated by the cluster's mode. Ask
  the user which, since the frozen contracts change.

### Minor

**M1. `lessorOk`'s expiry payload is `False` in every case; drop the noise.** `InvApplier.lean:506`:
`∃ (γc) (lg on : Bool), isChanBag … (⌜¬ N⌝ ∗ ∃ id, ⌜N ∧ lg ∧ ¬on⌝)` is equivalent to a bag of
`False`, and the existentials `lg`, `on` are chosen by the prover ("no conjunct whose reason you do
not know"). Restate as `isChanBag γc c (fun _ => iprop(False))`, with the docstring giving the
reason (the guard carries `leasesNoExpiry`, a slice refutes it). `run` then needs no
`srvGrantGuard_expired`.

**M2. `isApplyLessor`'s docstring is stale.** `Contracts.lean:357`: "the server's `AEnv.RW` … which
its apply thread does not lend (no lease request is admitted)". D3 lends it per grant. Update it
together with B2's restatement of the Grant clause.

**M3. `leaseGrantedResp` gives the supplier's mechanism, not the receiver's need.**
`LeaseGrant.lean:54`: `mvcc.certOk E.γ log ∗ ⌜sint.Z rv < log.length⌝ ∗ appliedWit ρ.rd log ∗
apply.appliedHdr log …`, so that v3rpc can derive `etcdReached rv` (`etcdReached_of_certOk`, plan
Q3). "A contract between packages states the receiver's need" (`irr-depth.md`, `lease-grpc.md`):
export `etcdReached rv` (or the KV model's reached revision) and the header's id ownership, and keep
`certOk`/`appliedWit`/the log inside. This also shrinks the spec's coupling to `mvcc`.

**M4. `EtcdServer.LeaseGrant.spec`'s ownership of `r.ID` is not returned.** Harmless today: no
interceptor reads the field after the handler (see (3)). Note the margin in the docstring: "the
request's `ID` is not given back; Go's interceptors do not read it".

**M5. `kv_lease_grant_served` restates `threadBound GF ≤ 2 ^ 30 - 1` and `receiptBound GF ≤ 2 ^ 48`.**
It copies `kv_lease_served`. The bounds principle prefers the owner's handle. Since the copy is
verbatim, leave it, but record the three new `etc/bounds-check.py` matches the plan reports in the
allow-list or the baseline, or `--check` fails in CI.

**M6. `histMono`, `leaseGrantedAt`, `lessorModeIs`: good, one gap in law coverage.**
`leaseGrantedAt_listed` needs `lessorRdInv γl`, which only the server holds. The client gets the fact
through `kv_lease_grant_served`, which is fine. A law "`leaseGrantedAt γl i id ∗ lessorLb γl j ⊢
lessorLb γl (max i j)`" (or a list form) would save `kv_lease_grant_served` from unfolding
`lessorLb` to combine the grants in `G` into one bound for `EtcdServer.LeaseLeases.spec`'s `m`.

## Per target: what is good

- **`lease.NewLessor.spec`** (`Spec/.../lease/NewLessor.lean:114`):
  - The mode is ghost only, chosen by the caller, pinned with the readers' names, and sound (see (3)).
  - The `⌜¬ leasesNoExpiry⌝` payload is justified at `lessor.go:652`.
  - Finding: S3 (wording).
- **`lease.lessor.Recover.spec`** (`lessor__Recover.lean:73`): the least change, an added premise.
  Finding: S4 (the restriction it creates).
- **`lease.lessor.ExpiredLeasesC.spec`, `lessorOk`:** derived. Finding: M1.
- **`isApplyLessor`'s Grant clause:** exact, derived from the proved `lessor.Grant.spec`, and the error
  condition matches Go. Findings: B2 (`RW` consumed, bucket write unstated), M2.
- **`pbLeaseGrantRequest`** (`client/v3/InvLease.lean:96-106`): fixes a real unsatisfiability (the
  server writes `r.ID`), follows `UserAdd`'s precedent, and is true of grpc and etcd's interceptors.
  No finding.
- **`lease.leasesNoExpiry`:** well motivated, honest about the clock. Findings: S1 (placement), S3
  (wording).
- **`lease.lessor.Grant.spec`, `Revoke.spec`, `histMono`, `leaseGrantedAt_*`:**
  - Clean vocabulary: persistent facts with agreement and listing laws, the mode inside
    `leaseGrantedAt` so the fact stands alone.
  - `histMono_snoc` is the right invariant step.
  - `Revoke`'s `lessorRevocable` is the right gate.
  - Finding: M6.
- **`EtcdServer.LeaseGrant.spec`:** the docstring's Go argument is correct (`v3_server.go:434-456`,
  the type assertion safe). Findings: S1, M3, M4. B1 and B2 block its proof.
- **`raftRequest.specGrant`, `dispatch.specGrant`, `rqOkG`/`plainCoverG`/`reqPropOkWG`/`grantAnswerIs`/`grantReplyOk`:**
  - `grantKindOk` is the right per-request condition.
  - `grantAnswerIs`'s Go reading is right: `backend.go:83-92`, the quota applier's success-to-error
    case noted.
  - Findings: B1, B2, S6.
- **`srvGrantGuard`, `srvGrantsLeases`:** auth off is a stated, filed scope restriction, and the
  guard trick keeps `run`'s receive dead without a hypothesis. Finding: S1.
- **`runSnapLgOk`:** the gating keeps the `sorry` out of other collections, which is right. Finding:
  S4.
- **`etcdLeaseGrantSpecL`/`etcdLeaseLeasesSpecL`:** they say exactly what `Main` checks; the
  hand-in list `G` with persistent facts fits `lessor.Leases.spec`'s `□ ▷ Spec () Q`. Findings: S5,
  S6.
- **`common.kv_lease_grant_served`:** the shape of `kv_lease_served`, plus one registration.
  Findings: S1, M5.
- **`leasegrant.Main.spec`, `leasegrant_safe`:**
  - The premises are named, `leasePeersOk` is explained, and `runSnapLgOk` is taken by the proof,
    not the spec.
  - Findings: S3, and S1 (the premise stays here, the sole entry point).
- **Frozen specs changed** (`_Lease_LeaseGrant_Handler.spec` to `grpcHandlerOwnOkMd`,
  `quotaLeaseServer.LeaseGrant.spec` `+ Req.recvOwn`, `LeaseServer.LeaseGrant.spec` `+
  leaseGrantReqIdOwn`):
  - All follow from the wire-model fix and the `Compact` precedent, and are true of
    `v3rpc/quota.go:79-84` and `v3rpc/lease.go:44-51`.
  - The only reads before the handler are the quota cost (type only) and the learner check (type
    only).
  - No finding.
- **`NewServer.spec`'s new rows:** `%Hslg` gets S4. `□ (⌜on = true⌝ → srvLessorNil srv)` is right:
  its only user is auth on.

## Targets ranked by need of revision

1. `apply.uberApplier.dispatch.specGrant`: B1, B2. As stated it cannot be proved: no
   `leaseGranted`, an unchanged frame over a bucket write, and `RW` consumed by the contract.
2. `EtcdServer.raftRequest.specGrant` with `rqOkG`/`plainCoverG`/`reqPropOkWG`: B1, S6. A family
   whose stated callees cannot give its post; the admission vocabulary has no consumer.
3. `isApplyLessor`'s Grant clause: B2, M2. It must return `RW` with the put.
4. `srvGrantsLeases`, and with it `EtcdServer.LeaseGrant.spec`, `lessorGrantOkL_of_server`,
   `kv_lease_grant_served`: S1, M3, M4, M5.
5. `ckptEffectsOk`: S2. A stale trusted premise this stage makes live.
6. `lease.leasesNoExpiry` and `NewLessor`'s payload: S3 (wording only).
7. `runSnapLgOk` in `NewServer.spec`: S4.
8. `etcdLeaseGrantSpecL`/`etcdLeaseLeasesSpecL`: S5, S6.
9. `lessorOk`, `lease.lessor.ExpiredLeasesC.spec`: M1.
10. `histMono`/`leaseGrantedAt_*`, `lessor.Grant.spec`, `lessor.Revoke.spec`, `lessor.Recover.spec`:
    M6 only.
11. The wire model and the three frozen handler specs: none.
12. `leasegrant.Main.spec`, `leasegrant_safe`: S3's wording only.
