# The lease-grant stage's lessor statements (axiom review, 2026-11-02)

**Reviewed** (branch `lease-grant` at `6d950135c2`, merged into `axiom/lessor-apply-ok`; plan
`notes/lease-grant-plan.md`, "Draft", "### Trusted and frozen statements changed", §2.12-2.15 and
"Freeze list"), one library, the lessor, plus the grant's wire model:

1. `lease.NewLessor.spec` (axiom `lease.NewLessor.wp_proof`,
   `Spec/go_etcd_io/etcd/server/v3/lease/NewLessor.lean`): the new `mono : Bool` and post
   `lessorModeIs γl mono`; the monotone history it promises in that mode (`histMono` in
   `lessorRdBody`, `InvLessor.lean:301,313`); the expiry payload `lessorExpiredC lp GA`
   (`LessorBackend.lean:143`): `⌜¬ leasesNoExpiry⌝ ∗ ∃ id, GA id`.
2. `lease.lessor.Recover.spec` (axiom): the new premise `lessorRevocable γl`.
3. `lease.leasesNoExpiry` (`LessorBackend.lean:71`, `opaque`, a deployment premise), reviewed as
   `leasePeersOk` was (`lease-ttl-id.md`): can a program meeting its docstring see a lease expire
   or leave the lessor?
4. `ckptEffectsOk` (`etcdserver/InvBoot.lean:214`, `opaque`): its docstring for a granting cluster.
5. The wire model `pbLeaseGrantRequest` (`client/v3/InvLease.lean:98`): `recv := TTL ↦□ m.1`,
   `recvOwn := ID ↦ m.2`.

Not redone: `lessorApplyOk` (`lessor-apply-ok.md`, survives; its findings used below: `le.b` read
once under `le.mu`, `Recover` the only other writer). Go at the etcd pin
(`/shared/etcd-goose-lean-wk`, `server/lease/{lessor,lease}.go`, `server/etcdserver/{server,
v3_server}.go`, `server/etcdserver/api/v3rpc/{lease,quota,interceptor}.go`,
`server/storage/quota.go`, `server/features/etcd_features.go`), `GOTOOLCHAIN=go1.27.3`.

## Verdicts

| # | statement | verdict |
|---|---|---|
| 1 | `NewLessor` (mode, `histMono`, expiry payload) | **survives** |
| 2 | `Recover`'s `lessorRevocable` | **survives** (and is needed: without it the axiom is false in the monotone mode) |
| 3 | `leasesNoExpiry` | **refuted as documented** (Go side shown, Lean proof not built): the docstring scopes it to "the cluster"; `NewLessor`'s payload uses it for every lessor of the program. Wording fix proposed. Its claims about the example hold, with two small inaccuracies |
| 4 | `ckptEffectsOk` (docstring) | **survives** |
| 5 | `pbLeaseGrantRequest` | **survives** |

## 1. `NewLessor`: the mode and the expiry payload

Claims: (a) the history starts at `[(∅, ∅)]`, monotone trivially; (b) in mode `true` the lessor's
history stays monotone: no id leaves the lease map; (c) one mode per lessor; (d) a slice sent on
`expiredC` refutes `leasesNoExpiry` and has a lease with `GA` of its id.

| # | attack | result |
|---|---|---|
| 1.1 | **A Go path that removes a lease without `Revoke`/`Recover`** (which take `lessorRevocable`). | `grep leaseMap lessor.go`: removals only at `:355` (`Revoke`, `delete`) and `:606` (`Recover`, a fresh map). `Grant` adds only if absent (`:297`); `Promote`/`Demote`/`Renew`/`Checkpoint`/`Attach`/`Detach`/`Lookup`/`Leases` and `runLoop` (`revokeExpiredLeases`, `findExpiredLeases`, `expireExists`, `checkpointScheduledLeases`) read the map or change a lease's expiry, never the map. `TestExpiryOnlyLater`: 2000 leases, three Demote/Promote rounds and a `Renew`, primary and not: none removed. |
| 1.2 | **The axioms that run under `lessorInv` and return `True`** (`Promote`, `Demote`, `Renew`, `scheduleCheckpointIfNeeded`, and `runLoop` inside `NewLessor`): their realisation must now keep `histMono` too. | None of them removes a lease (1.1), so the history appended by the proved specs alone stays monotone (`histMono_snoc`). |
| 1.3 | **Both modes of one lessor**: `lessorModeIs γl true` and `lessorRevocable γl`, then `Revoke`. | `lessorModeIs` is `lessorPinR γl γr ∗ ⌜γr.2.2 = mono⌝`, and `lessorPinR_agree` (proved) pins `γr` per `γl`: `lessorModeIs_agree`. `γl` is existential in the post, next to the exclusive `leaseOwn γl [] ∅`. |
| 1.4 | **Revocations reached anyway in a monotone server**: the server's expiry path (`run` → `LeaseRevoke` → apply), a client `Revoke`, `leasehttp`. | The apply's `revokeClause` takes `lessorRevocable` and `rqOk .leaseRevoke = False`; the expiry path's payload is `False` under `srvGrantGuard := ⌜leasesNoExpiry ∧ …⌝` (`srvGrantGuard_expired`). No other caller of `lessor.Revoke` in the server. |
| 1.5 | **The payload** `¬leasesNoExpiry`: a slice sent without an expired lease. | `revokeExpiredLeases` sends only `len(ls) != 0` (`:652`), `ls` from `findExpiredLeases`, which appends only `l.expired()` (`Remaining() <= 0`, `lease.go:51`) of a lease of the map (`expireExists`, `:706`). A lease of the map was granted or reloaded by `Recover`/`initAndRecover`, which the premise's docstring covers; `NewLessor`'s pre has an empty lease bucket. `expiredC` is never closed (`Stop` closes `stopC`/`doneC`), so a receive is a sent slice. A non-primary lessor sends nothing. True, modulo the premise's scope (3). |

## 2. `Recover`'s `lessorRevocable`

A premise added to an axiom only weakens it. It is also **necessary**: Go's `Recover` replaces the
map (`lessor.go:606`) and reloads the new backend's lease bucket, empty by the spec's premise, so a
lessor holding a lease loses it. In the monotone mode a program could take `leaseGrantedAt γl i id`
from a `Grant`, `Recover`, then `Leases()` (proved): `leaseGrantedAt_listed` says `id` is listed, Go
lists nothing. The premise excludes it. Not part of this stage: the row's earlier frame finding
(`rdOwn` not taken nor returned, `notes/audit.md`) is still open.

## 3. `leasesNoExpiry`

Docstring: "No lease the cluster grants expires while the program runs ... no lease granted in the
cluster (by this member, or by another and reloaded here from a snapshot by `Recover`) expires".
Used: in `lessorExpiredC`'s payload, which `NewLessor` gives for **every** lessor, and in
`srvGrantGuard`.

| # | attack | result |
|---|---|---|
| 3.1 | **Expiry shortened**: the minimum TTL, `Grant` on a non-primary lessor, `Promote`'s refresh and its overlap adjustment, `Demote`, `Renew`. | `minLeaseTTL` only raises `l.ttl` (`:301-303`); a non-primary `Grant` sets `forever` (`Remaining` = `MaxInt64`); `Promote` refreshes from now with `extend ≥ 0`, its adjustment adds a positive delay (by the loop's invariant `remaining - baseWindow ≤ previous delay < expires/target`); `Demote` sets `forever`; `Renew` refreshes from now. `TestExpiryOnlyLater` (with the adjustment: 2000 leases, rate 1000): every expiry ≥ TTL from the last refresh. |
| 3.2 | **Checkpoints** (`remainingTTL`, used by `Promote`'s refresh). | Only with the `LeaseCheckpoint` feature on (default off, `features/etcd_features.go:104`); then `remainingTTL` is a ceiling of the leader's remaining time. Not exercised by the example. |
| 3.3 | **A leader change** (Promote/Demote). | Single member: none after the first election; in general 3.1. |
| 3.4 | **Other removals**: client revoke, snapshot. | Outside the premise (it is about expiry); excluded by the workload (`rqOk .leaseRevoke = False`) and `srvGrantOpen`/`lessorRevocable` (2). |
| 3.5 | **The example's timing**: "the read that must list it runs within `RequestTimeout` of the grant's apply". | Slightly wrong: the apply happens inside `Grant`'s call (≤ 5 s), the lessor's read inside `Leases`' (≤ 5 s), so within **two** `RequestTimeout`s (10 s, plus Main's few statements between). Far below 600 s either way. |
| 3.6 | **Scope: a lessor outside "the cluster".** `NewLessor`'s payload `¬leasesNoExpiry` holds for every lessor the program creates, but the docstring speaks of the leases "the cluster" grants. A program with a lessor in no cluster (or two clusters, one granting short leases) meets the docstring's text and still has a lease expire. | **Falls (as documented).** `TestStandaloneExpiry`: `NewLessor` on a fresh backend, `Promote(0)`, `Grant(1, 1)`; `ExpiredLeasesC()` delivers lease 1 after 1.00 s. A `Main` that panics on that receive gets, under `leasesNoExpiry`, a no-panic proof from `NewLessor`'s axiom: the receive's payload `¬leasesNoExpiry` contradicts the hypothesis (`isChanBag_iff`, as `run`'s receives use it). **Lean proof not built**: the cost is the setup (a standalone real backend `d : KBReal` with `leaseParams`, `rbPart`, `wbTok`, through `backend.New`; no example builds a lessor outside `NewServer`), not the argument. |

**Proposed restatement (docstring only; not applied):** "No lease of any lessor the program
creates (`NewLessor`, in whatever cluster or none; a lease granted, or reloaded by `Recover`)
expires, by the clock its expiry loop reads, while the program runs." With the two corrections:
"within two `RequestTimeout`s of the grant's apply", and `Renew` (refresh from now) and checkpoints
(feature off) among the moves. The statement (an opaque `Prop`) is unchanged; the theorems that take
it (`leasegrant_safe`, `leasegrant_adequate`) are true of `examples/etcd/leasegrant` under either
wording, since it creates one lessor. (Parametrising the premise by the lessor, `leasesNoExpiry
lp`, would make the scope checkable, but `srvGrantGuard`'s and `NewServer`'s row would then name
the lessor before it exists: not worth it.)

## 4. `ckptEffectsOk`

Docstring claims: exercised only with a lease and the feature on; with it off, nothing is proposed.

- The server installs the checkpointer only if `features.LeaseCheckpoint` (`server.go:395-407`),
  default `false` (`etcd_features.go:104`); the examples pass the default gate
  (`examples/lib/etcdstart/common.go:96`). With `le.cp == nil`: `scheduleCheckpointIfNeeded` returns at
  once, so the checkpoint heap stays empty and `checkpointScheduledLeases` finds no due checkpoint
  and never calls `le.cp`; `Renew`'s `clearRemainingTTL` needs `le.cp != nil` (`:412`). Vacuous for
  `leasegrant`. (A non-empty `cps` with `le.cp == nil` would be a nil call; unreachable, since only
  `scheduleCheckpointIfNeeded` pushes and it returns first.)
- With the feature on and a lease: `Grant` on a primary schedules (`:318-321`), the loop proposes
  `LeaseCheckpoint` through `raftRequest`: the premise has content there, as the docstring says.
  `LeaseCheckpointPersist` only changes the apply side.
- The premise is opaque with no law: nothing is derived from it but through `NewLessor`'s
  precondition. **Survives**; same scope remark as 3.6 (it names "the server's checkpointer"), but
  a program's own checkpointer goes through `lessorCkptOk`, not this premise.

## 5. `pbLeaseGrantRequest`

Claims: once decoded on the server, `TTL` is never written (`↦□`), the handler alone owns `ID`.

- The only write to the request in the server path is `r.ID = …` while `r.ID == 0`
  (`v3_server.go:436-439`), in the handler's goroutine. `quotaLeaseServer.LeaseGrant` reads nothing
  of it (`storage/quota.go:142`: a constant cost); `LeaseServer.LeaseGrant` passes it on;
  `raftRequest` marshals it synchronously and keeps no pointer (the proposal is bytes).
- Interceptors: `newUnaryInterceptor` does not read the request's fields; `logUnaryRequestStats`
  reads only Range/Put/Txn requests (`interceptor.go:112-170`), a `LeaseGrantRequest` takes the
  `default` arm (`-1`). So M4's "`r.ID` not given back; Go's interceptors do not read it" holds.
- The decoded message is fresh per call (grpc's codec), so `recvOwn` is given once; the client's
  `send` owns its own `req` (`clientv3` sends `ID: 0`).
- Protobuf's `sizeCache` writes during marshalling are atomic and covered by the `proto` axioms'
  own reviews (`marshalirr-*.md`), not by this model.
**Survives.**

## Not tried

A Lean proof of 3.6's program (setup cost, above); `Promote`/`Demote`/`Renew`'s own triples beyond
the mode (they were reviewed in `notes/audit.md`); multi-member clusters (out of the stage).

## Go checks

`examples/axiomcx/leasegrantlessor/leasegrantlessor_test.go` (tests only, no Goose project), at
`GOTOOLCHAIN=go1.27.3` and the examples' etcd pin:

```
=== RUN   TestStandaloneExpiry
    leasegrantlessor_test.go:35: received 1 expired lease(s), id 1: a program would panic here
--- PASS: TestStandaloneExpiry (1.00s)
=== RUN   TestExpiryOnlyLater
    leasegrantlessor_test.go:84: 2000 leases, Demote/Promote x3 and Renew, primary and not: every expiry >= TTL from now, none removed
--- PASS: TestExpiryOnlyLater (0.03s)
```
