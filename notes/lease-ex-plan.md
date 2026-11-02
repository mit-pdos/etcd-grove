# The closed lease client example (2026-11-02; branch `lease-ex`)

The stage after `notes/lease-src-plan.md`: a Go program using etcd's client lease API against a
member started in-process, with a closed theorem (as `watchkv`'s `watch_safe`) that it does not
panic. Lean-first (no Rocq counterpart).

## Scope (2026-11-02; the user's choices)

- **State-independent reads** (revised from "reads on an empty lessor", which needs a new
  invariant that the lessor's history stays empty). `Main` starts a member, serves it, connects a
  client and checks what holds whatever the lessor holds: `cli.Leases(ctx)` lists no lease twice
  (`leaseIdsAt`'s `Nodup`), and `cli.TimeToLive(ctx, id)` answers about `id` (the reply's `ID`);
  it panics otherwise. The second check needs `leaseTTLOut`'s found arm to state the ID (today
  only the not-found arm does), down to the trust-boundary `leaseTimeToLive`: a trusted change for
  Freeze. It is true on every path (D3: the follower's `leasehttp.TimeToLiveHTTP` checks the
  leader's reply against the asked ID), so the check needs no assumption about the cluster. Grants are a later stage.
- **F4, the run's thread token** (the lease-src review): a lease read takes a thread token (the
  lessor's and each lease's reader slots are thread pools). First done by restating `grpc.serve`
  (D1, the user's choice "in grpcHandlerOk"), which turned out unsound and was reverted; now the
  program forks the token's goroutine ("The run's thread token" below, the user's choice).
- **Auth off**, as `watchkv`.

## What is missing (the survey)

Server side:
1. The wire models of the two reads: `pbLeaseTimeToLiveRequest`/`Response`,
   `pbLeaseLeasesRequest`/`Response` (as the client's `pbLeaseGrantRequest`, `InvLease.lean`).
2. The served specs a client may assume (`GrpcSpec`s), and the handler meets
   (`grpcHandlerOk` of `*quotaLeaseServer`'s promoted `LeaseTimeToLive`/`LeaseLeases`), from
   `LeaseServer.LeaseTimeToLive`/`LeaseLeases`' specs and `raftLeaseRead_server`.
3. F4: "The run's thread token" below.
4. `examples/common`'s `Serve`: the lease methods' registrations into `isGrpcRpcs` (`v3rpc.Server`'s
   `leaseRegs`, from lease-src).

Client side:
5. Translation: `lessor.TimeToLive`, `lessor.Leases`, `toLeaseTimeToLiveRequest`,
   `retryLeaseClient.LeaseTimeToLive`/`LeaseLeases` (`client/v3/lease.go:246-272`,
   `retry.go:142-148`; not in `Code/go_etcd_io/etcd/client/v3.toml`), and their specs (as
   `lessor.Grant.spec`'s: over `isGrpcRpcs addr "/etcdserverpb.Lease/LeaseTimeToLive" Spec`).

The example:
6. `examples/leasekv` (Go, a test), its Goose project, `Init.lean`, `Main`'s proof, the adequacy
   theorem.

## Stages

Draft → Review (an independent spec reviewer) → Test (the Go test) → Probe → Freeze (the user) →
Prove.

## Draft (2026-11-02)

**D1. F4** (`InvGrpc.lean`): the axiom `grpc.serve` restated, a run's slot `S ∗ threadTok`.
**Unsound, reverted** (2026-11-02, after the review): the axiom gave each run a token no caller
gave; tokens are bounded (`threadToks threadBound ⊢ False`) and grpc's goroutines are outside the
threads adequacy counts, so a program with a blocking gRPC service of its own could collect
`threadBound` of them. Replaced by "The run's thread token".

**D2. The wire** (`client/v3/InvLeaseRead.lean`): `pbLeaseTimeToLiveRequest` (`(ID, Keys)`; the
server's decoded copy read-only as a whole, which `LeaseServer.LeaseTimeToLive` takes),
`pbLeaseTimeToLiveResponse` (`LeaseTTLRespM`: header, `ID`, `TTL`, `GrantedTTL`; the `Keys` slice a
field, its contents not modelled), `pbLeaseLeasesRequest` (nothing), `pbLeaseLeasesResponse`
(`LeaseLeasesRespM`: header, the IDs in order); etcd's specs `etcdLeaseTTLSpec` (the reply's ID is the
asked one) and `etcdLeaseLeasesSpec` (no ID twice); the options (`leaseOptSpec`, `leaseOptsAt`,
`leaseKeysFold`, as the KV's `optSpec`).

**D3. The server's answer about the asked lease** (trusted and frozen statements): `⌜w.ID' = v.ID'⌝`
added to the success arms of the trust-boundary `EtcdServer.leaseTimeToLive.spec` (the leader's
literal has `ID: r.ID`; a follower's `leasehttp.TimeToLiveHTTP` returns only a reply whose ID is the
asked one, `lease: TTL id mismatch` otherwise, `http.go:274`), `EtcdServer.LeaseTimeToLive.spec`,
`ttlAns` and `leaseTTLOut` (proofs updated).

**D4. Served** (`client/v3/LeaseReadServed.lean`, `examples/common/ServedLease.lean`): the
handler meets (`etcd_leaseTTLHandlerOk`, `etcd_leaseLeasesHandlerOk`, at the contract's slot with
the lower bounds), the generated handlers' (`etcd_leaseTTLMethodOk`, ...), the promotions through
`quotaLeaseServer` (`QuotaLeaseLemmas.lean`), `etcdLeaseReadAt addr`, and `common.kv_lease_served`
(`kv_served` with the lease reads, under `threadBound GF ≤ 2 ^ 30 - 1`). The examples' `memberBuilt`
and `memberUp` carry `srvLeaseRd s E` (`NewServer`'s `srvLessorRd`, `lessorRdPool`), `grpcUp` the
Lease service `v3rpc.Server` registered (`grpcLeaseUp`).

**D5. The client** (translated: `lessor.TimeToLive`, `lessor.Leases`, `LeaseOp.applyOpts`,
`toLeaseTimeToLiveRequest`, the retry lease client's and the stub's two reads, the getters): specs
as `lessor.Grant`'s; `lessor.TimeToLive` over the options' `Keys` (`leaseKeysFold gs false`);
`lessor.Leases`' result a fresh `[]LeaseStatus` of the reply's IDs. Linked in the client's `Link`.

**D6. The example**: project `leasekv` (`etc/goose.py`, `etc/gen-init.py`), `Main` returns nothing
(as putget's; each read in a context with the request timeout), `leasekv.Main.spec` (putget's
premises at leasekv's addresses), `leasekv_Main`, `leasekv_safe` (`Adequacy.lean`, as putget's).

**Left `sorry` for Prove**: the handler and method meets, `kv_lease_served`, the client's
`applyOpts`, `toLeaseTimeToLiveRequest`, `lessor.TimeToLive`, `lessor.Leases`, `Main`.

**Bounds** (for Freeze): `etc/bounds-check.py`'s stock count in `examples/common` goes 23 → 29, all
six from `kv_lease_served`'s statement repeating `kv_served`'s slot premises (the same stocks,
counted twice). Prove should factor `kv_lease_served` through a `kv_served` generalized over extra
methods, with the slots in one definition, which brings the count back; else the baseline moves.

## The run's thread token (2026-11-02, the user's choice)

A lease read's run takes a `threadTok` (the lessor's reader pool, and each lease's two lock pools,
made per lease at `Grant`). The only sound tokens are those of goroutines the modelled program
forks. Rejected:
- an axiom giving it (D1: unbounded tokens);
- the client lending its own to the run: a call can time out while its run goes on, so a token
  back to the client on an error is held twice, and one back only with the reply breaks retries;
- stocks of reader slots set aside for grpc's runs: needed in every lease's two pools, a rework of
  the lessor's model and `Grant`.

Chosen: `leasekv`'s `Main` runs `go holdToken()` (sleeps forever, touches no lock) before `Serve`;
`wp_fork_tok_self` gives `Main` a token, which goes into the one gRPC slot (`S := slots ∗
threadTok`, `kv_lease_served`'s `threadTok`). Sound: the token is a real goroutine's, and that
goroutine never reads a lock, so the grpc goroutine using its token is never a reader too many; a
timed-out call's run keeps the slot until it ends. No trusted change. `holdToken.spec` (post
`False`) is proved.

## Test (2026-11-02)

`examples/leasekv/leasekv_cluster_test.go`: three members whose peer listeners serve the raft and
lease handlers (as etcd's embed), 12 leases granted through every member (one with a key), then
from every member `TimeToLive` of each and of an absent ID, with and without keys, and `Leases`.
Passes (3 of 3 runs): every reply's `ID` the asked one, on both paths (26 answers from the leader,
52 from followers through `leasehttp.TimeToLiveHTTP`); every listing without a repeat, all 12.

Found on the way: `examples/common`'s members serve only the raft handler on their peer
listeners, so a follower's `TimeToLive` gets the leader's 404 and answers "not found" (TTL -1, the
asked ID) for a lease that exists. Main's checks and the specs are unaffected (nothing is stated of
found or not-found); the trust-boundary `leaseTimeToLive`'s docstring stated its cluster assumption
as "the lease handler serves the leader's peer URLs", false in the examples; restated to what the
triple needs (no 200 without a response; a 404 is an allowed error).

## Freeze list (frozen by the user, 2026-11-02)

- Trusted: `EtcdServer.leaseTimeToLive.spec`'s `⌜w.ID' = v.ID'⌝` (D3). The `axiom` skill
  (`notes/axiom-review/lease-ttl-id.md`): the ID survives; the axiom as it stood since lease-grpc was
  refuted (its cluster assumption only prose), now the premise `leasePeersOk` (the user's (A)),
  threaded to `leasekv_safe`'s hypotheses. Collections resting on it: `server.txt`, `leasekv.txt`.
  `notes/decisions.md`, "The closed lease example".
- Frozen specs changed: `EtcdServer.LeaseTimeToLive.spec`, `ttlAns`, `leaseTTLOut` (D3);
  `memberBuilt`/`memberUp`/`grpcUp` gain conjuncts (the review's locality finding: nine `Main`
  proofs' patterns changed).
- New `sorry`s: the handler and method meets, `kv_lease_served`, `LeaseOp.applyOpts`,
  `toLeaseTimeToLiveRequest`, `lessor.TimeToLive`, `lessor.Leases`, `leasekv.Main`.
- Bounds (`etc/bounds-check.py --check`, 399 against 390): the stock count in `examples/common`
  23 → 29 (above); `examples/leasekv` new, `spec-thread 1` and `spec-receipt 2`, `Main.spec`'s
  `threadBound GF ≤ 2 ^ 28` and receipt bounds, as every example's (putget's baseline entries).
- tcb: `etc/tcb-collections/leasekv.txt` (593 entries; its `sorry`s the five above that `Main`
  reaches, plus the four the server's collections already carry).
- The Go program: `Main` forks `holdToken` ("The run's thread token").

## Probe (2026-11-02)

- Easy: `LeaseOp.applyOpts` (the KV's `Op.applyOpts` proof adapted, `foldl_apply_take_succ`) and
  `toLeaseTimeToLiveRequest` (one call): about 10 minutes with the build loop; no spec problem.
- Hard: `etcd_leaseTTLHandlerOk`, the server meet the example rests on (the request's wire model
  into `LeaseServer.LeaseTimeToLive.spec` at the contract's slot; its `leaseTTLOut` into the client's
  `leaseTTLRespMsg`, the response split into its fields and persisted, `ID` the asked one through
  D3): proved on the first build, no spec problem. The review's findings were the ones that mattered.

## Prove (2026-11-02)

- `leasekv.Main.wp_proof` proved (no spec change): putget's start; `go holdToken()` by
  `wp_fork_tok_self` (`holdToken.spec`'s `False` discharges the forked thread's post), its token into
  `common.kv_lease_served`'s slot (used as stated); `cli.Lease` from `isNewClient`'s
  `lessorAt` (its `lessorRemoteAt`), the interface call resolved by `wp_auto`; `Leases` with
  `Q m := ⌜m.ids.Nodup⌝`, the double loop over the persisted slice (each element's `ID` field through
  the generated `LeaseStatus_access_load_ID`, which `wp_auto` does not find through a
  `sliceIndexRef`; the equal-ID branch refuted by `List.Nodup.eq_of_getElem?_eq`); `TimeToLive(7)`
  with `Q m := ⌜m.id = 7⌝`, no options (`leaseOptsAt slice.nil []`). `etc/tcb-collections/leasekv.txt`:
  its `sorry` line dropped (by hand, without a run of the report).
- `common.kv_lease_served` proved (branch `lease-ex-served`): Proved, statement as frozen but for the stocks: `kv_served`'s six stock premises are written once,
in `common.kvServeStocks` (an `abbrev`), which both statements use (`iframe` does not see
through it: the five `Main`s calling `kv_served` unfold it before framing, one line each); `examples/common`'s stock count is back to 23. The KV path generalized
over extra methods: `client.etcd_kv_served_with`/`etcd_kv_started_with` (the methods `ms` served by
the same `grpc.serve`, at a slot `S` holding `etcdGrpcSlot` and giving it back, through
`grpcMethodOkMd_slot`, moved there from `ServedOn.lean`); `etcd_kv_served`/`etcd_kv_started` their corollaries, statements unchanged.
The lease reads at the slot `etcdGrpcSlot s E γr ∗ threadTok`: `client.etcd_leaseReadMethodsOk`
(`LeaseReadServed.lean`). The lower bounds `0`: the lessor's from `lessorLb_get` (its read
invariant from `srvLeaseRd`'s `lessorInv`) and `lessorLb_le`, the auth store's `authPubLbM_zero`.
