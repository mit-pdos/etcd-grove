# N9b: the lease workloads of `etcd_safe` (plan, 2026-11-25)

#50's work package N9b (the lead's plan, 2026-11-24T22:16:03Z; our claim 7161464198): the leaseRead,
leaseCatchup and leaseExpiry workloads of the multi-machine `etcd_safe` (`examples/etcd/dist/client/lease.go`:
`RunLeaseRead`/`leaseReadCheck`, `RunLeaseCatchup`/`leaseGrant`/`leaseList`/`listed`, `RunLeaseExpiry`/`gone`),
proved by reusing the single-process lease proofs (leaseN, leasecatchup, leaseexpiryN). Branch `etcd-safe-n9b`,
base the integration line `etcd-safe-main-r3/2026-11-25` @ `5a1c41d945`. Read at that base.

**Conclusion: blocked on N2 (I-1).** The translation is done; what is missing is any statement of a lease call
across machines. §6 gives the smallest unblocking step. No Lean was written.

## 1. Translation: done

`dist/client` is translated on this base (D2's translation, project `putget-dist`, packages `./putget`,
`./deployment`, `./enc`, `./kvremote`, `./server`, `./client`; `Code/.../examples/etcd/dist/client.lean`, 6511
lines). All of N9b's functions are in it: `leaseGrant`, `leaseList`, `listed`, `leaseReadCheck`, `RunLeaseRead`,
`RunLeaseCatchup`, `gone`, `RunLeaseExpiry`, and the constants `leaseReadID`, `maxLeaseTTL`. The package has
its `Base` (`isPkgInit` `True`), `Init`/`InitLinked` and `PkgTable` (`Proof/.../etcd/dist/client/`). Nothing
to translate; §11's "D2 translation: not started" row is out of date for `client`.

## 2. No `remote` instance: the lease workloads have no client machine

D8 kept the single-client workloads on one machine: `deployment.NodeCount` is `0` for every kind but kv,
watch, cache and auth, and `nodes.go` says so ("the single-client workloads (compact, putget, durable, the
lease workloads, authLease) … have no client machine"). Each lease workload runs on its orchestrator machine
(`clientProg d j` → `client.MainDeployment` → `MainReady` → `RunLease*`) and talks to the members directly
through clientv3 over gRPC. So the "instance over `remote`" of the brief is, for these three, the
orchestrator machine's own program: no `Report`/`Do` call, no codec, no `RSvc`. What N7 (the dispatch) needs
from N9b is one triple per workload, `RunLeaseRead.spec`, `RunLeaseCatchup.spec`, `RunLeaseExpiry.spec`
(post: the `Result` returned, safety being "no panic"), over the members' address facts.

## 3. The statements each workload must meet, and what each reuses

The shape every dist client statement on this base has (putget's, `Spec/.../dist/putget/Client.lean`): the
machine's share is `etcdAddrAt ep γE mid` (the address serves etcd's table for member `mid` publishing at `γE`)
plus what the workload's invariant needs, per endpoint; the calls are the per-operation interim axioms at
clientv3's interface (`Client_Put_dist`, `Client_Get_dist`: `cli.Put`/`cli.Get` by `New`'s client at another
machine, at the member's published view `envAt γE ν`), until #24's S2 re-proves clientv3 over the grpc model.
`EnvView` is `⟨st⟩` (the KV state variable's name) only.

| Workload | Calls | Its check needs from the member | Single-process proof it reuses |
|---|---|---|---|
| leaseRead | `newClient`, `Leases`, `TimeToLive(7)`, `Close` | nothing of its state: `etcdLeaseLeasesSpecAnyW` (the listing is `Nodup`) and `etcdLeaseTTLSpecW` (the reply's id is the one asked), both heap-free and view-free | leaseN's `check` (proof text adapted: its calls are over `isGrpcRpcs`/`etcdLeaseReadAt`, the in-process model) |
| leaseExpiry | `newClient`, `Grant(1)`, `Leases` (polled), `Close` | the member's lessor name `γl` and its history: `etcdLeaseLeasesSpecLive γl` with `lessorLb γl m`, so that "absent at m" (`leaseAbsentFrom γl m id`) persists | leaseexpiryN's `gone`, `grant`, `listed` (specs over `isGrpcRpcs eps … (etcdLeaseLeasesSpecLive γl)`) |
| leaseCatchup | `newClient` ×2, `Grant(maxLeaseTTL)` at the last and first members, `Leases` (polled) at the last | the granting member's lessor names, and the cluster's order of grants (the last filler listed implies the first grant listed, unless it expired: `lease.leasesNoExpiry`) | leasecatchup's `grant`, `leases`, `listed` and `run`'s argument |

What is reusable unchanged: the pure parts and the heap-free vocabulary: `listed`'s loop (its proof, verbatim
modulo the package), `etcdLeaseLeasesSpecAnyW`/`etcdLeaseTTLSpecW`, `etcdLeaseLeasesSpecLive`, `lessorLb`,
`leaseAbsentFrom` and leaseexpiryN's/leasecatchup's arguments over them. What must be adapted: every proof of
a function that makes a call, since the in-process specs (`leasecatchup.grant.spec`, `leases.spec`,
`leaseexpiryN.gone.spec`, `leaseN.check.spec`) take `isGrpcRpcs eps method Spec`, the axiomatized
`Invoke`'s registration in the same process, which a client at another machine does not have: the dist
client's calls go through the net grpc model (`grpcAddrAt a (etcdSvc γE mid)`), and the specs of clientv3's
`Lease.Grant`/`Leases`/`TimeToLive` over it do not exist yet (S2's clientv3 proofs, in flight with #24's
owner). So every call site needs a dist spec of its call, as `Client_Get_dist` is for `cli.Get`.

## 4. Dependencies

| Need | State |
|---|---|
| The translation of `dist/client` | **available** (§1) |
| `etcdstart.NewClients` spec (the dist programs' `newClient`), `Client.Close`, `context.WithTimeout`, `time.Sleep` | **available** (`Spec/.../lib/etcdstart/NewClients.lean`, `Spec/go_etcd_io/etcd/client/v3/Client__Close.lean`; putget's `Client` proof uses `NewClient`, `WithTimeoutBackground`) |
| The members' address facts per endpoint (`etcdAddrAt`), as putgetK's client share | **available** in shape (`clientShare`), per member for k members on `dist-putgetk`'s line, now on r3 |
| `cli.Lease.Leases`, `cli.Lease.TimeToLive` across machines, view-free (leaseRead) | **missing**. `etcdSvc` is an axiom with no law (`S2Interim.lean`: "no proof can learn an entry of it"), and no per-call dist axiom exists for any lease method (`Client_Put_dist`/`Client_Get_dist` only). `notes/etcd-dist-plan.md` §17.2: N2 (I-1) "Not done: `etcdSvc` stays an axiom, and no `etcdSvc_unary` law is added." |
| `cli.Lease.Grant`, `cli.Lease.Leases` across machines **at the member's lessor names** (leaseExpiry, leaseCatchup) | **missing**, and harder: the view would have to carry the member's lessor name (`γl`) and its history; §17.2's O1 (`etcdEnvOf ν` as a definition tied to the member's own names) and the restart point (a view must be restart-stable: `restartNames` keeps `rd.raft`, `kvCongr`, `ids`; whether it keeps the lessor's name is to be checked when D6 reaches the lessor) |
| `lease.leasesNoExpiry` for leaseCatchup | **available** as stated: `EtcdEnv.noExpiry` (conditional) and `Compatible` (§5) |
| The unary transport on r3 | the interim axioms on r3 are A1 (`etcdSvc`), A3 (`Serve_dist`), the putget calls (`Client_Put_dist`, `Client_Get_dist`), S5's peer side (`NewServer_dist`, `NewPeerHandler_dist`, `PeerServe_dist`) and `os.Getenv.wp_proofEnv`. `etcd-safe-transport/2026-11-24` (`f152a3be06`) is an ancestor of r3: no newer transport branch exists (checked 2026-11-25 with `git ls-remote`) |
| The lead's answer to our two questions (#50, 7161464198) | **none yet** (checked 2026-11-25) |

## 5. The `leasesNoExpiry` question: no split needed, already handled

`lease.leasesNoExpiry` (`Proof/go_etcd_io/etcd/server/v3/lease/LessorBackend.lean`) is an opaque pure `Prop`:
"no lease of any lessor the program creates expires while the program runs". A pure proposition is the same in
every machine's proof, so "per member" changes nothing by itself; and splitting it per member would not help,
since a lease lives in every member's lessor (granted through raft), so leaseExpiry's 1 s leases expire in every
member's lessor, the one leaseCatchup's member runs too.

What makes it sound on the dist deployment is already in the statement, at the deployment level:
- `Compatible` (Lean `DeploymentDefs.lean:165`, Go `deployment.compatible`) refuses a deployment with
  `leaseExpiry` beside a workload that `needsNoExpiry` (authLease, leaseCatchup);
- `EtcdEnv.noExpiry : (∃ w ∈ d.workloads, w.needsNoExpiry = true) → lease.leasesNoExpiry`
  (`TopLevelDefs.lean`): the premise is taken only for deployments with leaseCatchup or authLease, where no
  workload grants a short lease (`grantsLeases` is authLease, leaseCatchup, leaseExpiry; authLease is alone;
  leaseCatchup's leases are `maxLeaseTTL`).

So: leaseRead and leaseExpiry never take it (leaseexpiryN's proof does not; leaseN's does not); leaseCatchup
takes it from `EtcdEnv.noExpiry`, at a deployment where the premise is meant to hold. This is the unified
scope's option (a) moved to the deployment: leaseExpiry and the no-expiry workloads are never in one
deployment. Nothing to change. (Remaining caveat, the same as in one process: the premise is about the real
clock, untestable; with crashes (D6) a member's lessor `Recover`s its leases with refreshed expiries, which
only makes expiry later.)

## 6. The blocker and the smallest unblocking step

N9b cannot be proved on r3 without either a lease entry of the service table with a law, or per-call interim
axioms at clientv3's interface; both are N2's (the lead's), and the brief forbids N9b a new axiom. Writing the
dist lease call specs as statements only (hypotheses of the workloads' `wp_proof`s, the Link pattern) is possible,
but would draft N2's interface on our own, which the plan says N9b waits for.

**Smallest unblocking step (for leaseRead, the first workload):** two view-free statements at clientv3's
interface, in the form of `Client_Get_dist` (`Spec/.../dist/ClientGetDist.lean`), over `etcdAddrAt ep γE mid`
and nothing of the view:
- `Client_LeaseLeases_dist.spec`: `cli.Lease.Leases(ctx)` by `New`'s client returns `nil` and a response whose
  `Leases` slice is `m.ids.map LeaseStatus.mk` with `m.ids.Nodup` (`etcdLeaseLeasesSpecAnyW`), or an error;
- `Client_LeaseTimeToLive_dist.spec`: `cli.Lease.TimeToLive(ctx, id)` returns `nil` and a response whose `ID` is
  `id` (`etcdLeaseTTLSpecW`), or an error.
Whether they come as reviewed interim axioms or as an `etcdSvc` law for the two entries (with S2's clientv3
proofs) is the lead's choice; N9b needs only the statements to start (a proof takes them as hypotheses). Both
specs are view-free, so they avoid O1 entirely.

**For leaseExpiry and leaseCatchup** the step is larger: the same for `Lease.Grant` and `Lease.Leases`, but at the
member's lessor names (`etcdLeaseLeasesSpecLive γl`, the grant's lessor fact), which needs the view (or the table
at the start, §17.2's "route found on the way": `memberBoot`'s `ρ`/`E₀`) to name the member's lessor. That is O1.

## 7. Order and size (once unblocked)

1. **leaseRead** (~300 lines): `leaseReadCheck.spec` (over the two statements of §6, `NewClients`, `Close`),
   `RunLeaseRead.spec` (a loop over `eps`, `checked`/`ended`), `Link` entries, `etc/gen-link.py` list.
2. **leaseExpiry** (~450): `leaseGrant`, `leaseList`, `listed`, `gone` (leaseexpiryN's arguments, re-stated over the
   dist calls), `RunLeaseExpiry` (the three slices of clients, ids and flags, the deferred `Close`s in a loop).
3. **leaseCatchup** (~450): `RunLeaseCatchup` over leasecatchup's argument, `ready` an observer (`MainReady`'s
   callback), `EtcdEnv.noExpiry` at its deployments.

About 1200 lines in all, the lead's estimate; the shared helpers (`leaseGrant`, `leaseList`, `listed`) once.

## 8. leaseRead proved over draft statements (2026-11-25, the coordinator's go-ahead)

The coordinator posted the plan to the lead on #50 with the proposal of §6; we proceed on it unless the lead
objects (no reply from the lead yet when this was written).

- **The draft statements** (N2-owned, pending the lead; `def … .spec : Prop` only, **no axiom, no proof**):
  `etcd_dist.Client_LeaseLeases_dist.spec` (`Spec/.../etcd/dist/ClientLeaseLeasesDist.lean`) and
  `etcd_dist.Client_LeaseTimeToLive_dist.spec` (`ClientLeaseTTLDist.lean`), shaped like `Client_Get_dist`
  (`isNewClient cl [ep] V`, `clientNoProxy cl`, `etcdAddrAt ep γE mid`, a client context), plus the client's
  `Lease` field as the `*lessor` `lp` the call is made on; nothing of the member's view (`envAt`) is read. Posts:
  `nil` and the listing's `Leases` slice (owned) with `ids.Nodup`, resp. the reply's `ID` field `↦□ id`; or an
  error and `null`. TimeToLive's is for the call without options (`slice.nil`) only.
- **Vocabulary** (`Proof/.../dist/client/LeaseDefs.lean`, defs): `leaseMember a` (`Net.addrOk a` and
  `∃ γE mid, etcdAddrAt a γE mid`), `clientCoreAt_of_new` (`Client.Close`'s precondition from `New`'s result).
- **Specs and proofs** of `dist/client` (`Spec/.../dist/client/`, `Proof/.../dist/client/`, namespace
  `etcd_dist_client`): `checked`, `ended`, `newClient` (over `zap.NewNop`, `etcdstart.NewClients`), `leaseList`
  (over the draft Leases statement and the context specs), `leaseReadCheck` (leaseN's `check` proof adapted:
  the slice literal, `defer cli.Close()`, the double loop verbatim, TimeToLive over the draft), `RunLeaseRead`
  (the loop over `eps`, `ended`/`checked`). `RunLeaseRead.spec`: with `eps ↦*□ addrs` and `[∗list] a ∈ addrs,
  leaseMember a`, `threadBound ≤ 2^30`, `errors.AsTarget`, and `Nonempty (WEnv GF)` (a watch environment for
  `newClient`'s client; N7 discharges it as putget does, `wenv_nonempty`), it returns (no panic), `levelTok 0`
  kept. Each proof takes its callees' specs as hypotheses; no `sorry`.
- **Not linked**: no `Link.lean` for `dist/client` (the two draft statements have no proof, so `RunLeaseRead`
  has no linked result yet; `etc/verified-code.py` counts it unverified). When the lead settles N2, the link is
  `etc/gen-link.py` over this package with the two statements' proofs (or axioms) as roots.
- **Build**: on fk-lean1 (`wt/etcd-safe-n9b`), every module above built, no error, no `sorry`; `#print axioms`
  of the three main theorems: `propext`/`Classical.choice`/`Quot.sound` and the base's existing axiomatized
  vocabulary (`etcd_dist.etcdSvc`, `grpcConn`, `grpcAddrIsRaw`, `grpcSrvCfgRaw`, `grpcWrotePeer`,
  `promSrvMetrics`), none new. `etc/tier-check.py --check` passes.
- **Next** (waits on the lead's O1): leaseExpiry and leaseCatchup (§7, steps 2-3).

## 9. The two draft statements reviewed (2026-11-25, `axiom` skill; coordinator-E's item 6)

Both **sound with a fix** (`notes/axiom-review/n9b-lease-leases.md`, `n9b-lease-ttl.md`): no program
refutes them (the Go code at `e94f33b50`: a listing is one map's values keyed by ID; every successful
`TimeToLive` reply echoes the asked ID, the not-found `TTL -1` path and the follower's forwarding with
`TimeToLiveHTTP`'s ID check included; a real 3-member cluster under grant/revoke/expiry, a stopped follower
and a killed leader: 176609 calls of each, no violation). The fix: both lend and return the caller's
`levelTok 0`, as the proved in-process `lessor.Leases.spec`/`lessor.TimeToLive.spec` (the retry backoff's
`epMu` reader slot, `backoffOkT`); `leaseList.spec` threads it; `leaseList`'s and `leaseReadCheck`'s proofs
adapted; built on fk-lean1 (`Proof…dist.client.leaseList`, `leaseReadCheck`, `RunLeaseRead`), no error.
For the lead, when they become axioms: `etcdSvc`'s and `Serve_dist`'s docstrings (F4) name the KV calls
only and must add the two lease entries (`etcdLeaseLeasesSpecAny`, `etcdLeaseTTLSpec`). The same token gap
is in `Client_Get_dist`/`Client_Put_dist` (not changed here).
