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

## 10. leaseCatchup and leaseExpiry over the lead's drafts (option B), 2026-11-25

The lead's O1/N2 design (#50, 2026-11-25T15:52:14Z; `notes/etcd-dist-plan.md` §18): the view is a Lean value
`DistView := ⟨kv, ls, auth⟩`, the lease drafts `Lease_Grant_dist`, `Lease_GrantLive_dist`,
`Lease_LeasesGranted_dist`, `Lease_LeasesLive_dist` at `Γ.ls mid`, our two drafts re-indexed `γE → Γ` with
`levelTok 0` threaded (all in `Proof/.../etcd/dist/ClientViewDist.lean`, namespace `etcd_dist.view`, each
`X.spec svc` over the table `svc : DistView → w64 → GrpcSvc GF`, A1 re-indexed).

- **Merge**: `etcd-safe-n2/2026-11-25` @ `70588fe058` merged whole (one commit over our base: the drafts file,
  §18, STATUS). `ClientViewDist.lean` built unchanged on fk-lean1 (warnings only: unused `π`).
- **Re-index**: our `Spec/.../dist/ClientLeaseLeasesDist.lean`/`ClientLeaseTTLDist.lean` are deleted; the
  proofs use the lead's re-indexed copies (`view.Client_LeaseLeases_dist`, `view.Client_LeaseTimeToLive_dist`).
  Every N9b spec takes `svc`; `leaseMember svc Γ a` (`⌜addrOk a⌝ ∗ ∃ mid, etcdAddrAtV svc a Γ mid`), and
  `memberCli svc cl ep V Γ mid` (`New`'s client of one member, no proxy, its address fact) with
  `leaseClientV_of_memberCli` (the drafts' `leaseClientV`, the `Lease` field from `isNewClient`)
  (`Proof/.../dist/client/LeaseDefs.lean`). `RunLeaseRead.spec svc` quantifies `Γ` (one view for every member).
- **New specs and proofs** (`dist/client`, each `wp_proof` taking its callees' specs, the drafts among them):
  `leaseList.spec`/`specLive`/`specGranted` (one per Leases draft), `leaseGrant.spec` (revocable,
  `Lease_GrantLive_dist`)/`specMono` (`Lease_Grant_dist`), `listed` (leaseexpiryN's, copied), `gone`
  (leaseexpiryN's argument; a listing's error polls again), `RunLeaseCatchup`, `RunLeaseExpiry`.
  - `RunLeaseCatchup.spec svc`: `Γ.kv.lm = .mono`, `addrs ≠ []` (`eps[k-1]` panics on none; `MainReady`
    checks it), `ready` any call that returns (`∀ Ψ, ▷ Ψ #() -∗ WP ready #() {{ Ψ }}`; the orchestrator's is
    `func() {}`). The panic is unreachable because `g1` is granted at the last member's lessor and
    `Lease_LeasesGranted_dist` at `G = [g1]` lists it, whatever the fillers did (leasecatchup's argument).
  - `RunLeaseExpiry.spec svc`: `Γ.kv.lm = .revocable`. The deferred `Close`s in the grant loop are a chain
    whose triple the loop invariant carries.

### What the lead's drafts lack (for the lead; not edited here)

1. **"Absent stays absent" at a remote member.** leaseexpiryN's check uses `lease.lessorAt_absent_stays`, whose
   premise `lessorRdInv γl` is the lessor's reader invariant: it holds the member's heap (`lsF l ↦□ id` in
   `lessorRdBody`), so a client at another machine cannot hold it, and no draft's post gives the fact. The
   proof of `RunLeaseExpiry` takes it as a hypothesis, the draft law `lessorAbsentStays_dist.law svc`
   (`LeaseDefs.lean`): from `etcdAddrAtV svc a Γ mid` and three `lessorAt (Γ.ls mid)` snapshots at
   `i ≤ k ≤ j` (the lease in the first, not in the second), it is not in the third (`|={⊤}=>`). It is heap-free
   in substance (`histOnce` of the history). Options for N2/P-L1: (a) split `lessorRdInv` into a heap-free
   history invariant the start hands to clients with the address fact (then the law is a theorem); (b) add the
   law as a reviewed interim axiom beside the lease drafts; (c) strengthen `Lease_LeasesLive_dist`'s post with
   "a lease the caller knows absent from index `k ≤ n` after it was live is not listed". (a) is the least trust.
   With crashes (D6), the law also needs the restarted lessor's history to continue at `ls mid` (§18.3).
2. `leaseClientV` has no `Persistent` instance (added in `LeaseDefs.lean`, not in the drafts file).
3. No draft is needed for `ready`: it is the orchestrator's `func() {}`; N7 gives its triple.

Nothing else: `Lease_Grant_dist`/`Lease_LeasesGranted_dist` suffice for leaseCatchup as drafted, and
`Lease_GrantLive_dist`/`Lease_LeasesLive_dist` for leaseExpiry with the law above.

### Handoff (2026-11-25, end of session; branch `etcd-safe-n9b`)

**Built on fk-lean1 with no error and no `sorry`** (`wt/etcd-safe-n9b`, `/shared/tmp/fklean1-check.sh`): `ClientViewDist`
(the lead's file, unchanged), `client.LeaseDefs`, `leaseList` (3 proofs), `leaseGrant` (2), `listed`, `gone`,
`leaseReadCheck`, `RunLeaseRead`, **`RunLeaseCatchup`** (all at the view, over the drafts as callee hypotheses).

**`RunLeaseExpiry`: not finished.** `Proof/.../dist/client/RunLeaseExpiry.lean` (spec in `Spec/.../RunLeaseExpiry.lean`).
- Build b7 (commit before the last) compiled it with no error, but with `declaration uses sorry` at
  `RunLeaseExpiry.wp_proof` (line 87), `wp_Close` unused, and "tactic never executed" in the grant loop's `defer`
  bullet. The cause was the bullet `· iexists _; iframe` (proving the new `defer` chain's triple): `iframe` closed it
  without the `Close` step. A `sorry` that no error reports has to come from a `try` that swallowed an elaboration
  error. The likely suspect is the check loop's `(try (· iframe #; ipureintro; rw [hnz]; exact Hx_lookup))` after
  `(try wp_apply wp_load_slice_index eps …)` (around line 355).
- Build b8 (this commit) replaced the bullet with `iexists _; iframe defer` (no error there now, so `wp_Close` is
  used). It also joined the two `try`s into one, `(try (wp_apply … as -;\n focus (…)))`, which is a **parse error**
  (line 357: "unexpected identifier; expected ')'"). The errors at 337 and 97 follow from it.
- **Next step:** fix that line, e.g. drop both `try`s and see whether the forRange loads `eps[j]` at all (if it
  does: `wp_apply wp_load_slice_index eps … as -` then `· iframe #; ipureintro; rw [hnz]; exact Hx_lookup`; if
  not: delete the two lines). Then rebuild `client.RunLeaseExpiry` and check that no `declaration uses sorry` and no
  "never executed" warning remain in our files.
  Then: `etc/tier-check.py --check` (it passed for the leaseRead files on the earlier base; not rerun this
  session), the `#print axioms` check of the three Run* theorems, and STATUS.md.
- No `Link.lean` for `dist/client`: the drafts and the law `lessorAbsentStays_dist.law` are callee hypotheses.

## 11. F2 session 1 (2026-11-26): handoff

#50 F2 (the lead's split, 2026-11-26T01:14:37Z): leases on the full no-crash line. Branch **`etcd-safe-f2`**
off M1's `etcd-safe-m1-top/2026-11-25` @ `e2d102d97b`; worktree `/shared/etcd-grove-f2`; fk-lean1
`~/eg/wt/etcd-safe-f2` (its `.lake/build` moved from `wt/etcd-safe-n9b`).

**N9b brought over without merging the branch whole.** `etcd-safe-n9b` sits on the crash integration line
(etcd pin `e94f33b50`, P6-P8, round 3): merging it would bring all of that into the no-crash line (59 files
conflicted). Its own files (the `dist/client` lease specs and proofs, the axiom reviews, this note) were taken
from `a276f9570e` and re-indexed to M1's view (no `svc` parameter: `etcdAddrAt`, `leaseClientAt`).

**Done.**
- *Item 2:* `lessorAbsentStays_dist.law` is a theorem (`LeaseDefs.lean`, `law_holds`), over the heap-free slot
  `lease.lessorSlot` (`Proof/go_etcd_io/etcd/server/v3/lease/LessorSlot.lean`; design: the ledger's
  2026-11-26 entry). `leaseMember`/`memberCli` carry `lease.lessorSlot (Γ.ls mid)`; `RunLeaseExpiry` uses the
  theorem (no hypothesis left). No interim axiom's text changed.
- *Item 5 (part):* the six lease contracts are interim axioms, each in its own pair (Spec/Proof
  `.../etcd/dist/{LeaseGrantDist,LeaseGrantLiveDist,LeaseLeasesGrantedDist,LeaseLeasesLiveDist,
  ClientLeaseLeasesDist,ClientLeaseTTLDist}.lean`, `axiom … .wp_proof` at line 59/59/59/59/57/57).
  Route rows: `notes/etcd-dist-plan.md` §18.4 (no `dsv-axiom-routes.md` exists on any branch). The four
  lessor ones must not be linked before P-L1.
- *The three missing axioms* (`Lease.Revoke`, `TimeToLive(WithAttachedKeys)`, `Put(WithLease)`) are **not
  drafted**: authLease alone calls them, auth on, and their contracts (who is refused, the owner's
  revocation, the keys verdict) are stated over the auth names F7 adds to `Γ`. Rows in §18.4, marked
  "after F7's auth view".

**Next, in order.**
1. Build result of `b7a05e8e60`-and-later (see STATUS); fix what fails in `LessorSlot`/the ported proofs.
2. **P-L1** (item 4): `newLessor_alloc` at a given `γl` (`NewLessorAlloc.lean:113` allocates it today) taking
   `ghostMapAuth γl ½ ∅ ∗ lessorSlot γl`: open the slot, join the halves, `ghost_map_insert` the two keys,
   build `lessorRdInv` as today, prove `lessorHistOk γl` from `lessorAt_absent_stays` at `⊤ ∖ lessorSlotN`
   (namespace disjointness of `lessor_rd`/`lessor_slot`), close the slot. Then `NewLessor`/`newLessor`
   variants, `NewServer.specG`'s lessor name from the caller (`mvccLeases E.γ = Γ.ls mid` in the post), the
   member boot passing its half, and the start allocating `Γ.ls mid` and the slots (`ClusterNames.ls` in place
   of `DistView.ofKV`'s constant).
3. **Link** leaseRead/leaseCatchup/leaseExpiry as N7-kv linked kv (`KvLinked`, kvremote's dispatch).
4. The three auth-on lease axioms with F7.
