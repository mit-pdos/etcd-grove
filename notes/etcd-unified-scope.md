# One closed etcd theorem, `etcd_safe`: Scope (E0, 2026-11-21)

Scope for etcd-grove-03, stage E0 of `/shared/tmp/coord-03/etcd-unified-plan.md` (the user's decisions
D1-D6 of 2026-11-21: one theorem `etcd_safe`, built in four parts; retire the subsumed theorems, keep the
drivers' triples; restart1 included; watch and compacted retired; MainWatch stays at 3 members; names
`etcd_all` / `etcd_adequate` / `etcd_safe` / `etcd_robust`). Branch `etcd-all`, worktree
`/shared/etcd-grove-etcdall`. The precedent is `notes/k8s-unified-scope.md` (`k8s_safe`, `examples/k8s/all`).
No Lean edited, nothing built. Go: the new package `examples/etcd/all` (committed) and measurements in a
scratch copy (`/shared/tmp/etcdall-e0/`, not committed: §2.4).

**In short.** One Go package `examples/etcd/all` (package `etcdall`, in the examples' Go module: §2.3)
whose `Main` runs four part functions at once, `KV`, `Auth`, `Lease` and `Restart`, each of which runs
its drivers at once; every driver is called unchanged and every triple is GF-polymorphic, so the proof
is the k8s one repeated: a frame per driver, a `spawn` lemma for the thread tokens, one
`etcd_adequate_members_below` call with the eleven clusters' lists concatenated. Measured: the eleven
parts run in one process (k = 3: 30 s, and 38 s under `-race`, no race reported) **once restartN's ports
move**. Three findings block the statement as the plan wrote it, each with a recommended fix:

1. **Ports** (expected): authN and restartN both use peers `29000+i` (§2.2 A). Move restartN to
   `14000/15000` (a Go change to an existing driver, E1).
2. **Member ids across the process** (new): the trusted idutil model needs the 16 low bits of **every
   member of the process** distinct (k8s's `Hlow`). With six clusters of up to 1000 members that is false
   for any tokens (6000 values in 65536: about 230 collisions measured); at lean's tokens it holds only for
   k_i ≤ 70 (§2.2 B). New tokens make it hold at measured larger bounds (k1 ≤ 1000 with the others ≤ 300,
   or all ≤ 400), at the cost of the k ≤ 1000 claims of the composed drivers (decision N2).
3. **`lease.leasesNoExpiry` is process-wide** (new, a soundness-of-coverage finding): authlease and
   leasecatchup take it ("no lease of **any** lessor the program creates expires while the program
   runs", `Proof/go_etcd_io/etcd/server/v3/lease/LessorBackend.lean:66-80`); leaseexpiryN grants 1 s
   leases and waits until they expire. In one process the premise is false of every run in which
   leaseexpiryN gets that far, so `etcd_safe` with both would say nothing about those runs (§2.2 C).
   Either leaseexpiryN stays out of `etcd_safe`, or the premise is made per cluster (a trust-base change,
   decision N1).

---

## 1. What exists

### 1.1 Go Mains (all in the examples' Go module, `examples/go.mod`)

| Driver | Entry point | Members | Fixed addresses (listened on) | Token | Member names / data dirs | Snapshots / compactor |
|---|---|---|---|---|---|---|
| txnlinfaultsN | `txnlinfaultsN.go:121` `Main(k, clients, ops, sched) porcupine.CheckResult` | k ≤ 1000 | peer `26000+i`, client `27000+i`, bridge `28000+i` | `txnlinfaultsN-6255` | `txnlinfaultsN-i` | SnapCount = SnapCatchUp = 1 / off |
| partition | `linkv3p.go:182` `MainWatch(nw, nops, sched) int` | 3 (cluster3) | peers `23841-3`, clients `23831-3`, bridges `23851-3` | `linkv3p` | `linkv3p-{1,2,3}` | 1/1 / off |
| compactwatch | `compactkv.go:52` `Main()` | 1 | client `23794` (peer `23804` not served) | `compactkv` (its name) | `compactkv` | none / revision, retention 1 |
| cache | `cachekv.go:104` `Main(nw, nops) int` | 1 | client `23873` (peer `23883` not served) | `cachekv` | `cachekv` | none / periodic, 10 ms |
| authN | `authN.go:180` `Main(k) int` | k ≤ 1000, auth on | peer `29000+i`, client `30000+i` | `authN-1286` | `authN-i` | none / off |
| authlease | `authlease.go:325` `Main(k) int` | k ≤ 1000, auth on | peer `16000+i`, client `17000+i` | `authlease-3354335` | `authlease-i` | none / off |
| leaseN | `leaseN.go:109` `Main(k)` | k ≤ 1000 | peer `10000+i`, client `11000+i` | `leaseN-2422` | `leaseN-i` | none / off |
| leaseexpiryN | `leaseexpiryN.go:158` `Main(k)` | k ≤ 1000 | peer `12000+i`, client `13000+i` | `leaseexpiryN-1973196` | `leaseexpiryN-i` | none / off |
| leasecatchup | `leasecatchup.go:180` `Main()` | 3 (cluster3) | peers `24011-3`, clients `24021-3`, bridges `24031-3` | `leasecatchup` | `leasecatchup-{1,2,3}` | 1/1 / off |
| restartN | `restartN.go:295` `Main(k)` | 2 ≤ k ≤ 1000 (theorem: 3 ≤ k) | peer `29000+i` (client `30000+i` advertised, not served) | `restartN-1440` | `restartN-i` | 1/1 / off |
| restart1 | `restart1.go:178` `Main()` | 1 | none (peer `23811`, client `23812` not served) | `restart1` | `restart1` | 1/1 / off |

Data directories are `/tmp/etcd-grove-data/<name>.etcd`, WAL areas `/tmp/etcd-grove-wal/<name>.etcd`
(`etcdstart/common.go:51,60`). Every member's feature gate is its own
(`features.NewDefaultServerFeatureGate(name, lg)`, `common.go:113`); the compactor and snapshot settings
are per member (`ServerConfig`). No driver has a package-level `var`; none sets an environment variable
or a global feature gate.

### 1.2 Lean results per driver

All under `Proof/` and `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/<d>/`. Every driver's `Main`
triple is GF-polymorphic (`variable {GF} [hG]`), takes `isPkgInit`, its members' start bundles
(`etcdstart.memberStartRes`, or `cluster3.startRes clusterCfg`), `threadTok` and its `premises`, and
returns nothing exclusive.

| Driver | Triple (Spec `Main.lean`) | Start resources | Pure premises beyond the common ones* | Closed theorem / robust spec | GF / collection |
|---|---|---|---|---|---|
| txnlinfaultsN | `Main.spec`, post `r = Ok ∨ Unknown` | `[∗list] memberStartRes (members k)`, `[∗list] netAddrFree (bridges k)`, `sched ↦*□ steps` | `1 ≤ k ≤ 1000`, `ids.length = k`, `BootFacts`, client bounds (`< 2^31`, product `< 2^60`) | `etcd_txnlinfaultsN_safe`/`_robust` | `linkvGF` / `txnlinfaultsN.txt` (362 axioms) |
| partition | `MainWatch.spec`, post `r ∈ {0,1,2}` | `cluster3.startRes clusterCfg`, `sched ↦*□` | `BootFacts id₁ id₂ id₃`, writer bounds (`< 2^62`), errors/fmt/rpctypes `Assumptions` | `etcd_partition_watch_safe`/`_robust` (and `etcd_partition_safe` for `Main`, retiring) | `linkvGF` / `linkv3p.txt` (376) |
| compactwatch | `Main.spec` | `memberStartRes "compactkv" ⟨none, some 23794⟩` | `BootFacts id` | `etcd_compactwatch_safe`/`_robust` | `compactkvGF` / `compactkv.txt` (345) |
| cache | `Main.spec`, post `r ∈ {0..3}` | `memberStartRes "cachekv" ⟨none, some 23873⟩` | `etcd_putget.BootFacts`, writer bounds | `etcd_cache_safe`/`_robust` | `putgetGF` / `cachekv.txt` (346) |
| authN | `Main.spec`, post `r ∈ {0,1,2}` | `[∗list] memberStartRes (members k)` | `1 ≤ k ≤ 1000`, putgetN `BootFacts` | `etcd_authN_safe`/`_robust` | `putgetGF` / `authN.txt` (383) |
| authlease | `Main.spec`, post `r ∈ {0,1}` | same | putgetN `BootFacts`, `leaseIdsApart`, `leasePeersOk`, **`lease.leasesNoExpiry`** | `etcd_authlease_safe` (Adequacy, no `TopLevelRobustness`) | — / `authlease.txt` (390) |
| leaseN | `Main.spec` | same | putgetN `BootFacts`, `leasePeersOk` | `etcd_leaseN_safe`/`_robust` | `putgetNGF` / `leaseN.txt` (362) |
| leaseexpiryN | `Main.spec` | same | putgetN `BootFacts`, `leaseIdsApart`, `leasePeersOk` | `etcd_leaseexpiryN_safe`/`_robust` | `putgetNGF` / `leaseexpiryN.txt` (363) |
| leasecatchup | `Main.spec` (premises inside the precondition) | `cluster3.startRes clusterCfg` | `cluster3.BootFacts`, `leasePeersOk`, **`lease.leasesNoExpiry`** | `etcd_leasecatchup_safe`/`_robust` | `leasecatchupGF` / `leasecatchup.txt` (369) |
| restartN | `Main.spec` | `[∗list] memberStartRes m.Name' ⟨some m.Peer', none⟩` | `k ≤ 1000` (theorem `3 ≤ k`), `BootFacts`; bounds as instances (`ThreadBoundLe`, `ReceiptBoundLe`); no `grpcRepliesFit`, no client premises | `etcd_restartN_safe`/`_robust` | `restartNGF` / `restartN.txt` (258) |
| restart1 | `Main.spec` | `memberStartRes "restart1" {}` | `BootFacts id`; bounds as instances | `etcd_restart1_safe`/`_robust` | `restart1GF` / `restart1.txt` (238) |

\* Common to all: `threadBound GF ≤ 2^28`, `srvLevels`, `receiptBound GF ≤ 2^48`, `receiptBound GF ≤ N+1`,
`N + 7 + bootWB ≤ backend.wbInit`, `authRecordsFit`, `apply.backendUnderQuota`, `storage.diskOk`, and (all
but the restart drivers) `grpcRepliesFit`, `v3rpc.ServerMethodSets`, `errors.AsTarget …EtcdError.ty`,
`ContextReadErrs`/`ContextErrsClient` instances. The closed theorems add `HNs` (`prometheus.namesUnclaimed`
over the package's `initNames`), `HAs` (`addrsUnclaimed`, the listened addresses), `HDs` (`dataDirsAbsent`),
`HEnv` (`verifyEnvOff`), `Hfs` (`Fs.FsInit`), `HWal` (`etcdWalAreasInit` over the data dirs), and conclude
`Robust [] [(program, σ)] g (threads := 2^28) (bound := 2^40 - 11)`. Each adequacy is by
`etcd_adequate_members(_below)` (`Proof/.../examples/lib/etcdstart/AdequacyMembers.lean:98-260`), which
already takes arbitrary member, bridge, address and data-dir lists.

The GFs are all the same first slots; `linkvGF` (`partition/TopLevelDefs.lean:44`) adds slot 7
(`GhostVarF`) and slot 11 (`NaInvF`, porcupine's). It is a superset of the others' used slots, so
`etcdGF := linkvGF` (moved and renamed, as `k8sGF` was) serves every triple.

### 1.3 The theorems to retire (D2, D4): coverage, with evidence

| Retired | Covered by | Evidence / gap |
|---|---|---|
| putget (1 member, Put then Get) | txnlinfaultsN at k1 = 1 | porcupine's check of puts and gets (txnlin's model) implies a Get after an acknowledged Put of the same client reads it. Config differs: clients through bridges, SnapCount 1 (putget: no snapshots). Covered as a property. |
| putget3, putgetN (k ≤ 1000, Put/Get through member 0) | txnlinfaultsN (k1 members) | as above; putgetN's no-snapshot k-member configuration stays covered by authN/leaseN/leaseexpiryN (NoSnapCount). **Bound**: only up to the k1 bound N2 decides. |
| txnlin (1 member, no faults, lintest + porcupine) | txnlinfaultsN at k1 = 1, `sched1 = []` | partition's `Check` is `lintest.Run(txnlin.Model(), …, txnlin.Gen, …)` (`linkv3p.go:83-85`): the same workload and model. |
| partition `Main` (3 members, partitions) | txnlinfaultsN at k1 = 3 | txnlinfaultsN's doc: partition's workload and checks "carry over unchanged; only the start differs" (`txnlinfaultsN.go:14-18`). |
| compacted (1 member, periodic 10 ms compactor, Put then Get) | compactwatch + cache | **Partial**: compactwatch checks client Gets under the *revision* compactor; cache runs the *periodic* 10 ms compactor but checks the cache's Gets and the watch, not a server Get after a Put. The combination "periodic compactor + latest server Get" is not in `etcd_safe`. D4 retires it anyway; flagged. |
| watch (1 member, prefix watch + writers, `etcdstart.Check`) | partition.MainWatch (3 members, partitions) and cache | both call the same `etcdstart.Check` on a watch from revision 1 (`linkv3p.go:219`, `cachekv.go:169`). Covered. |
| auth (1 member), auth3 (3) | authN at k2 = 1, 3 | authN is auth3 for k members, auth3's principal assignment at k = 3 (`authN.go:1-12`), the same `auth.SetUp`/`auth.Work`/checks. Covered. |
| lease (1 member, Leases/TimeToLive reads, no grant) | leaseN at k4 = 1 | leaseN is the lease example per member (`leaseN.go:1-15`). Covered. |
| leasegrant (1 member, Grant then Leases lists it) | **leasecatchup** (not leaseN, which grants nothing) | leasecatchup grants through member 3 and checks member 3's listing lists it (after a catch-up), and authlease grants and checks attachments. Covered as a property at 3 members; the plan's inventory said leaseN: corrected. |
| leaseexpiry (1 member, a lease expires, listing omits it) | leaseexpiryN at k5 = 1 | covered **only if leaseexpiryN is in `etcd_safe`** (N1). |
| restart (restart3) | restartN at k6 = 3 | restartN is restart3 for k members (`restartN.go:1-12`). Covered. |

Their collections' axioms are all in the union of the eleven parts' collections (checked:
`comm` of each against the union is empty), so retiring them removes no axiom from what some result rests on.

---

## 2. Can the eleven Mains share one process?

### 2.1 Process-global state, item by item

| State | Per driver | Conflict? |
|---|---|---|
| Listened ports | §1.1 | **Yes: authN and restartN**, peers `29000+i` for i < min(k2, k6) (§2.2 A). All other ranges disjoint for k ≤ 1000 (`TestAddrs`): 10000-13999, 16000-17999, 26000-28999, 23794, 23831-23853, 23873, 24011-24033. (restartN's advertised client URLs `30000+i` collide with authN's served clients, but restartN never dials or listens on them.) |
| Member names / data dirs / WAL areas | `<pfx>-i`, `linkv3p-n`, `leasecatchup-n`, `compactkv`, `cachekv`, `restart1` | **No**: the prefixes differ (`leaseN-` vs `leaseexpiryN-` at the 6th character, `restartN-` vs `restart1`). `etcdWalAreasInit st Ds` is `∀ d ∈ Ds`, so the premise over the concatenation is the conjunction. |
| Tokens / member ids | §1.1 | Tokens distinct; **ids**: see §2.2 B. |
| idutil issue record (`idIssueExt`) | one per process | **Yes** (§2.2 B): the trusted model's faithfulness needs the 16 low bits of all the process's members distinct. |
| Lease ids (`leaseIdsApart`, 15 bits) | authlease, leaseexpiryN | **No**: within one cluster's lessors only (as k8s's §2.3). |
| `lease.leasesNoExpiry` | authlease, leasecatchup (premise); leaseexpiryN (its leases expire) | **Yes** (§2.2 C). |
| `leasePeersOk` | leaseN, leaseexpiryN, authlease, leasecatchup | **No**: every member of every part serves only the raft handler on its peer address (restartN through `raftSwap`, which forwards to the raft handler), so `/leases/internal` is a 404 everywhere. Recheck when the statement is written. |
| `authRecordsFit`, `backendUnderQuota`, `grpcRepliesFit`, `diskOk`, `verifyEnvOff`, `FsInit` | all | **No**: claims over every backend, reply, file and the environment of the run; each part's workload is small and the parts share none of these objects. |
| Prometheus names | each package's `initNames` (registered by package init) | **No**: package init runs once; `HNs` over the new package's `initNames` (generated, the union). |
| Feature gates | per member (`NewDefaultServerFeatureGate`) | **No**. No k8s gate in these programs (`etc/featuregate-check.py` is not concerned). |
| Compactor settings | compactwatch revision/1, cache periodic/10 ms, others off | **No**: per member (`ServerConfig`). |
| Snapshot settings | 1/1 for txnlinfaultsN, partition, leasecatchup, restartN, restart1; NoSnap otherwise | **No**: per member. |
| Package-level variables | none in the drivers | **No**. |
| Goroutines left running | members' servers, gRPC servers, bridges, partitioners, `holdToken`s, watch/cache loops, raftSwap's `http.Serve` | **No** for the logic: each forked inside its driver's triple over that driver's resources (k8s §3.4). In Go they keep their ports until the process exits, so the drivers' own tests must not run at the same time as this one. |
| zap logger, lintest, porcupine | `zap.NewNop()` per driver; porcupine inside `Check` | **No**. |
| Time | leaseexpiryN's 1 s leases; authlease 600 s, leasecatchup 3600 s; restartN/restart1 stop and restart | Only through `leasesNoExpiry` (§2.2 C). |

### 2.2 The three conflicts

**A. Ports.** authN `PeerBase 29000, ClientBase 30000` (`authN.go:37-38`) and restartN the same
(`restartN.go:67-68`). Measured: with the two in one process, whichever starts second fails `net.Listen` and
its `Main` returns without its check (no panic: the test would pass while one part did nothing; `TestAddrs`
is what catches it). **Proposed Go change (E1)**: restartN to `PeerBase 14000, ClientBase 15000` (no
example uses 14000-15999, k8s included). Its ids change with its peer URLs, so its token must be searched
again: at the moved ports `restartN-535` is the first token whose 1000 ids pass restartN's own
`TestMemberIDs` (measured, `TestFindToken`); under N2's options it is the jointly searched one instead. Lean:
`restartN/Defs.lean:44,67` (`members`, `token`), `Run.lean:388`, `Dir.lean`'s address lemmas (the
`addr_port` bound), and the TopLevelDefs address list: mechanical, but a change to an existing driver
(STOP).

**B. Member ids across the process (`Hlow`).** `TrustedCode/go_etcd_io/etcd/pkg/v3/idutil.lean`'s model of
`Generator.Next` `assume`s no other generator **of the process** issued the id; it is faithful only if
distinct members of the process differ in the 16 low bits of their ids (else two generators started in the
same millisecond issue the same first id, and the model silently drops that real execution). Each driver's
`BootFacts` states it within its own cluster, and its token was searched so that it holds for every
k ≤ 1000. Across clusters (measured, `examples/etcd/all`'s `TestMemberIDs` and a scratch search):

- At lean's tokens and ports it holds for every k1, …, k6 ≤ **70** (79 with restartN moved); at
  k_i = 1000 there are 228 colliding members (e.g. `txnlinfaultsN-828` and `authN-442`, low `0x00d6`).
- It cannot hold at six clusters of 1000: 6012 values in 65536 have about 6012²/2¹⁷ ≈ 275 expected
  collisions; no choice of tokens fixes that.
- New tokens, searched greedily, the fixed parts' ids kept (scratch `search_test.go.scratch`,
  `/shared/tmp/etcdall-e0/token-search.log`):
  - all six at **k ≤ 400**: found in 76 s (`txnlinfaultsN-s0`, `authN-s35`, `authlease-s2366`,
    `leaseN-s8407`, `leaseexpiryN-s543173`, `restartN-s692212`, the last at 14000);
  - txnlinfaultsN at **k1 ≤ 1000**, the other five at **≤ 300**: found in 6 s (`txnlinfaultsN-s5481`,
    `authN-s152`, `authlease-s277`, `leaseN-s110`, `leaseexpiryN-s52450`, `restartN-s6981`); at ≤ 200 in 3 s.
    (lean's `txnlinfaultsN-6255` itself collides with a fixed part's id below 1000, so it changes too.)
  - k = 500 for all six is out of reach (about 10⁹ tries for the last cluster).
  The searches keep authlease's and leaseexpiryN's 15-bit `leaseIdsApart` within their clusters.

A new token changes the driver's Go constant, its translation, its `Defs.lean` `token` abbrev, and its own
`TestMemberIDs` bound (1000 → the new bound); its closed theorem retires anyway (§4), and its triple's
premises do not mention the token's value beyond `BootFacts`'s ids.

**C. `lease.leasesNoExpiry` is a claim about the whole program.** Its docstring
(`LessorBackend.lean:66-80`): "no lease of any lessor the program creates (in a cluster or none; granted
there, or reloaded by `Recover`) expires … while the program runs" — sharpened so by the axiom review of
2026-11-02, which refuted a per-cluster wording ("a program with a standalone lessor and a 1 s lease met
that wording yet saw an expiry"): `NewLessor`'s `expiredC` payload is `⌜¬ leasesNoExpiry⌝ ∗ …` for every
lessor. leaseexpiryN's leases are granted with TTL 1 (raised to the 2 s minimum) and its `Main` waits until
they are gone (`leaseexpiryN.go:57-62`). In one process with authlease or leasecatchup, the conjunction of
the parts' premises is false of every run in which leaseexpiryN gets past its expiry wait, i.e. of the
runs the theorem is meant for. Lean would accept the composition (the premise is opaque, and the
leaseexpiryN triple does not take it), so this is caught only by reading.

Options:

- **(a) leaseexpiryN out of `etcd_safe`.** It keeps its own closed theorem (`etcd_leaseexpiryN_safe`, k5 ≤
  1000) as a second row; leaseexpiry (1 member) then retires into it as planned. No trust-base change. The
  Lease part is leaseN + leasecatchup.
- **(b) Make the premise per cluster**: `lease.leasesNoExpiryIn c` for a cluster identity `c` the lessor is
  created with (the member's cluster token, which `NewServer` has: `ServerConfig.InitialClusterToken`, or a
  ghost name allocated per cluster at boot), `NewLessor`'s payload `¬ leasesNoExpiryIn c`, `lease.bootCfg`
  and the auth/lease coupling carried at `c`; `etcd_safe` takes it for authlease's and leasecatchup's
  clusters only. A trust-base change (an opaque and a trust-boundary axiom restated): an independent axiom
  review (the 2026-11-02 refutation is exactly about the scope of this premise: a per-cluster form must say
  which lessors belong to `c`, and a lessor created outside a cluster must be in none or all), then
  re-proofs through `NewLessor`, `NewServer(R)`, `LeaseGrant`, `LeaseRun`. Estimate 1-2 sessions plus review.
- (c) Prove authlease and leasecatchup without the premise (the revocable mode's expiry arm with auth on,
  the monotone lessor's `Recover` with expiry): research-sized. Not now.

### 2.3 The new Go code (committed on `etcd-all`)

`examples/etcd/all/all.go`, package `etcdall`, **in the examples' Go module** (no `go.mod` of its own):
every driver is a package of that module already (k8s/all needed its own module only because the k8s
drivers have theirs), so nothing is added to `GO_MOD_PINS`; the goose project is one more `Project` like
`txnlinfaultsN`'s (`local=examples/etcd/all`, the same `lean_roots` plus porcupine).

```go
func spawn(wg *sync.WaitGroup, f func()) { go holdToken(); go func() { f(); wg.Done() }() }

func KV(k1, clients, ops, sched1, nw, nops, sched2, cnw, cnops)  // txnlinfaultsN, MainWatch, compactwatch; cache inline
func Auth(k2, k3)                                                // authN; authlease inline
func Lease(k4, k5)                                               // leaseN, leaseexpiryN; leasecatchup inline
func Restart(k6)                                                 // restartN; restart1 inline
func Main(k1, clients, ops, sched1, nw, nops, sched2, cnw, cnops, k2, k3, k4, k5, k6) {
	var wg sync.WaitGroup; wg.Add(3)
	spawn(&wg, func() { KV(…) }); spawn(&wg, func() { Auth(k2, k3) }); spawn(&wg, func() { Lease(k4, k5) })
	Restart(k6); wg.Wait()
}
```

Each part function has the shape of a driver (`{… ∗ threadTok} part(…) {True}`), so each part's triple is
its own stage and `Main`'s triple composes four triples of the same shape as a part composes its drivers.
Results are dropped (a failed check panics). Concurrent, not sequential, for the reason k8s gave (D1
there): `Robust` speaks of executions shorter than `2^40 - 11` steps; sequentially the later parts are
reached only after the earlier ones finish, concurrently every prefix interleaves all eleven.

`examples/etcd/all/all_test.go`: `TestAddrs` (listened addresses disjoint, ports ≤ 65535, at every k ≤ 1000;
**fails at lean** on authN/restartN until E1), `TestMemberIDs` (reports the largest uniform k with `Hlow`
and the collisions at 1000; checks the bound `uniformK = 70`, or `ETCDALL_MAXK`), `TestMainRun` (`Main`
once, every k-member part at `ETCDALL_K`, default 3, the drivers' tests' workloads and schedules, after
resetting all WAL areas and data dirs). Not to be run beside the drivers' own tests (same ports and dirs).

### 2.4 Measurements (scratch copy `/shared/tmp/etcdall-e0/scratch`, restartN at 14000/15000 there only)

- `TestMainRun`, k = 3 (27 members): PASS, `Main` 30 s (`mainrun-k3.log`); with `-race`: PASS, 38 s, no
  race reported (`mainrun-race-k3.log`); the final four-part shape with the whole test file: `final-k3.log`.
- Per part, the same composition with results kept (scratch `diag_test.go.scratch`, `diag-k3.log`,
  `diag2-k3.log`): txnlinfaultsN `Ok`, MainWatch `WatchOk`, cache `Ok`, authN `Ok`, authlease `Ok`;
  compactwatch ran all its rounds (instrumented once); the void drivers (leaseN, leaseexpiryN,
  leasecatchup, restartN, restart1) returned without panic, whether after their check or by an early
  return is not observable through `Main` (leasecatchup's time varied, 1.9 s and 6.7 s). The longest part
  is authN (30 s).
- `TestAddrs` at lean's ports: 1000 collisions (authN/restartN peers); at the moved ports: PASS.
- `TestMemberIDs`: K = 70 at lean, 79 with restartN moved; token searches as in §2.2 B.

---

## 3. The proof

### 3.1 Triples

- **`spawn`** (once): `{{ P ∗ (P -∗ threadTok -∗ WP f #() {{ True }}) ∗ wgDoneRight }} spawn wg f {{ True }}`
  over k8s/all's bookkeeping: `go holdToken()` by `wp_fork_tok_self` keeps a fresh token, `go func(){…}()`
  by `wp_fork_tok_body` gives the goroutine its fresh token for `f` and its exit token from the `holdToken`
  fork; `wg.Done` in the join idiom (`sync.join`, as `k8s/all/Main.lean` and the compactor). `holdToken`'s
  spec (post `False`) copied from `k8s/all/holdToken.lean`.
- **Each part**: the union of its drivers' preconditions; the exclusive resources are per member, per
  bridge and per schedule slice, so disjoint (as k8s §3.1); persistent premises duplicate. `wg.Add(n)`,
  `n` spawns, the last driver inline, `wg.Wait`. The drivers whose bounds are instances (restartN,
  restart1) get them from the props by `⟨…⟩`.
- **`Main`**: the same over the four part triples. `N` (receipts) shared: each triple asks
  `receiptBound ≤ N + 1` only.

### 3.2 The closed theorem

`etcd_adequate` by `etcd_adequate_members_below` (no registry to allocate, unlike k8s's `_alloc`):
`ms` the concatenation of the eleven start lists (k-member parts `startOf (members k_i)`; restartN
`⟨some peer, none⟩`; compactwatch and cache `⟨none, some client⟩`; restart1 `{}`; the two cluster3 parts via
`cluster3.members clusterCfg` and `startRes_intro`), `Bs` txnlinfaultsN's bridges ++ the two cluster3
parts' bridges, `As`/`Ds` the concatenated address and dir lists. New lemmas: `As.Nodup`/`Ds.Nodup` over
the concatenation (the drivers' own `_nodup` lemmas plus pairwise disjointness: six numeric ranges and
nine literal groups, by the `addr_port` bound and `decStr_inj`, as `k8s/all/Disjoint.lean`, here ~30
pairs: generate them by a lemma over ranges rather than by hand), and the permutation `hA`/`hD`. `HNs`
over `etcdall.initNames`. Two schedule literals (`schedLit`, k8s's block, twice). GF `etcdGF :=
linkvGF` moved to `examples/etcd/all/TopLevelDefs.lean`.

**Statement** (`etcd_robust.spec`): the union of the eleven premise lists of §1.2, once each for the shared
ones (`Hctx`, `Hcec` at `etcdGF`, `Haf Hbuq Hrf Hdbo`, `Hlp`, `HEnv`, `Hfs`), per part for the cluster
variables (`k_i, ids_i, ps_i, ctxs_i, boot_i, Hlen_i, BootFacts_i`; `leaseIdsApart` for authlease and
leaseexpiryN), the client/writer bounds of txnlinfaultsN, MainWatch and cache, two schedules (`∀ steps₁
steps₂`), `Hprem` per part at one `n`, `HWal` over the concatenation, **`Hlow`** over the concatenation of
all ids (§2.2 B, with the bounds N2 fixes), and `Hlne` (or its per-cluster form) per N1. Conclusion
`Robust [] [(etcdProgram …, σ)] g (threads := 2^28) (bound := 2^40 - 11)`.

### 3.3 Linking and initialization

`etc/gen-init.py`: `examples.etcd.all` in `ROOTS` and `PROGRAMS` (one `PkgTable.lean` over the union of the
eleven closures, estimated 1,500-2,000 generated lines); `etc/gen-link.py --etcdall` with
`etc/link-lean-first-etcdall.txt` (its Link imports the eleven `MainLinked`s/`Link`s; partition and cache
have `Link.lean`, not `MainLinked`).

---

## 4. Retirements (D2, D4) and what stays

- **Retire** (closed theorems: `Adequacy*.lean`, `TopLevelRobustness.lean` pairs, the `_safe` parts of
  `Results.lean`, `PkgTable.lean`, the `PROGRAMS` entries, their tcb collections): the twelve of §1.3
  (putget, putget3, putgetN, txnlin, partition `Main`'s, compacted, watch, auth, auth3, lease, leasegrant,
  leaseexpiry — the last only if N1 takes leaseexpiryN in), and, as in k8s, the eleven composed drivers'
  own closed theorems (subject to N2: if their k ≤ 1000 claims are to survive, they cannot retire, and
  their tokens cannot change). About 3,400 + 3,240 hand-written lines and 10,150 + 9,380 generated
  (`PkgTable`) lines go.
- **Stay**: every driver's `Main` triple, `MainLinked`/`Link`, `Init`/`InitLinked` (the new table needs
  the package facts; check each `InitLinked`'s importers with `etc/importers.py` before deleting), and the
  Go drivers (their tests keep testing them alone).
- Note partition's `Main` triple stays though its closed theorem goes (its `Link` is shared with
  `MainWatch`).

## 5. Trust base delta

- The union of the eleven collections: **401 axioms**, 0 `sorry` (the largest single one, authlease, has
  390). New collection `etc/tcb-collections/etcd-all.txt`, roots `examples/etcd/all/(Results|MainLinked)`.
- New trusted text: the Go `Main` and parts (what the theorem is about); the statement's `Hlow` and its
  rewording in `idutil.lean`'s faithfulness docstring ("the process's members: of the eleven clusters of
  `examples/etcd/all`"); under N1 (b) the restated `leasesNoExpiry` and `NewLessor` payload.
- No new axiom otherwise (the new package's initializer: generated, check `gen-init`'s output).

## 6. Stages

| Stage | Work | Lean (hand / gen) | Builds | Stops |
|---|---|---|---|---|
| E1 Go fixes | restartN ports and the tokens N2 picks (Go constants, `goose.py` retranslation, `Defs.lean` `token`/`members`, `Dir.lean`, drivers' `TestMemberIDs` bounds); goose project `etcd-all`; `uniformK` raised | ~80 / retranslation | incremental over the touched drivers | existing-driver change |
| E1L (if N1 = b) | per-cluster `leasesNoExpiryIn`; axiom review; re-proofs | ~300 | incremental, lease cone | trust base |
| E2 statements | `TopLevelDefs`, `etcd_robust.spec`, the part and `Main` specs | ~600 | spec cone | statement review |
| E3a KV part | `spawn`, `holdToken`, `KV` triple | ~300 | 1 incremental | — |
| E3b Auth, E3c Lease, E3d Restart | each part's triple | ~120 each | 1 incremental each | — |
| E3e Main + closed theorem | `Main` triple, `Disjoint`, `Adequacy`, `Results`, `TopLevelRobustness` proof, gen-init/gen-link | ~1,000 / ~2,000 | 1 incremental | — |
| E4 retire | §4; collections `--check --update`; `featuregate-check` unaffected; STATUS; paper Fig. 2 rows (the user edits) | −6,600 / −19,500 | 1 full + `etc/gates.sh` | land |

Total ≈ 2,400 hand-written new lines (mostly copied from the eleven adequacies and k8s/all), about two to
three sessions after the decisions. Each part triple can land on its own (E3a-d); `etcd_safe` lands at E3e.

**Risks.** R1 memory: the Link and Adequacy import eleven `MainLinked` cones (k8s's two were already
heavy); split `Adequacy` into `AdequacyLinked` + lemma modules early, and keep the part triples in the
proof tier (each imports only its drivers' specs). R2 instance synthesis: `etcdall.Assumptions` must imply
eleven packages' `Assumptions` (`synthInstance.maxSize` already 4096). R3 the disjointness lemmas:
~30 pairs; do them by a range lemma. R4 the Go test's coverage: void drivers' early returns are invisible
(add returned codes in a later Go change if wanted). R5 the step bound (as k8s R1).

## 7. Open decisions (recommendation in bold)

- **N1** `leasesNoExpiry` vs leaseexpiryN: **(a) now — leaseexpiryN out of `etcd_safe`, keeping
  `etcd_leaseexpiryN_safe` as its own row; (b) the per-cluster premise as a follow-up stage that then folds
  leaseexpiryN in.** (b) first if the user wants one theorem from the start (then the Lease part lands
  last).
- **N2** Bounds under `Hlow`: **new tokens for all six k-member drivers, txnlinfaultsN at k1 ≤ 1000 and
  the five others at k ≤ 300 (measured feasible); the composed drivers' own closed theorems retire with
  their k ≤ 1000 claims**. Alternatives: all six at ≤ 400 (measured); no token change but restartN's and
  every k_i ≤ 70; or keep the drivers' k ≤ 1000 theorems beside `etcd_safe` at k_i ≤ 70 (two statements
  per driver, against the precedent).
- **N3** restartN's new ports: **14000/15000** (E1, a change to an existing driver).
- **N4** Program shape: **four part functions, each a stage** (as committed) rather than one flat `Main`
  with ten spawns (one triple fewer per part, but no landable intermediate).
- **N5** Module: **the examples' Go module** (no new `go.mod`).
- **N6** `Hlow`'s form: **one premise over the concatenation of all eleven clusters' ids** (k8s's), plus the
  idutil docstring reworded to "the process's members" (already so worded since k8s/all: extend its example
  list).
- **N7** compacted's periodic-compactor Get (§1.3): **accept the gap** (D4 already retires it), or add a
  client Get to cache's driver later.

---

## 8. E1 and E2 (2026-11-21, after the decisions N1-N7)

### 8.1 E1: the Go changes and the token/bound table

- restartN at peers `14000+i`, clients `15000+i` (N3). leaseexpiryN out of the program (N1): `Lease(k4)` is
  leaseN + leasecatchup; compacted (`putgetc`, client `23791`, peer `23801` not served) in the KV part (N7):
  `KV` spawns four drivers and runs cache inline. Still eleven drivers; the member counts are renamed
  `k1..k5` (restartN's is `k5`, was `k6`).
- New tokens (N2), searched jointly (`/shared/tmp/etcdall-e1/search_test.go.scratch`: the fixed clusters'
  ids first, compacted's included, then per k-member cluster in turn its current token if it works, else
  the first `<pfx>-<i>` whose ids at its bound avoid every 16-bit low half taken so far and are distinct
  among themselves, authlease's also in 15 bits):

  | Driver | Old token | New token | `etcd_safe` bound | Driver's `TestMemberIDs` | Closed theorem's `k ≤` (unchanged) |
  |---|---|---|---|---|---|
  | txnlinfaultsN | `txnlinfaultsN-6255` | `txnlinfaultsN-12748` | k1 ≤ 1000 | 1000 | 1000 |
  | authN | `authN-1286` | `authN-133` | k2 ≤ 300 | 300 (`idMembers`) | 1000 |
  | authlease | `authlease-3354335` | `authlease-1787` | k3 ≤ 300 | 300 | 1000 |
  | leaseN | `leaseN-2422` | `leaseN-1302` | k4 ≤ 300 | 300 | 1000 |
  | restartN | `restartN-1440` (ports 29000/30000) | `restartN-11208` (14000/15000) | 3 ≤ k5 ≤ 300 | 300 | 1000 |
  | leaseexpiryN | `leaseexpiryN-1973196` | unchanged (not in `etcd_safe`) | — | 1000 | 1000 |

  The drivers' closed theorems keep `k ≤ 1000` (their proofs need only the ports' bound; `BootFacts` is a
  premise, so no Lean bound is forced), but for authN, authlease, leaseN and restartN that premise is now
  checked only up to 300: above it may be false of the real ids, and the theorem says nothing there. Their
  docstrings (`Defs.lean`, `Results.lean`) and Go comments say so. They retire in E4.
- Go: `TestAddrs`, `TestMemberIDs` (at the bounds above; 136 collisions at five clusters of 1000, for the
  record), `TestMainRun` k = 3 (30 s) and with `-race` (38 s, no race) pass; the five drivers'
  `TestMemberIDs`/`TestMembers`/`TestAddrs` pass. Logs `/shared/tmp/etcdall-e1/`.
- Lean: the five drivers' `token`, restartN's `members` and `Dir`/`Run` ports; goose project `etcd-all`
  (`etc/goose.py`); `examples.etcd.all` in `etc/gen-init.py`'s `ROOTS`/`PROGRAMS` (`Base.lean` by hand,
  fact `True`; `Init`, `InitLinked`, `PkgTable` generated, 935 table lines).

### 8.2 E2: the statements

- `Proof/github_com/mit_pdos/etcd_grove/examples/etcd/all/TopLevelDefs.lean`: `etcdGF` (`linkvGF`'s
  slots), `etcdHeapAt`, `etcdProgram k₁ clients ops steps₁ nw nops steps₂ cnw cnops k₂ k₃ k₄ k₅`,
  `etcdNames` (`etcdall.initNames`), `etcdAddrs k₁ k₂ k₃ k₄ k₅` and `etcdDirs …` (the eleven clusters'
  lists concatenated in the parts' order).
- `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/all/TopLevelRobustness.lean`: `etcd_robust.spec`,
  `Robust [] [(etcdProgram …, σ)] g (threads := 2 ^ 28) (bound := 2 ^ 40 - 11)` (the etcd drivers' bound,
  through `etcd_adequate_members_below`; k8s_safe's `2 ^ 28 - 1` came from its drivers'
  `etcd_adequate_members` form; authlease, the one etcd driver in that form, fits the `_below` one: its
  `receiptBound ≤ 2 ^ 48` holds at `n < 2 ^ 40`).
- **The planned `etcd_safe`** (`Proof/.../examples/etcd/all/Results.lean`, E3e), as the drivers'
  `_safe`: the premises of `etcd_robust.spec` up to `HEnv`, then
  ```
  (n : Nat)
  (Hprem₁ : ∀ hG, ⊢ etcd_txnlinfaultsN.premises (GF := etcdGF) (hG := etcdHeapAt hG lctx) k₁ n ids₁ ps₁ ctxs₁ boot₁)
  … (the eleven `Hprem…` of the spec, each at this `n` instead of `∀ n`) …
  (σ : state) (g : GlobalState) (Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world))
  (HWal : etcdWalAreasInit (extLocal Fs.fsExt σ.world) (etcdDirs k₁ k₂ k₃ k₄ k₅))
  (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ) (Hthreads : σ.threads = 1)
  (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
  (Hsteps' : RealNstepsBelow (2 ^ 28) n
    ([etcdProgram k₁ clients ops steps₁ nw nops steps₂ cnw cnops k₂ k₃ k₄ k₅], ((σ, g) : CfgState)) κs (t2, σ2))
  (Hn : n + 12 ≤ 2 ^ 40) :
  (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
  (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
  (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2)
  ```
  (`Main` returns nothing; `Hlow` named `_Hlow` there, unused, as in `k8s_safe`.) `etcd_robust` follows
  by `Robustness.Robust.of_single_below`, as authN's.
- Forms decided: one `Hlow` over `ids₁ ++ [partition's three, compactwatch's, compacted's, cache's] ++
  ids₂ ++ ids₃ ++ ids₄ ++ [leasecatchup's three] ++ ids₅ ++ [restart1's]` (N6); the shared premises once
  (`Hctx`, `Hcec`, `Haf`, `Hbuq`, `Hrf`, `Hdbo`, `Hlp`, `Hlne`, `HEnv`, `Hfs`); the instance arguments the
  union of the drivers' (`errors`, `fmt`, `rpctypes` `Assumptions` from partition's watch, cache, authN,
  authlease); one `HWal` over `etcdDirs`; `Hprem…` per cluster at one `n`; the two schedules and the three
  workloads independent; cluster variables named by part (`ids₁…ids₅` with `k₁…k₅`, `pid₁₋₃`, `lid₁₋₃`,
  `cwId`, `cId`, `kvId`, `rId`).
