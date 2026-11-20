# One closed Kubernetes theorem, `k8s_safe`: Scope (2026-11-20)

Scope for etcd-grove-03, branch `k8s-unified-scope`, worktree `/shared/etcd-grove-k8sunified`. A plan and
the Go reading behind it. No Lean edited, nothing built. One Go measurement was taken: a temporary test,
since deleted, that computed the member ids (§2.3).

**The user's goal (2026-11-20).** One closed Kubernetes theorem, `k8s_safe`, over the k8s drivers'
workloads that do not overlap, proved by composing the existing Main triples rather than by redoing
proofs, with one adequacy and robustness theorem in place of the separate ones.

**Recommendation in short.** Add a new Go package `examples/k8s/all`, in a Go module of its own. Its
`Main` forks `k8setcd3.MainPartition(k, …, sched1)` on a goroutine, runs `compactor.MainPartition(sched2)`
on the main thread, and waits for both. No existing driver changes: the drivers' Go code, their
translations and their function triples all stay as they are. The two triples' preconditions share no
exclusive resource (§3.1), so the new triple is a frame argument plus some thread-token bookkeeping,
about 200 lines. The closed theorem uses the same generic adequacy lemma both drivers already use
(`etcd_adequate_alloc_members`), called with the two clusters' member, address and data-directory
lists concatenated. The five separate k8s closed theorems are retired; the function triples stay.
Estimate: about 1,100 hand-written Lean lines (most copied from the two existing adequacy proofs),
about 1,150 generated lines, and roughly 1,300 hand-written plus 2,100 generated lines deleted. That is
one to two sessions, two incremental builds and one full build.

---

## 1. What exists

### 1.1 Go Mains

| Driver | Go entry point | Cluster | Addresses (fixed) | Data dirs |
|---|---|---|---|---|
| k8s etcd3 store, 1 member | `examples/k8s/etcd3/k8setcd3.go:1887` `Main(clients, ops, watchers, wops)` | 1 member `k8setcd3`, `MaxUnaryRetries: 1`, no bridge | client `127.0.0.1:23896` (`:1862`), peer `:23906` (`:1889`) | `k8setcd3.etcd` |
| k8s etcd3 store, k members | `:2004` `MainCluster(k, …)` | `etcdstart.Members("k8setcd3N", k, 20000, 21000)` (`:1968`), token `k8setcd3N-6285` (`:1934`), bridges `22000+i` (`:1925-1927`) | peer `20000+i`, client `21000+i`, bridge `22000+i`, i < k ≤ 1000 | `k8setcd3N-i.etcd` |
| k8s etcd3 store, k members, partitions | `:2028` `MainPartition(k, …, sched)`: `MainCluster` plus `go cluster3.Partitioner` (`:2040`) | same | same | same |
| k8s compactor, 1 member | `examples/k8s/compactor/compactor.go:176` `Main()` | `StartCompactingServer("k8scompactor", …)` | client `:23976` (`:48`), peer `:23986` (`:51`) | `k8scompactor.etcd` |
| k8s compactor, 3 members, partitions | `:220` `MainPartition(sched)` | `cluster3.StartCluster(clusterConfig())` (`:56-65`): token `k8scompactorp`, names `k8scompactorp-{1,2,3}` | peers `23941-3`, clients `23931-3`, bridges `23951-3` | `k8scompactorp-{1,2,3}.etcd` |
| DaemonSet controller | `examples/k8s/daemonset/dsmain/dsmain.go:210` `Main(checks)` | none: the model API server `apimodel`, no etcd | none | none |

**The DaemonSet program** (`dsmain`) runs the real DaemonSet controller and client-go's informers over
the model API server. It has **no closed theorem**: `Proof/.../k8s/daemonset/` holds only `apimodel/`,
the model's own specs. Its intended theorem is **false of the code as it stands**: with ambiguous writes
the controller can bind two pods to one node (`dsmain.go:13-15`,
`issues/k8s-daemonset-ambiguous-create-duplicate-pod.md`). It overlaps nothing, since it involves no
etcd. It also cannot share a process with the other two drivers, because it mutates the feature gate
with `SetFromMap` (`dsmain.go:66-75`). That breaks the gate's environment assumption, "no code of the
program mutates the gate but `Set`s of the table's values"
(`Proof/k8s_io/apiserver/pkg/util/feature/Gate.lean:26-34`); `etc/featuregate-check.py:18-24,43` keeps
it outside for exactly this reason. **It stays out of `k8s_safe`.**

### 1.2 Lean results per driver

| Program | Triple (Results.lean) | Adequacy | Safe (Results.lean) | Robust spec / proof | Defs |
|---|---|---|---|---|---|
| etcd3 `Main` | `k8setcd3_Main` (`Proof/.../k8s/etcd3/Results.lean:97`) | `k8s_etcd3_adequate` (`etcd3/Adequacy.lean:107`) | `k8s_etcd3_safe` (`:123`) | `k8s_etcd3_robust.spec` (`Spec/.../k8s/etcd3/TopLevelRobustness.lean`) / `etcd3/TopLevelRobustness.lean:41` | `etcd3/TopLevelDefs.lean`: `k8setcd3GF` (slot 11 = `NaInvF`), `k8setcd3HeapAt`, `k8setcd3Program` |
| etcd3 `MainCluster` | `k8setcd3_MainCluster` (`:103`) | `k8s_etcd3_cluster_adequate` (`:221`) | `k8s_etcd3_cluster_safe` (`:168`) | `k8s_etcd3_cluster_robust` (`:53`) | `k8setcd3CProgram` |
| etcd3 `MainPartition` | `k8setcd3_MainPartition` (`:109`); spec `Spec/.../etcd3/MainPartition.lean:51-79` | `k8s_etcd3_partition_adequate` (`:306-427`, via `etcd_adequate_members`) | `k8s_etcd3_partition_safe` (`:214`) | `k8s_etcd3_partition_robust` (`:66`) | `k8setcd3PProgram` (uses `schedLit`) |
| compactor `Main` | `k8s_compactor_Main` (`compactor/Results.lean:53`) | `k8s_compactor_adequate` (`compactor/Adequacy.lean:125`) | `k8s_compactor_safe` (`:74`) | `k8s_compactor_robust` (`compactor/TopLevelRobustness.lean:41`) | `compactor/TopLevelDefs.lean`: `k8scompactorGF` (no slot 11), `heapAtKc`, programs |
| compactor `MainPartition` | `k8s_compactor_MainPartition` (`:59`); spec `Spec/.../compactor/MainPartition.lean:50-73` | `k8s_compactor_partition_adequate` (`:193-301`, via `etcd_adequate_alloc_members`) | `k8s_compactor_partition_safe` (`:115`) | `k8s_compactor_partition_robust` (`:52`) | `k8scompactorPProgram`, `k8scompactorPAddrs`, `k8scompactorPDataDirs` |

The linked triples are in `etcd3/MainLinked.lean:72` (`k8s_etcd3.wp_MainPartition`) and
`compactor/MainLinked.lean:94` (`k8s_compactor.wp_MainPartition`).

The trust-base collections are `etc/tcb-collections/k8setcd3.txt` (roots `etcd3/(Results|MainLinked)`,
588 axioms) and `k8scompactor.txt` (roots `compactor/(Results|MainLinked)`, 538 axioms). Their union
is **597 axioms**: compactor-only are the lease protobuf registrations, `leaseTimeToLive`, and
`strconv.FormatInt`/`ParseInt`. Neither collection has a `sorry`. `k8s.txt`, `k8s-compactor.txt` and
`k8s-apimodel.txt` are library collections and do not change.

The package tables come from `etc/gen-init.py`: `ROOTS` at `:108,110`, `PROGRAMS` at `:3315,3373`. The
Links come from `etc/gen-link.py --k8setcd3` (`:509`); the compactor's `MainLinked` is hand-written.

### 1.3 Overlap

- `MainCluster` is `MainPartition` with an empty schedule (the partitioner then does nothing). Its
  theorem is subsumed as coverage, as the user says.
- etcd3 `Main` (1 member) overlaps `MainPartition` at k = 1. It differs in two ways: no bridge, and
  `MaxUnaryRetries: 1` instead of the default retries.
- compactor `Main` (1 member) overlaps compactor `MainPartition`: same workload, one member in
  compaction mode instead of three.
- etcd3 `MainPartition` and compactor `MainPartition` do **not** overlap. One is the store's workload
  checked by porcupine (with watches); the other is five API servers' compactors plus a writer. They
  run on different clusters, ports, data directories and tokens.

The paper table (`/shared/grove-paper/osdi27/theorem.tex:166-169`) has exactly the rows
`k8s_etcd3_cluster_safe`, `k8s_etcd3_partition_safe` and `k8s_compactor_partition_safe`. (Its
`cluster_safe` row still says "on 3 members"; since 7f-6 stage A the theorem covers k members,
1 ≤ k ≤ 1000.)

---

## 2. Can the two Mains share one process?

### 2.1 Process-global state, item by item

| State | etcd3 `MainPartition` | compactor `MainPartition` | Conflict? |
|---|---|---|---|
| Ports | `127.0.0.1:{20000..20999, 21000..21999, 22000..22999}`, i < k ≤ 1000 (`k8setcd3.go:1925-1927`) | `23931-3, 23941-3, 23951-3` (`compactor.go:58-62`) | **No**: 23931 > 22999 for every k ≤ 1000. |
| Member names / data dirs | `memberDataDir "k8setcd3N-i"` = `/tmp/etcd-grove-data/k8setcd3N-i.etcd` (`WalLayout.lean:32`, `DirN.lean:126`) | `…/k8scompactorp-{1,2,3}.etcd` (`compactor/TopLevelDefs.lean`, `k8scompactorPDataDirs`) | **No**: the names differ in their fourth character (`k8se…` vs `k8sc…`). |
| WAL areas | `walAreaOf` of each data dir (`/tmp/etcd-grove-wal/<name>.etcd`) | same | **No**. `etcdWalAreasInit st Ds` is `∀ d ∈ Ds` (`WalAreasInit.lean:36`), so the premise over the concatenated list is the conjunction of the two. |
| Tokens / member ids | token `k8setcd3N-6285`, ids low-16 distinct for k ≤ 1000 (`k8setcd3_test.go:167`) | token `k8scompactorp` (`compactor_test.go:368`) | **No collision, measured** (§2.3). The trusted model's faithfulness argument must now cover both clusters. |
| `idutil` issue record (`idIssueExt`) | **one per process**: `Generator.Next` `assume`s that no other generator issued the id (`TrustedCode/go_etcd_io/etcd/pkg/v3/idutil.lean`, header) | same record | See §2.3. |
| Prometheus names | `read`'s two names, registered by package init (`k8setcd3Names`) | the same two (`k8scompactorNames`) | **No**: package init runs once; `HNs` is over the same list. |
| Feature gate | `Set("EtcdRangeStream=false")`, `Set("WatchList=true")` in `newStore` (`k8setcd3.go:1848-1858`) | only `Enabled(ListFromCacheSnapshot)` (NewCompactor, `compact.go:98`; listed in `Gate.lean`) | **No**. Different features. The assumption "each Set before any Enabled of its feature" (`Gate.lean:26-34`) holds in either order and under interleaving. Add the new program to `etc/featuregate-check.py`'s `INSIDE` (`:39-40`). |
| Compactor registry (`k8s.CompactorRegistry`, `endpointsMap`) | unused: `noCompactor{}`; its adequacy instantiates the registry name arbitrarily, `⟨0⟩` (`etcd3/Adequacy.lean:362`) | `StartCompactorPerEndpoint` at its 3 bridges; needs `regAuth ∅` (`compactor/Adequacy.lean:241-245`) | **No**: allocate the registry once and give `regAuth ∅` to the compactor. The etcd3 triple is parametric in `reg`. |
| Goroutines left running | members' servers, bridges, `holdToken` (`:1976`), partitioner (`:2040`), store and client goroutines | the same kinds, plus the writer, compactors and watch loops | **No** for the logic: each goroutine's WP was proved inside its own triple, over its own resources (§3.4). |
| zap logger | `zap.NewNop()` per call | `zap.NewNop()` per call | **No**. |
| lintest / porcupine | inside `Check`, per call | not used | **No**. |
| `holdToken` | unexported in `k8setcd3` and in `cluster3` (`cluster3.go:92`) | — | The new package needs its own 4-line copy (§2.2). |

**Conclusion: no Go change to either driver.** Their fixed addresses, names, tokens and directories
are already disjoint. The drivers' comments chose them "so that the examples' tests can run at once"
(`k8setcd3.go:1922-1923`).

### 2.2 The new Go code (new package; nothing existing changes)

`examples/k8s/all/all.go` (package `k8sall`), in a Go module of its own,
`examples/k8s/all/go.mod`. It requires the two driver modules through `replace => ../etcd3`,
`../compactor`, at their pins. The two modules' requirement lists agree on every shared version: the
diff shows only porcupine, lintest and testify extra in etcd3.

```go
// Main runs the Kubernetes etcd3 store's partitioned workload on k members (k8setcd3.MainPartition)
// and Kubernetes' compactor under partitions on three more members (compactor.MainPartition) at
// once, in one process, and returns when both have.
func Main(k uint64, clients, ops, watchers, wops int, sched1, sched2 []cluster3.Step) {
	go holdToken()                  // its thread token stays with Main: the etcd3 goroutine's exit token
	var wg sync.WaitGroup
	wg.Add(1)
	go func() {
		k8setcd3.MainPartition(k, clients, ops, watchers, wops, sched1)
		wg.Done()
	}()
	compactor.MainPartition(sched2)
	wg.Wait()
}

func holdToken() { for { time.Sleep(time.Hour) } }
```

**Why concurrent and not sequential** (decision D1). With sequential composition
(`go holdToken(); r := k8setcd3.MainPartition(…); compactor.MainPartition(…); return r`) the proof is
about 80 lines shorter. But `Robust` only speaks of executions of fewer than `2^28 − 1` steps.
Sequentially, the compactor part is reached only after the etcd3 part has finished, and a full etcd3
run may well take more steps than that, so the theorem could in practice say nothing about the
compactor. Run concurrently, both parts start in the first steps, and every interleaving in the bound
covers both. Concurrency also matches a real deployment (both API-server workloads at once), and the
Go test runs in roughly half the time. The `wg.Wait()` matters only for real Go: a process ends when
`main` returns, which would cut the etcd3 check short. Main returns nothing, so the result conjunct is
`v = #()`. etcd3's `Ok`/`Unknown` result says nothing beyond "no panic", which `Robust` already says.

**Go tests** (`examples/k8s/all/all_test.go`):

- `TestMain`: k = 3, small workload, a few schedule pairs, with `walarea.Reset` of all k + 3 members'
  areas (as the driver tests do since wal-link).
- `TestMemberIDs`: the low-16 condition across both clusters for every k ≤ 1000 (§2.3).
- `TestAddrs`: the two address lists are disjoint.

These tests use the same ports and directories as the drivers' own tests, so they must not run at the
same time as them. CI runs no Go tests (`.github/workflows/lean.yml`); write this in the test file's
comment.

Translation: a project `k8s-all` in `etc/goose.py`, like `k8s-compactor` (`:1640-1655`): local
directory, the same `lean_roots`, `packages=["."]`. Its `go.mod` also goes into `GO_MOD_PINS` and
`CLIENT_GO_PINS` (`:1819-1847`). Every other name resolves through the empty root to the existing
translations, so **no driver is retranslated**.

### 2.3 Member ids and the issue record (a trusted-text change)

`TrustedCode/.../idutil.lean`'s model of `Generator.Next` `assume`s that no other generator of the
process issued the id. Its faithfulness argument is that "generators of distinct members differ in the
prefix (the member ids' 16 low bits distinct, a premise of the examples, `TestMemberIDs`)". Each
theorem's `BootCore.lowNodup` (`SrvRaftLog.lean:515-525`) states that condition only within its own
cluster.

With two clusters in one process, a cross-cluster low-16 collision would let two generators started in
the same millisecond issue equal ids. The `assume` would then silently exclude real executions, which
would make the model unfaithful.

**Measured** (a temporary `TestZZCrossIDs` in `examples/k8s/etcd3`, run in this worktree, then
deleted). The compactor ids are `214a39417a505f63`, `2a653e6708ea5068` and `cb91392dbe1ea479` (low 16
bits `0x5f63`, `0x5068`, `0xa479`). None of these low halves appears among the first 1000 k8setcd3N
ids (`largest collision-free k = 1000`). So no Go change is needed.

**Plan (D5):**

- Add an explicit premise `Hlow : ((ps₁ ++ ps₂).map (uint.Z · % 2^16)).Nodup` to `k8s_safe`: the
  process's every member, the issue record's precondition. The proof does not use it; it records the
  trust-base condition in the statement, as `BootCore.lowNodup` does per cluster.
- Check it with the new `TestMemberIDs`.
- Reword idutil.lean's docstring: "distinct members **of the process**" instead of "of the example".

This is a trusted-text change, so it is a STOP for the user. The lease condition (`leaseIdsApart`,
15 bits) is within one cluster only (lease ids live in one cluster's lessor), so no cross-cluster form
is needed.

---

## 3. The proof

### 3.1 The new Main's triple, from the two triples

The two preconditions, as written:

- etcd3 (`Spec/.../etcd3/MainPartition.lean:73-76`): `isPkgInit k8setcd3 ∗ [∗list] memberStartRes (startOf (members k)) ∗ [∗list] netAddrFree (bridges k) ∗ sched ↦*□ steps ∗ threadTok ∗ k8s_etcd3N.premises k N ids ps ctxs boot`.
- compactor (`Spec/.../compactor/MainPartition.lean:65-71`): `isPkgInit compactor ∗ cluster3.startRes clusterCfg ∗ sched ↦*□ steps ∗ threadTok ∗ cluster3.premises clusterCfg N id₁ id₂ id₃ ps ctxs boot ∗ k8s.regAuth ∅`.

**The exclusive resources are disjoint.** Each `memberStartRes` (`StartRes.lean:73-76`) is per member:
`envVerifyOff`, the member's own data dir and areas, and the member's own peer and client addresses
with `httpProtoFree` per peer address. The bridges are per address, `regAuth ∅` is the compactor's
alone, the schedules are two different slices, and the premises are persistent
(`ClusterN.lean:91-104`, `cluster3/Defs.lean:150-170`). The two triples share no exclusive resource,
so the new triple is a frame.

The new spec, `Spec/.../k8s/all/Main.lean`:

```
{{ isPkgInit k8sall ∗ <etcd3's start bundles and bridges> ∗ cluster3.startRes clusterCfg ∗
   sched1 ↦*□ steps1 ∗ sched2 ↦*□ steps2 ∗ threadTok ∗ k8s_etcd3N.premises k N … ∗
   cluster3.premises clusterCfg N … ∗ k8s.regAuth ∅ }}
  Main k clients ops watchers wops sched1 sched2
{{ RET #(); True }}
```

Its pure premises are the union of the two lists: `1 ≤ k ≤ 1000`, both `BootFacts`, the thread and
receipt bounds (etcd3 takes them as instances, the compactor as premises: the same facts), `srvLevels`,
`N + 7 + bootWB ≤ wbInit`, `authRecordsFit`, `backendUnderQuota`, `grpcRepliesFit`, `diskOk`,
`ServerMethodSets`, `AsTarget`, `storageErrTyOk`, `objTyOk`, and the client-count bounds.

The proof, `Proof/.../k8s/all/Main.lean`, in the proof tier: it imports only the callees' Spec files.

1. `wp_start`. Derive `isPkgInit` of `k8setcd3`, `compactor`, `sync` and `cluster3` with `iPkgInit`;
   the new package imports them.
2. **Thread tokens.** Both triples consume a `threadTok` and return none (`{{ RET #r; ⌜…⌝ }}`,
   `{{ RET #(); True }}`).
   - `go holdToken()`: `wp_fork_tok_self` (Perennial `GooseLang/Lifting.lean:2006`). The forked
     thread never returns, since `holdToken.spec` has post `False` (copy of
     `Spec/.../etcd3/holdToken.lean`), so Main keeps the fresh token T₂.
   - `go func(){…}()`: `wp_fork_tok_body` (`:1993`). The goroutine receives the fresh token T₃ and
     hands it to `k8s_etcd3.MainPartition.spec`. It exits with T₂, which Main moves into the closure
     before the `go`, together with etcd3's resources and the WaitGroup's `Done` right.
   - The main thread keeps its own token T₁ for `k8s_compactor.MainPartition.spec`.
   - The WaitGroup uses `sync.join`, as the compactor's own proof does
     (`compactor/MainPartition.lean:353-438`).
3. Callee specs taken (`@` callees): `holdToken.spec` (the new package's own), `k8s_etcd3.MainPartition.spec`,
   `k8s_compactor.MainPartition.spec`, and the WaitGroup specs.

**Bounds** (`notes/bounds-plan.md`). Nothing new to count: two `go` statements and one WaitGroup with
counter 1. `etc/bounds-check.py` counts stay the same, or the WaitGroup goes in `etc/bounds-allow.txt`
as the compactor's does.

### 3.2 Linking and initialization

- `etc/gen-init.py`: add `github_com.mit_pdos.etcd_grove.examples.k8s.all` to `ROOTS` and to
  `PROGRAMS`. This generates `Proof/.../k8s/all/{Init,InitLinked,PkgTable}.lean`; the table covers the
  union of both closures, about 1,100 lines. Its `table_vars` include the registry name through the
  `k8s.io/apiserver/.../etcd3` fact (`gen-init.py:3388-3398`).
- `etc/gen-link.py --k8sall` with `etc/link-lean-first-k8sall.txt`. The Link imports both
  `MainLinked`s (which are linking modules) and the new `holdToken` proof.
- `etc/featuregate-check.py` `INSIDE`: add `("all", "examples/k8s/all", ".")`.

### 3.3 The closed theorem

`Proof/.../k8s/all/Adequacy.lean`, `k8s_adequate`, by `etcd_adequate_alloc_members`
(`Proof/.../etcdstart/AdequacyMembers.lean:122-162`). That lemma already takes arbitrary members `ms`,
bridges `Bs`, addresses `As` and data dirs `Ds`. The arguments:

- `ms := k8s_etcd3N.startAddrs k ++ cluster3.members clusterCfg`.
- `Bs := k8s_etcd3N.bridges k ++ cluster3.bridges clusterCfg`.
- `As := k8setcd3NAddrs k ++ k8scompactorPAddrs`.
- `Ds := k8setcd3NDirs k ++ k8scompactorPDataDirs`.
- `hA`, `hD`: a swap of the middle of two appends, from `k8setcd3NAddrs_perm`/`_dirs_perm`
  (`DirN.lean:132-151`) and the compactor's `List.Perm.refl`.
- `hAs`, `hDs` (Nodup): each list's own lemma (`k8setcd3NAddrs_nodup`, `k8setcd3NDirs_nodup`,
  `by decide`), plus **two new disjointness lemmas** of about 40 lines each:
  - addresses: every etcd3 address is `127.0.0.1:` ++ `decStr (b + i)` with b + i ≤ 22999 (`addr_port`,
    `DirN.lean:159`); the compactor's nine are literals ≥ 23931; then use `decStr_inj`.
  - directories: `memberDataDir_inj` plus a prefix inequality, `k8setcd3N-` vs `k8scompactorp-`.
- `hAsLit`: from both lists' lemmas.
- `HNs`: the one name list, `k8setcd3Names = k8scompactorNames`.
- `Hprog`:
  - allocate `regAuth ∅`, as `compactor/Adequacy.lean:241-245` does;
  - `wp_initialize'` of `k8sall`;
  - build the two schedules' slice literals; the 35-line `schedLit` block of each adequacy, once per
    schedule (it could become a lemma in a defs module);
  - split `[∗list] (ms₁ ++ ms₂)` and `[∗list] (B₁ ++ B₂)` with `bigSepL_app`;
  - `cluster3.startRes_intro` for the compactor part;
  - `wp_apply k8s_all.wp_Main`.

**GF.** Use `k8sGF`, which is `k8setcd3GF` moved and renamed: it has the `NaInvF` slot 11 that
porcupine needs. The compactor's triple is GF-polymorphic, so it applies unchanged.

**The statement.** The premises are the union of the two lists:

| | etcd3 partition (`Spec/.../etcd3/TopLevelRobustness.lean`, `_partition_robust.spec`) | compactor partition (`Spec/.../compactor/TopLevelRobustness.lean`, `_partition_robust.spec`) | `k8s_robust.spec` |
|---|---|---|---|
| instances | `k8setcd3.Assumptions`, cache, five k8s `Assumptions`, `DialWithBalancerBody`, `log.NewModel` | `compactor.Assumptions`, cache, `DialWithBalancerBody`, `log.NewModel` | `k8sall.Assumptions` (implies both packages'), cache, the five k8s ones, `DialWithBalancerBody`, `log.NewModel` |
| `Hctx`, `Hcec` | at `k8setcd3GF` | at `k8scompactorGF` | once, at `k8sGF` |
| cluster | `k, 1 ≤ k ≤ 1000, ids, ps, ctxs, boot, Hlen, k8s_etcd3N.BootFacts` | `id₁ id₂ id₃, ps, ctxs, boot, cluster3.BootFacts` | both, with primed names for the compactor's |
| ids | — | — | **new** `Hlow` (§2.3) |
| workload | `Haf Hbuq Hrf Hdbo`, the client bounds `Hc0 … Hmul` | `Haf Hbuq Hrf Hdbo` | once each, plus the client bounds |
| schedule | `steps, Hsteps` | `steps, Hsteps` | `steps₁, Hsteps₁, steps₂, Hsteps₂` |
| `HNs` | `k8setcd3Names` | `k8scompactorNames` (equal) | once |
| `HAs`, `HDs` | `k8setcd3NAddrs k`, `k8setcd3NDirs k` | `k8scompactorPAddrs`, `k8scompactorPDataDirs` | concatenations |
| `HEnv` | yes | yes | once |
| `Hprem` | `k8s_etcd3N.premises k n …` | `cluster3.premises clusterCfg n …` | two hypotheses, same `n`, at `k8sGF` |
| `Hafter` | — | `RealClock.After.spec` | yes |
| `Hfs`, `HWal` | `HWal` over `k8setcd3NDirs k` | `HWal` over `k8scompactorPDataDirs` | `Hfs` once; `HWal` over the concatenation |
| conclusion | `Robust [] [(k8setcd3PProgram …, σ)] g (2^28−1)` | `Robust [] [(k8scompactorPProgram steps, σ)] g (2^28−1)` | `Robust [] [(k8sProgram k clients ops watchers wops steps₁ steps₂, σ)] g (2^28−1)` |

**The premises combine.** The address and directory lists are disjoint for every 1 ≤ k ≤ 1000 (§2.1);
the receipt bound `n` is shared, and each triple only asks `receiptBound ≤ n + 1`; both thread bounds
are `≤ 2^28`; `srvLevels` is a fact about GF.

Files, following the layout:

- `Proof/.../k8s/all/TopLevelDefs.lean`: `k8sGF`, `k8sHeapAt`, `k8sProgram`, `k8sAddrs`, `k8sDirs`.
- `Spec/.../k8s/all/TopLevelRobustness.lean`: `k8s_robust.spec`.
- `Proof/.../k8s/all/TopLevelRobustness.lean`: `theorem k8s_robust` by `Robust.of_single`.
- `Proof/.../k8s/all/Results.lean`: `k8s_all_Main`, `k8s_safe` (the n-step form, the paper's name),
  and `#print axioms`.

### 3.4 Threads left running

Concurrently, the etcd3 goroutine's servers, bridges, partitioner, `holdToken`s and store goroutines
run alongside the compactor's, and both sets keep running after `Main` returns. Every such thread was
forked inside a driver's triple with its own WP, over that driver's resources and invariants, and the
frame keeps the other driver's resources out of reach. The adequacy theorem's "no thread stuck, none
panicked" covers them all, exactly as each driver's theorem covers its own threads today. `holdToken`
sleeps forever, which counts as reducible, not stuck; both drivers' theorems already rely on this.
Nothing new.

---

## 4. The existing separate theorems

**Recommendation (D3): retire them, keep the function triples.** The unified theorem is about another
program, so it cannot have the old theorems as corollaries; keeping them beside it would put two
top-level statements on the same workloads, which the no-twins rule forbids for closed theorems.

- **Go**: nothing changes. The drivers' `Main`/`MainCluster`/`MainPartition` stay as functions.
- **Stay**: the triples `k8setcd3_Main`, `_MainCluster`, `_MainPartition`, `k8s_compactor_Main` and
  `_MainPartition` in the two `Results.lean` files and `MainLinked.lean` files. They are triples of Go
  functions, and two of them are the unified proof's callees.
- **Go**: all five adequacy, safe and robust theorems of `etcd3`/`compactor`, meaning `Adequacy.lean`
  (both whole) and the `_safe` parts of both `Results.lean` files. Also both
  `TopLevelRobustness.lean` pairs and both `TopLevelDefs.lean` files, after `k8setcd3GF` moves to
  `k8s/all/TopLevelDefs.lean` as `k8sGF`.
- **Generated**: drop both drivers from `PROGRAMS`. This deletes their `PkgTable.lean`, about 2,080
  lines; check that each `InitLinked.lean` has no other importer, using `etc/importers.py`. Their
  `Init.lean` stays (`ROOTS`): the new table needs the drivers' package facts.
- **Trust base**:
  - new `etc/tcb-collections/k8s-all.txt`, roots `^Proof/.../k8s/all/(Results|Link)\.lean$`. Its
    baseline should be about the union, 597 axioms, plus the new program's initializer axioms if any;
    `--check --update` sets it.
  - `k8setcd3.txt` and `k8scompactor.txt` stay as triple collections; their baselines shrink by
    whatever only the adequacy reached.
  - `etc/tcb-baseline.txt` changes only if an axiom appears or disappears; the idutil docstring is not
    an axiom.
- **Paper (the user edits it)**: three rows become one, `k8s_safe`: "Kubernetes' etcd3 storage layer
  on k members under partitions, concurrently with Kubernetes' compactor run by 5 API servers on 3
  more members under partitions, for every pair of schedules". Model 617; Driver ≈ 676 + 43 + 114 +
  ~25; Axioms ≈ the union (`etc/theorem-loc.py k8s_safe` once the collection exists).

---

## 5. Stages, estimates, risks, STOPs

| Stage | Work | Lean lines | Builds |
|---|---|---|---|
| U0 Go | `examples/k8s/all` (module, Main, holdToken, the three tests), run under `systemd-run MemoryMax=32G`; `etc/goose.py` project `k8s-all` plus the pin tables; translate; `--check`; `featuregate-check` INSIDE | 0 (generated Code ~80) | goose only |
| U1 triple | `holdToken` spec+proof (~70, copied); `Main` spec (~90) and proof (~200); `gen-link --k8sall` (~60 generated) | ~360 | 1 incremental (new Link over both MainLinked) |
| U2 closed theorem | gen-init ROOTS/PROGRAMS (PkgTable ~1,100 generated); TopLevelDefs (~110); Adequacy (~320, including the two disjointness lemmas ~80); Results (~110); TopLevelRobustness spec (~110) and proof (~30) | ~680 | 1 incremental |
| U3 retire | delete the five closed theorems and the two PkgTables; move GF; tcb collections (`--check --update`); `etc/tier-check.py`, `api-check`, `gen-interface` if touched; STATUS; full timed build; `etc/gates.sh` | −~1,300 hand, −~2,100 generated | 1 full |

Total: about 1,040 new hand-written lines, mostly copied from `compactor/Adequacy.lean` and
`etcd3/Adequacy.lean`; one to two sessions.

**Risks**

- **R1, the step bound.** It is the reason for D1. Concurrency mitigates it, but neither form makes
  `Robust` cover a run longer than `2^28 − 1` steps. That is the existing limit, and the theorem's
  docstring should say so.
- **R2, the token bookkeeping in the closure.** The `wp_fork_tok_body` plus T₂ handoff has no exact
  precedent in the k8s proofs: `startCluster` uses `wp_fork_tok_self`, and the compactor uses
  `wp_fork` with `sync.join`. Estimate +1 day if Iris framing through the closure is awkward.
- **R3, instance synthesis.** `k8sall.Assumptions` has to imply both drivers' instance sets; the
  existing files already need `synthInstance.maxSize 4096`. Possibly an explicit `letI`.
- **R4, memory.** The new Link and Adequacy import both `MainLinked` cones. Each driver's adequacy is
  already heavy, and the union may be 1.5×. Use `build-slot.sh`; if a module hits its cap, split
  Adequacy (`AdequacyLinked`).
- **R5, the Go test.** k + 3 members plus both workloads in one process: run it at k = 3, never
  concurrently with the drivers' own tests (same fixed ports and directories).

**STOPs for the user**

1. **This Scope** (now): D1-D7 below.
2. **Before U2's Lean**: the text of `k8s_robust.spec`, which is a new closed statement, and the
   retirement of the five closed theorems (a closed-statement change).
3. **Trusted text**:
   - `TrustedCode/.../idutil.lean`'s faithfulness docstring, reworded to the process's members, with
     the premise `Hlow` (§2.3);
   - the new Go `Main`, part of what the theorem is about;
   - `featuregate-check` INSIDE, which extends the gate assumption's claim to the new program.
4. **No Go change to an existing driver.** If one turns out to be needed (it should not), that is a
   STOP of its own.
5. The land stop. The coordinator runs `etc/land.sh`.

---

## 6. Open decisions (recommendation in bold)

- **D1** Concurrent or sequential `Main`: **concurrent** (WaitGroup, fork with token handoff),
  because of the step bound (R1) and to match a real run. Sequential is about 80 proof lines less.
- **D2** Include the 1-member `Main`s (etcd3 with `MaxUnaryRetries: 1`; compactor's compaction-mode
  single member) as two more goroutines: **no**. They overlap the partition workloads, and including
  them adds two more boot-fact and premise families, four addresses and two directories to the
  statement. Their closed theorems retire; their triples stay.
- **D3** The old closed theorems: **retire all five**; keep the function triples (§4).
- **D4** One schedule shared by both clusters, or two: **two independent schedules** (`∀ steps₁
  steps₂`). That is stronger and costs nothing.
- **D5** Cross-cluster ids: **explicit premise `Hlow`, a Go test, and the idutil docstring reworded**
  (§2.3). Measured true for every k ≤ 1000.
- **D6** Names: package `examples/k8s/all` (`k8sall`), Lean namespace `k8s_all`, theorems
  `k8s_adequate` / **`k8s_safe`** / `k8s_robust`.
- **D7** Return value: **`Main` returns nothing**, conclusion `v = #()`. etcd3's `Ok`/`Unknown` adds
  nothing to "no panic".

---

## 7. Decisions (2026-11-20)

Approved by the user, 2026-11-20, via etcd-grove-03: **D1** concurrent `Main`; **D3** retire the five
separate closed theorems, keep the drivers' function triples; **D5** the premise `Hlow`, the Go test, and
the idutil docstring "members of the process". Decided by etcd-grove-03 as recommended: **D2** no
single-member Mains; **D4** two independent schedules; **D6** names `k8s_all` / `k8s_adequate` /
`k8s_safe` / `k8s_robust`; **D7** `Main` returns `#()`. Stops kept: the exact text of `k8s_robust.spec`
and `k8s_safe` before proving past them; any Go change to an existing driver; any further trusted-text
change; a refutation; the land stop (after an independent attack on the docstring change and `Hlow`).
