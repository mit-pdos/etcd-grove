# k8s-dist: the statement packet (K1) and the K6 interim-axiom packet (DRAFT, 2026-11-28)

Session KSTMT-1 (etcd-grove-03's brief), branch `k8s-dist-stmt/2026-11-28` off `lean` @ `766f9e4acb`. For approval
by coordinator-E (etcd_safe lead, Upamanyu's delegation) and Upamanyu. Drafts only: nothing under `Spec/` or
`Proof/` is changed, nothing was built. Sources: the plan (`git show 685a5160d5:notes/k8s-dist-lean-plan.md`,
§1, §2, §4), `notes/k8s-dist.md`, K4's result (`k8s-dist-k4/2026-11-27`, `notes/k8s-dist-k4.md`: `fullComplete`
closed), K5's client laws (`k8s-dist-k5/2026-11-27` @ a649b823b5, `Proof/k8s_io/apiserver/pkg/storage/etcd3/EtcdClient.lean`),
and the Go on `lean` (`examples/k8s/dist`, with G1-G10).

The proposed files: `notes/k8s-dist-statement/TopLevelRobustness.lean` (the `Spec` file, header included) and
`notes/k8s-dist-statement/TopLevelDefs.lean` (the defs it names, a sketch; the `sorry`s are K3's mechanical parts).

---

## Part 1. The statement (K1)

### 1.1 The statement

`Spec/github_com/mit_pdos/etcd_grove/examples/k8s/dist/TopLevelRobustness.lean`, namespace `k8s_dist`:

```lean
def k8s_robust_nocrash.spec : Prop :=
  ∀ [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [errors.Assumptions] [fmt.Assumptions]
    [server_sem : examples.etcd.dist.server.Assumptions]   -- the members, unchanged
    [client_sem : examples.etcd.dist.client.Assumptions]   -- AwaitCluster, Rotate, ConnectRetry, AwaitAccept, CallAll
    [k8s_sem : examples.k8s.dist.Assumptions]
    [rpctypes.Assumptions] [cache.v3.Assumptions] [log.NewModel]
    (d : Deployment)
    (boot : List LogEntry) (Hbf : BootFacts d.cluster boot) (Henv : EtcdEnv d.cluster)
    (σs σo σn : List state) (g : GlobalState)
    (Hσs : σs.length = d.cluster.members.length ∧ ∀ p ∈ d.cluster.members.zip σs, ServerStart p.1 p.2)
    (Hσo : σo.length = orchCount ∧ ∀ σ ∈ σo, ClientStart σ)
    (Hσn : σn.length = d.nodeCount ∧ ∀ σ ∈ σn, ClientStart σ)
    (HEnv : EtcdVerifyOff) (Hfips : crypto.fips140.GodebugFips140Off),
    Robust [] (machines d σs σo σn) g (threads := etcdThreads) (bound := etcdSteps)
```

Theorem name `k8s_safe_nocrash` (proof in `Proof/.../k8s/dist/TopLevelRobustness.lean`).

**The `Robust` instance.**

| Argument | Value |
|---|---|
| crashing machines | `[]` (no crash; `k8s_safe`, members crashing, is a one-line change once etcd_safe's D4b/D6 land) |
| stable machines | `machines d σs σo σn`: members `etcd_dist.serverProg d.cluster i` (etcd-dist's `server.MainDeployment(d.Cluster, i)`, the same expression as `etcd_safe_nocrash`'s); orchestrators `dist.Orchestrator(d, j)`, `j ∈ {0 store, 1 compactor}`; client machines `dist.NodeDeployment(d, n)`, `n < NodeCount(StoreW) + NodeCount(CompW)` (`Apiservers` store API server machines, then `CompactorMachines`: writer, own compactors, shared one) |
| extensions | `etcdNetExts` (`[idIssueExt, fsExt at etcdFsSem, netExt]`), unchanged |
| `threads` | `etcdThreads = 2^28` (etcd-dist's: the server's and clients' reader-slot pools) |
| `bound` | `etcdSteps = 2^48` (etcd-dist's: idutil's 48-bit suffix, mvcc's change count, auth's fuel; the highest the server's specs allow) |

**The deployment** (Go `dist.Deployment`, `deploy.go`, program code since G1): `Cluster` (an etcd-dist
`deployment.Deployment`, no workload of its own), `StoreW`, `CompW` (`Workload{Kind, Clients, Ops, Watchers, WOps,
Apiservers, Rounds}`), `StoreAddrs`, `CompAddrs`. One cluster; the store's keys are under `/registry/` (the driver's
prefix), the compactor's under its own keys (`compact_rev_key`, `/k8sdist-compactor/`): the two workloads share the
cluster's revisions, and the compactor compacts while the store serves. `dist.WellFormed(d)`: etcd-dist's
`WellFormed(d.Cluster)`; no auth, `Retention = 0` (etcd's compactor off: every compaction is a Kubernetes
compactor's), no etcd workload; store `Kind = Store`, counts ≥ 0, `1 ≤ Clients + Watchers < 2^31`,
`1 ≤ Apiservers ≤ Clients + Watchers`; compactor `Kind = Compactor`, `Rounds ≥ 1`; `AddrCount` addresses per workload,
each `AddrOk`, at most `MaxLen` bytes, distinct, none a member's. Every orchestrator and client machine checks it first
and returns if it fails; the members check etcd-dist's `WellFormed` of the cluster.

**What panics** (Go `panic`, every one):

| Machine | Panic | Property |
|---|---|---|
| store orchestrator (`RunStore`, `store.go:145`) | "a compacted error on an operation at no old revision" | etcd answers `ErrCompacted` only to a read at an explicit old revision (`PastRead`) or one the store pinned (`PinnedRead`: a paged List's later pages, any watch) |
| store orchestrator (`store.go:174`) | "porcupine found the store's history not linearizable" | the store's history linearizes in `SharedModel` (the driver's `Model` with foreign revisions and compacted reads; `CheckShared`: lazy, then eager, then full mode, full's `Illegal` final) |
| store orchestrator (`store.go:193`) | "Kubernetes' checker rejected the store's history" | Kubernetes' own checker accepts it, where it applies (`FailureFree`, no compacted error, every Raw carried, `NoForeign`) |
| store API server machine (`StoreNode`, `store.go:80`) | "the API server's store could not be made" | `NewStoreOnly` succeeds |
| compactor orchestrator (`RunCompactor` → `comp.CheckLog`) | `CheckLog`'s comparisons | each API server's compactor revision never decreases and never runs ahead of the cluster |

Timeouts (`CheckTimeout`, porcupine's or the checker's) return: a timed-out run checks nothing (the header says so).
No exit on the programs' own path: `grep` of `examples/k8s/{dist,etcd3,compactor}` (non-test) finds no `os.Exit`,
`log.Fatal`, `klog.Fatal`; `etc/exit-check.py` covers them once the real `TopLevelDefs.lean` exists (K12).

### 1.2 In plain words

**A reader can conclude:** for every size of cluster and workload the Go check accepts, and under every network
fault (delay, cut, refused dial, partition), with no machine crashing: Kubernetes' etcd3 storage, each API server on
its own machine with its own etcd client, serving a concurrent mix of Get/List (paged or not, at any resource version
and match)/Create/Update/Delete/Watch (watch-lists, bookmarks, progress) gives a history that linearizes against the
driver's model of the store, even though another tenant (the compactor workload) writes and compacts the same cluster
concurrently; etcd's "compacted" error reaches the store only on reads at an old or pinned revision; and Kubernetes'
compactor, own and shared, across several rounds, never moves its compaction revision back or ahead of the cluster.

**It does not cover:** crashes (members or clients; `k8s_safe` later); auth; etcd's own compactor; the DaemonSet
controller and authz (no etcd); a timed-out check; executions past `2^48` steps or with `2^28` live threads on a machine
(the run is covered up to there); the binaries' JSON parsing (the trusted gap, as etcd_safe); Kubernetes' checker on
most runs (one cluster almost always has foreign revisions, and the checker numbers revisions itself, so it is skipped;
porcupine on `SharedModel` is the check that always runs); anything the `_dist` client axioms assume (Part 2), until
#24 S2 proves the client.

**Against `k8s_all` (`k8s_robust_single_process`):**

| | `k8s_all` | `k8s_safe_nocrash` |
|---|---|---|
| Machines | one process | members, 2 orchestrators, `Apiservers + CompactorMachines` client machines; none crashes |
| Clusters | two (store's `k₁`, compactor's `k₂`), in-process | **one**, shared, over the net extension |
| Faults | partition schedules the program draws | every fault of the net extension |
| Store check | porcupine on `Model`, then Kubernetes' checker | porcupine on `SharedModel` (foreign revisions, compacted reads), Kubernetes' checker where it applies, the compacted-error panic (new) |
| Compactor | 5 API servers and a writer, one round | the same split over machines, `Rounds ≥ 1` rounds |
| Config | program arguments, `ParamsOk` in Go | `d : Deployment`, `WellFormed` in Go |
| Function-contract premises | `Hafter` (`RealClock.After`), `Hprem₁`, `Hprem₂` (Iris premise bundles) | none |
| Other premises | `Hlow`, `HAs`, `HDs`, `HWal`, `Hfs`, the four opaque env premises | etcd_safe's: `BootFacts`, `EtcdEnv`, `ServerStart`, `ClientStart`, `EtcdVerifyOff`, fips140 off |
| Trust | in-process client proved | `_dist` client axioms (+ Part 2's arms) |

**Against `etcd_safe_nocrash`:** the same members' program, premises (at `d.cluster`), extensions and bounds; the
client side is Kubernetes' instead of etcd-dist's workloads. The cluster is in "clients compacting" mode:
`v3compactor.bootCfg`'s `ret = 0` arm with the KV at `cmp = true`, `cret = 0` (K12 picks this, not etcd-dist's
`cmpOf`, which gives `(false, 0)` at `Retention = 0`; `bootCfg` allows it, "Kubernetes' deployment"). It rests on
etcd_safe's `_dist` axioms plus Part 2's error arms. It implies nothing about etcd's own workloads and they nothing
about it; `etcd_safe_nocrash` is a premise-for-premise template, not a lemma.

### 1.3 The plan's open choices (§1.3), resolved

| # | Choice | Resolution |
|---|---|---|
| 1 | One cluster or two | **One** (K4: `fullComplete` proved, no `sorry`, standard axioms only, with G7-G10, which are on `lean`: 152e1a4634, 79ce313b20). The store's invariant drops `compacted = 0`/`OneChange`; K8 carries that. |
| 2 | `Apiservers` | A deployment parameter, any `1..Clients+Watchers` (`WellFormed`); the proof is per API server. |
| 3 | Compactor `Rounds` | A parameter, `≥ 1`. Fallback if K11 cannot handle the shared compactor's restart: `WellFormed` fixes `Rounds = 1` (a Go change; the statement text is unchanged). |
| 4 | Kubernetes' checker | Covered wherever `RunStore` runs it; the header says it rarely applies on one cluster. |
| 5 | DaemonSet, authz | Out (no etcd; not in Go). |
| 6 | Deployment carries addresses, checked by every program | Done in Go (G1, 4c98d57bf5): `Deployment`, `WellFormed`, `Orchestrator`, `NodeDeployment` are program code. No pure premise on `d`. |
| 7 | Name | `k8s_safe_nocrash` / `k8s_robust_nocrash.spec`, namespace `k8s_dist`. |

### 1.4 The robustness skill's checklist

1. **Every premise and class, unfolded and classified.**

   | Binder | Kind | Verdict |
   |---|---|---|
   | `GoGlobalContext`, `GoLocalContext`, `go.Semantics` | framework | allowed |
   | `errors`/`fmt`/`rpctypes`/`cache.v3` `Assumptions`, `server`/`client` (etcd-dist) `Assumptions`, `k8s.dist.Assumptions` | package assumptions of translations | allowed, trusted (listed). Open (K3): whether `k8s.dist.Assumptions` bundles its closure's classes (`k8s_all` needed only `k8s.all.Assumptions` and `cache.v3`); if not, the missing ones are added as binders |
   | `log.NewModel` | a name's model (etcd_safe's, review F7) | allowed, trusted |
   | `d` | the deployment | not a premise: checked in Go |
   | `boot`, `Hbf : BootFacts d.cluster boot` | pure, bootstrap's log of the peers/contexts Go computes from `d.cluster` | etcd_safe's, approved; unchanged |
   | `Henv : EtcdEnv d.cluster` | environment/workload, opaque (`authRecordsFit`, `backendUnderQuota`, `grpcRepliesFit`, `diskOk`, `leasePeersOk`, `noExpiry` vacuous here, `peerRequests` placeholder) | etcd_safe's, with its open items; the k8s workload must also meet `backendUnderQuota`/`grpcRepliesFit` (opaque, the same Props; K12 to confirm no k8s-specific one is needed) |
   | `Hσs` (`ServerStart`), `Hσo`/`Hσn` (`ClientStart`) | start state | allowed; etcd_safe's |
   | `HEnv : EtcdVerifyOff`, `Hfips` | environment | allowed; etcd_safe's |

   No pure fact the program could check; no function contract (`k8s_all`'s `Hafter` becomes an axiom in
   `Proof/k8s_io/utils/clock/RealClock__After.lean` or is proved; `Hprem₁`/`Hprem₂` are gone); no Iris assumption.
2. **Bounds:** `threads := etcdThreads`, `bound := etcdSteps`, named constants. `etcdSteps` is `2^48`, not `2^63 - 1`:
   the highest the server's specs allow (three lifetime counters), as etcd_safe. Not `threads := bound + 1`. **Pass.**
3. **No bare literals** in the statement. `orchCount` and `CompactorMachines` are named. **Pass.**
4. **Non-vacuity.**
   - Go: `TestWellFormed` (50 random deployments pass, malformed ones fail); `TestDist` runs the real path on network
     namespaces (it also crashes members, more than the statement needs). **Gap:** no test shows Kubernetes' checker
     reached on one cluster (`RealCheck` needs `NoForeign`); a `TestDist` variant with the compactor's writer idle
     until the store ends, or a seeded run asserting "model and Kubernetes' checker", would show it. Without it the
     checker branch may be dead code in practice (the theorem still covers it).
   - Lean: the premises are etcd_safe_nocrash's at `d.cluster`; its witness (`Proof/.../etcd/dist/PremiseWitness.lean`)
     is to be instantiated at a k8s deployment (K12). **Pending.**
   - Concrete instance: K12, as etcd-dist's `TopLevelWitness.lean`.
5. **Extensions** fixed (`etcdNetExts`), assumptions in the header (`etcdFsSem`). **Pass.**
6. **Trust** listed in the header (translations, package assumptions, extensions, `tcb-collections/k8s-dist.txt`).
   **Pass** (the collection is K12's).
7. **Header** concise, technical, no history. **Pass.**

**No hidden function specs:** none of the binders unfolds to a triple, WP or entailment: `EtcdEnv`'s fields are pure
opaque Props, `BootFacts` is pure, `ServerStart`/`ClientStart` are file-system state predicates; the classes are
generated `Assumptions` (field layouts, names' models). **Every checked property is a Go panic** (table in §1.1); the
statement has no Lean trace property.

---

## Part 2. The K6 interim-axiom packet (GAP-1, GAP-2)

### 2.0 What the k8s proofs need, through K5's laws

K5 (`EtcdClient.lean`, `K8sEtcd.Laws`) states what the k8s library needs of its client: `get`/`list`
(C1, `kubernetes.Client.{Get,List}`) end in `kvErr`'s three parts plus `K.live → rangeErrSound`; `optimisticPut`/
`optimisticDelete` in `kvErr`; `kvGet` (C2) in `kvErr`; `casCommit` (C3) in `kvErr`. The k8s compactor's
`Compact` (and its `Get` of the key) still goes through `clientKvOk` (`CompactorDefs.lean:83`, in-process `isKv`),
whose `Compact` spec (`Compact.lean:111`) ends in `kvErr`. K7 builds the dist instance of these from the `_dist`
axioms; the axioms below are what that needs beyond today's.

Today's error arms: `KV_Get_dist` `⌜err ≠ nil ∧ resp = null⌝ ∗ statusErrOk err`
(`Spec/.../etcd/dist/KVGetDist.lean:39`; `clientErr`, `errCellOk` left out on purpose:
`notes/axiom-review/kv-get-dist-statuserr.md`); `Txn_Commit_dist` and `KV_Compact_dist` `⌜err ≠ nil ∧ resp = null⌝`
only. The in-process specs (`kv.Get.spec`, `txn.Commit.spec`, `kv.Compact.spec`) all end in `kvErr err`.

### 2.1 GAP-1: `KV_Get_dist`'s error arm

**Proposed:** a new axiom `KV_GetE_dist` (a new file pair beside `KVGetDist.lean`; `KV_Get_dist` stays for its
current users, and `KV_GetE_dist` implies it), `KV_Get_dist.spec` with the error arm

```lean
(⌜err ≠ GoInterface.nil ∧ resp = null⌝ ∗ kvErr err ∗
  rangeErrDist (rangeWireOf (opGetModel key opts)) Q err)
```

over a new dist definition (in `Proof/.../etcd/dist/KVClientDist.lean` or a defs file beside it), mirroring
`client.rangeErrOut`/`rangeErrΨ` (`KVService.lean:1248-1272`) at the view `Γ` instead of the members:

```lean
/-- What a failed range tells its caller, across machines: for a request the server's check accepts,
an error with mvcc's future-revision description means the read's update fired at a state below the
asked revision; one with the compacted description means the request asked an explicit revision
(a read at revision 0, the latest, is never compacted); or it is the context's error. -/
def rangeErrDist (o : OpFull) (Q : KVState → IProp GF) (err : GoInterface) : IProp GF :=
  iprop(⌜v3rpc.rangeCheck o = none⌝ →
    ((∃ d : GoString, descIs err d ∗ □ (
        (⌜d = futureRevDesc⌝ → ∃ σ : KVState, □ Q σ ∗ ⌜σ.rev < sint.nat o.base.rev⌝) ∧
        (⌜d = compactedDesc⌝ → ⌜0 < sint.Z o.base.rev⌝))) ∨
     ⌜∃ e : GoInterfaceOk, err = GoInterface.ok e ∧ ctxErrShape e⌝))
```

Its three parts:

| Part | Why k8s needs it | Go evidence (etcd fork `d26dd5da6f`, the pin; same text at `df6af0c36a`) | Claims more than today? |
|---|---|---|---|
| (a) `kvErr` = `clientErr ∗ statusErrOk ∗ errCellOk` | the store's `unkErr` (`Store.lean:166-175`); `errors.Is`/`As` on client errors; `errDeleteRejected` told apart from etcd's errors (`kvErr_ne`); K5's `get`/`list`/`kvGet` laws | every error `kv.Get` returns is `ContextError(ctx, err)` (`client/v3/kv.go`, `client.go:610`): `rpctypes.Error` (`api/v3rpc/rpctypes/error.go:256`: an `EtcdError{code, desc}` for a known description, else the status error unchanged), or `ctx.Err()` on `Canceled`/`DeadlineExceeded`. The statusErr review's (c) found no non-leaf on the client path in this configuration (no credentials but etcd's token bundle, no retry policy) and says the same evidence makes `clientErr` hold | **Yes**: `clientErr` and `errCellOk` are new at dist (proved in-process). The review of (a) must also check `errCellOk`'s message list (`clientErrMsgs`) against the dist path's own `*errorString`s (context errors, the net extension's dial errors as grpc wraps them) |
| (b) future half | K5's `rangeErrSound` (`kubernetes/Defs.lean:315`); the store's `ErrFutureRev` handling (a List at a too-new resource version) | mvcc `rangeKeys` (`server/storage/mvcc/kvstore_txn.go:73-77`): `rev > curRev → ErrFutureRev`, mapped by `togRPCError` (`v3rpc/util.go:46`) to `ErrGRPCFutureRev` ("etcdserver: mvcc: required revision is a future revision", `rpctypes/error.go:33`), back to `rpctypes.ErrFutureRev` by `rpctypes.Error` | **Yes**: new at dist. In-process derivable (`rangeErrΨ`'s future arm, `rangeErrReply … rangeFutureAt`, as `client_range_any` gives it today) |
| (c) compacted half | the store orchestrator's "compacted at no old revision" panic: K8 shows every List whose etcd range is at revision 0 cannot get `ErrCompacted` (`interpretListError`'s `err == etcdrpc.ErrCompacted`, apiserver fork `ef23adaea1b3`, `pkg/storage/etcd3/errors.go:66-73`, is the only source of `ResourceExpired` the orchestrator's `compacted` sees on a List) | `rangeKeys` (`kvstore_txn.go:78-83`): `rev <= 0 → rev = curRev`, then `rev < compactMainRev → ErrCompacted`; `compactMainRev ≤ currentRev` always: `updateCompactRev` (`kvstore.go:197-211`) refuses `rev > currentRev` with `ErrFutureRev`. So a read at revision 0 is never compacted. `ErrGRPCCompacted` = `status.Error(OutOfRange, "etcdserver: mvcc: required revision has been compacted")` (`rpctypes/error.go:32`), `rpctypes.ErrCompacted = Error(ErrGRPCCompacted)` (`:177`), the client's `err == etcdrpc.ErrCompacted` holds of the `EtcdError` `rpctypes.Error` rebuilds | **Yes**: new at dist **and** new at the k8s client level in-process (today's `rangeErrSound` has the future half only). Derivation in-process: §2.4 |

**The liveness condition.** In-process the range soundness holds only on refusal-free members (K5's `K.live`,
`∀ x ∈ ms, noRefusalAt x.addr`, needed by `rangeErrΨ_of_ifc`). Across machines a refused dial is a fault of the net
extension, so a conditional claim would leave K8's panic unprovable: **the dist instance needs `K.live := True`**, i.e.
`rangeErrDist` unconditionally. Go: a refused dial gives grpc's `Unavailable` with a transport text, which
`rpctypes.Error` does not recognize (not in `errStringToError`), so its description is neither of the two; the claim
is true in Go, but it is stronger than any proved in-process statement. **Decision for the coordinator** (doubt D1).

### 2.2 GAP-2: `Txn_Commit_dist`'s error arm

**Proposed:** the error arm `⌜err ≠ GoInterface.nil ∧ resp = null⌝ ∗ kvErr err` (a change to the existing axiom; its
current users only read `err ≠ nil` and are unaffected).

- **Why:** K5's `optimisticPut`/`optimisticDelete` (the store's writes, `unkErr`) and `casCommit` (the compactor's
  round: `klog.Errorf("…%v", err)` needs `statusErrOk` through `fmtArgOk_of_statusErrOk`, `Compact.lean:362-364`) end in
  `kvErr`.
- **Go:** `(*txn).Commit` (`client/v3/txn.go:138-148`): `ContextError(txn.ctx, err)`, the same path as (a). No
  compacted half: the store's and compactor's transactions read at revision 0 (`txnModelIn`), and the orchestrator's
  `compacted` reads no write's error (a write's error is never `ResourceExpired`).
- **Claims more:** yes, all of `kvErr` is new at dist (today: nothing). Proved in-process (`txn.Commit.spec`).

### 2.3 GAP-2: `KV_Compact_dist`'s error arm

**Proposed:** the error arm `⌜err ≠ GoInterface.nil ∧ resp = null⌝ ∗ kvErr err` (a change to the existing axiom).

- **Why:** the k8s compactor's `Compact` (`compact.go:247`, fork `ef23adaea1b3`) returns the error to
  `runCompactLoop`, which logs it with `%v` (`compact.go:207`); `Compact.lean`'s spec states `kvErr`. Minimal would be
  `statusErrOk` (all the logging needs); `kvErr` is proposed for uniformity with the in-process spec and the other arms.
  K5 has no `compact` law yet (the compactor's `Compact` goes through `clientKvOk`'s in-process `isKv`): **K7 must add
  one** (doubt D3).
- **Go:** `(*kv).Compact` (`client/v3/kv.go:197-202`): `ContextError(ctx, err)`. Real errors: `ErrCompacted` when
  `rev ≤ compactMainRev` (`kvstore.go:199-204`; on one cluster with own and shared compactors this happens: another
  API server's compactor got there first), `ErrFutureRev` (`rev > currentRev`; the axiom's `kvRevLbZ` precondition
  and raft's ordering exclude it), and transport/context errors.
- **Claims more:** yes (today: nothing). Proved in-process (`kv.Compact.spec`).

### 2.4 The in-process half: what is proved, not assumed

1. **`rangeErrSound`'s compacted conjunct** (`Proof/go_etcd_io/etcd/client/v3/kubernetes/Defs.lean:315`): add
   `⌜d = compactedDesc⌝ -∗ ⌜EtcdError shape⌝ -∗ ⌜0 < sint.Z o⌝` beside the future one. Prove it in
   `kubernetes/Client__Get.lean` and `Client__List.lean` from `client.rangeErrOut`'s `rangeErrΨ` compacted arm:
   `rangeErrReply … (rangeCompactedAt o)` gives `o.rev ≤ cur ∧ rangeRev cur o.rev < crev` with `□ E.Cp crev`. If
   `o.rev = 0` then `rangeRev cur 0 = cur`, so `cur < crev`: a contradiction **only with `crev ≤ cur`**.
   `E.Cp = kvCpOk γk` (`InvRequest.lean:1519-1528`) gives `crev = -1` or a `kvCmpPermit` (`crev + cret` reached by
   the *cluster*), which does not bound `crev` by *this member's* log. **Risk:** the lemma may need `crev ≤ log.length
   - 1` added to `rangeErrReply` (a server-side strengthening of `etcdRangeSpecE`, proved from the store's invariant
   `compactMainRev ≤ currentRev`, i.e. `updateCompactRev`'s refusal above `currentRev`; no axiom). K6's first task is
   to settle this; if it fails, the compacted half is not derivable and S2 could not retire (c).
2. **K5's laws** `get`/`list` gain the conjunct through `rangeErrSound`; the in-process instance (`inProcEtcd`) gets it
   from 1. No library proof changes (a stronger post).
3. **`K7`** proves the dist instance of the laws from `KV_GetE_dist` (`rangeErrDist` ⇒ `rangeErrSound` at
   `Q R m := …`, `K.live := True`), the changed `Txn_Commit_dist`, and `KV_Compact_dist` through the new `compact` law.
4. **K8** uses (c) to show the "compacted at no old revision" panic unreachable: the store's Get, writes and unpaged
   List at no past revision send revision 0 (K8's own argument about the k8s store: `GetList`'s `withRev` is 0 unless
   `Exact` or a continue token, which `PastRead`/`PinnedRead` cover).

### 2.5 Review and approval

Each changed or new axiom: rule #8 (Upamanyu's OK) and an `axiom`-skill review (try to build a Go program over
real grpc-go and etcd whose call returns an error that violates the arm). The review of (a) can extend
`notes/axiom-review/kv-get-dist-statuserr.md` (its 44 cases) to `clientErr`/`errCellOk`; (b)/(c) need a run where the
real server answers `ErrFutureRev`/`ErrCompacted` across a network (and a refused dial, for `K.live := True`).

### 2.6 Rework risk: #24 S2

S2 replaces the per-function `_dist` axioms by one client spec proved over the net extension. Every arm proposed here is
the in-process statement (`kvErr`, `rangeErrΨ`'s two halves) at `Γ`, so S2 proves them the way the in-process proofs
do, with two exceptions it must cover: the compacted half's server-side fact (§2.4 item 1) and `K.live := True`
(refusals across machines). K5's abstraction keeps the swap local: S2 re-proves the dist instance (K7) only; the 550
modules of the k8s cone see `k8sClient`, not the axioms. If S2's single spec states errors differently (e.g. one
`clientErrOut` predicate), `rangeErrDist` becomes a lemma over it and K7 changes, nothing above it.

---

## Doubts for the coordinator

- **D1 (`K.live := True`).** The dist range-error soundness must be unconditional (refused dials are faults), which
  no in-process statement claims. Go says it is true. Approve the stronger claim, or ask S2 for it first.
- **D2 (the compacted half's derivation).** In-process, `0 < o` from `rangeCompactedAt` needs `crev ≤` the member's
  log, which `rangeErrReply` may not state; a server-side strengthening (proved) may be needed. Settle before the
  axiom is approved, so (c) is known to be S2-provable.
- **D3 (K5 has no `compact` law).** The k8s compactor's `Compact` still uses the in-process `clientKvOk`/`isKv`; K7
  must add a `compact` law (and the key's `Get` through `kvGet`) or the dist instance cannot be built.
- **D4 (Kubernetes' checker non-vacuity).** No Go test shows it reached on one cluster. Ask for a test, or accept
  that the header says it rarely applies.
- **D5 (package classes).** Whether `k8s.dist.Assumptions` bundles its closure's classes (K3 decides the binder list;
  the statement's shape does not change).
- **D6 (`EtcdEnv` with a k8s workload).** `backendUnderQuota` and `grpcRepliesFit` are opaque workload premises,
  carried over at `d.cluster`; their eventual discharge must cover the k8s workload's writes and replies too.
