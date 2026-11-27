# k8s-dist, Lean side: the plan (K8SD-0 scope, 2026-11-27, DRAFT for the coordinator)

Scoping session K8SD-0 (etcd-grove-03's brief), branch `k8s-dist-scope/2026-11-27` off `lean` @ `bc8f931ab5`.
Read-only on code: nothing built, no Lean edited. The Go side is `notes/k8s-dist.md` (`examples/k8s/dist`,
2026-11-22, one cluster). The model to follow is etcd-dist (`notes/etcd-dist-plan.md`, `etcd-dist-f7-fork.md`):
a no-crash statement first (`etcd_safe_nocrash`), proved over interim per-function client axioms
(`etcd_dist.*_dist`, `etcd_dist.view.*`), which #24 S2's single client spec retires later.

## 1. The statement

### 1.1 Draft

`Spec/github_com/mit_pdos/etcd_grove/examples/k8s/dist/TopLevelRobustness.lean`, namespace `k8s_dist`, theorem
`k8s_safe_nocrash` (spec `k8s_robust_nocrash.spec`), modeled on `etcd_robust_nocrash.spec`
(`Spec/.../examples/etcd/dist/TopLevelRobustness.lean:127`):

```lean
def k8s_robust_nocrash.spec : Prop :=
  ∀ [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [errors.Assumptions] [fmt.Assumptions]
    [server_sem : examples.etcd.dist.server.Assumptions]     -- the members: etcd-dist's server, unchanged
    [k8s_sem : examples.k8s.dist.Assumptions]                -- the new project's package assumptions
    [rpctypes.Assumptions] [cache.v3.Assumptions] [log.NewModel]
    (d : Deployment)          -- Go's dist.Deployment: cluster (an etcd_dist.Deployment, no workloads),
                              -- StoreW, CompW, and (new, G1) the client machines' addresses
    (boot : List LogEntry) (Hbf : etcd_dist.BootFacts d.cluster boot)
    (Henv : etcd_dist.EtcdEnv d.cluster)
    (σs σo σn : List state) (g : GlobalState)
    (Hσs : σs.length = d.cluster.members.length ∧ ∀ p ∈ d.cluster.members.zip σs, ServerStart p.1 p.2)
    (Hσo : σo.length = 2 ∧ ∀ σ ∈ σo, ClientStart σ)            -- orch-store, orch-compactor
    (Hσn : σn.length = d.nodeList.length ∧ ∀ σ ∈ σn, ClientStart σ)  -- store-node-a, compactor-node-0..4
    (HEnv : EtcdVerifyOff) (Hfips : crypto.fips140.GodebugFips140Off),
    Robust [] (machines d σs σo σn) g (threads := etcdThreads) (bound := etcdSteps)
```

- **Machines** (`Proof/.../k8s/dist/TopLevelDefs.lean`, as etcd-dist's `TopLevelDefs.lean:201-238`): every
  member runs etcd-dist's `server.MainDeployment(d.cluster, i)` (the same expression as etcd_safe's
  `serverProg`); the two orchestrators run `dist.Orchestrator(d, j)` and the client machines run
  `dist.NodeDeployment(d, n)`. Both are new Go entry points (G1). Each checks `WellFormed(d)` first and
  returns if it fails, then calls `MainReady`/`NodeMain`.
- **Which crash:** none (`Robust []`). The crash version (`k8s_safe`, members in the crashing list) waits for
  etcd_safe's D4b/D6 (`etcd-dist-plan.md` §12). It is a one-line change of the statement once those land.
- **Bounds:** etcd-dist's named constants, `etcdThreads = 2^28` and `etcdSteps = 2^48`
  (`TopLevelDefs.lean:294,303`; the same caps as `k8s_all`'s literals). The k8s side adds no counter that
  needs a lower cap; K8 checks this (the store's revisions are the cluster's, so they live under mvcc's
  `2^48` cap).
- **WellFormed** (Go `dist.WellFormed`, today in `deploy_test.go:34`): etcd-dist's `WellFormed` on the
  cluster, with no auth, no etcd compactor (`Retention = 0`) and no etcd workload; the store's bounds
  (`0 < clients + watchers < 2^31`, `1 ≤ Apiservers ≤ clients + watchers`); `Rounds ≥ 1`. G1 adds the
  addresses' checks (`addrOk`, all distinct, none a member's).
- **What panics** (the property, in Go):
  - `orch-store`: porcupine's `Illegal` on `SharedModel` in the full mode (`store.go` `RunStore`, via
    `CheckShared`); Kubernetes' checker `Illegal` (only on a history that is failure-free, has no compacted
    error, kept its Raw and shows no foreign revision); a compacted error on an operation at no old revision
    (neither `PastRead` nor `PinnedRead`).
  - `store-node-a`: "the API server's store could not be made" (`store.go:79`).
  - `orch-compactor`: `CheckLog`'s comparisons (each API server's compactor revision never decreases and
    never runs ahead of the cluster).
  - A porcupine timeout or a checker timeout (`CheckTimeout`) is a return, so a safe run. The header must say
    that a timed-out run checks nothing.
- **Premises:** exactly etcd_safe_nocrash's (`BootFacts`, `EtcdEnv`, `ServerStart`, `ClientStart`,
  `EtcdVerifyOff`, fips140 off), at `d.cluster`. `k8s_all`'s other premises go, as the skill requires
  (`.claude/skills/robustness/SKILL.md`, checklist 1):
  - `Hafter`, `RealClock.After`'s contract: a function contract as a premise (`k8s/all/TopLevelRobustness.lean:94`).
    It becomes an axiom in `Proof/k8s_io/utils/clock/RealClock__After.lean`, or is proved.
  - `Hprem₁`/`Hprem₂`, Iris premise bundles: gone. The members are etcd-dist's, whose contracts are
    per-function axioms.
  - `Hlow`: etcd-dist's `WellFormed` keeps the ids apart.
  - `HAs`, `HDs`, `HWal`, `ParamsOk`: covered by `Robust`'s fresh start, `ServerStart` and `WellFormed`.
- **Extensions:** `etcdNetExts` (`[idIssueExt, fsExt at etcdFsSem, netExt]`), unchanged.

### 1.2 Against `k8s_all` (`k8s_robust_single_process.spec`, `Spec/.../k8s/all/TopLevelRobustness.lean:88`)

| | `k8s_all` (in-process) | `k8s_safe_nocrash` (draft) |
|---|---|---|
| Machines | one process, never crashes | members, 2 orchestrators, `Apiservers + 5` client machines; none crashes |
| Clusters | two (`k₁` store, `k₂` compactor) | **one**, shared (k8s-dist.md "One cluster") |
| Store check | porcupine on `Model` + Kubernetes' checker | porcupine on `SharedModel` (foreign revisions, compacted errors) + Kubernetes' checker where it applies |
| Compactor | 5 API servers + writer, one round | the same split over machines, `Rounds` rounds |
| Config | program args `k₁ k₂ clients ops watchers wops n₁ n₂`, `ParamsOk` in Go | `d : Deployment`, `WellFormed` in Go |
| Faults | partition schedules drawn by the program | every fault of the net extension |
| Function-contract premises | `Hafter`, `Hprem₁`, `Hprem₂` | none (axioms in their files) |

### 1.3 Statement choices left open (`notes/k8s-dist.md`, "Open decisions", line 249, plus new ones)

1. **One cluster or two** (k8s-dist.md #6). The Go test has one cluster, by the user's decision. `k8s_all` has
   two. This choice decides most of the cost (§4):
   - With one cluster, the store's invariant loses `compacted = 0` and `OneChange`
     (`Proof/.../k8s/etcd3/Inv.lean:960`), and the check is `SharedModel`, a new 969-line Go model
     (`storecopy/export.go`).
   - With two clusters the in-process store proof carries over almost unchanged, but that program is not the
     one the user chose to test.
   - **Recommendation:** target one cluster. Run K4 (§4) first: it decides whether that is feasible. Fall back
     to two clusters (a Go deployment change plus the driver's `Model` on a cluster the store owns) only if K4
     fails.
2. **`Apiservers`** (#2): keep it random (any `1..clients+watchers`). The theorem covers every value, and the
   proof is the same per API server.
3. **Compactor `Rounds`** (#3): keep it a parameter (`≥ 1`). The risk is that the shared compactor
   (`StartCompactorPerEndpoint`) is removed and restarted each round, while the in-process proof has one
   round. Fallback: `WellFormed` fixes `Rounds = 1`.
4. **Kubernetes' checker** (#4): the statement covers it wherever the program runs it. It runs rarely on one
   cluster, and the header must say so.
5. **DaemonSet, authz** (#1): out of scope, as in Go.
6. **New: the deployment carries the addresses and is checked by every program** (G1). Today `WellFormed` is
   test-only and the addresses are run-time `Args`. Without this the statement would need pure premises.
7. **New: name.** `k8s_safe_nocrash` / `k8s_robust_nocrash.spec`, following `etcd_safe_nocrash`.

## 2. Dependencies: the client specs

### 2.1 Today (in-process)

`k8s_all`'s store and compactor rest on clientv3's specs **proved over the in-process server registry**.
`kubernetes.Client.{Get,List,OptimisticPut,OptimisticDelete}` (`Spec/go_etcd_io/etcd/client/v3/kubernetes/`)
and `watcher.Watch`, `kv.Txn`/`txn.If/Then/Else/Commit`, `kv.Compact` and `New` are all stated over `isNewClient
cl (ms.map SrvAt.addr) V ∗ [∗list] x ∈ ms, kvRegsAt x` and per-member read updates `kvReadAu x.γr.kv`
(e.g. `kubernetes/Client__Get.lean:56-77`). The k8s storage library bakes that shape in:

- `StoreCfg` holds `ms : List SrvAt` and `V : WEnv` (`Proof/k8s_io/apiserver/pkg/storage/etcd3/Store.lean:67-86`).
- 16 library files take these client specs as callees.
- There are about 80 mentions of `ms`/`kvRegsAt`/`isClientWatcher`/`isNewClient` (36 in the library, 44 in
  `examples/k8s/{etcd3,compactor}`).
- Error arms:
  - Client errors are `kvErr` = `clientErr ∗ statusErrOk ∗ errCellOk` (`InvKVConn.lean:1211`). The store's
    `unkErr` needs all three (`Store.lean:166-175`).
  - A range error also carries `k8s.rangeErrSound`, the future-revision half
    (`kubernetes/Defs.lean:315`).

### 2.2 The dist axioms they would use, call by call

| k8s call (who) | dist axiom | Covered? |
|---|---|---|
| `kv.Get` from `Client.Get`/`List`/`GetCurrentResourceVersion` (store), the compactor's reads, `AwaitCluster` | `KV_Get_dist` | success post: yes. **Error arm: GAP-1** |
| `Txn().If(ModRevision=)/Then(Put\|Delete)/Else(Get).Commit()` (`OptimisticPut`/`Delete`), `If(Version=)/Then(Put)/Else(Get)` (k8s compactor) | `Txn_Commit_dist` (auth off; `plain`, `txnModelIn`: gets at rev 0) | shapes: yes. **Error arm: GAP-2** |
| `Watch(key, WithRev, WithPrevKV, WithPrefix, WithProgressNotify)` (store watches) | `Watch_dist` (`isRangeWatchP`, `rev ≥ 1`, compaction through `cmpOkOf`) | yes (rev ≥ 1: the store watches from rv+1) |
| `RequestProgress` (watch-list/progress paths) | `RequestProgress_dist` | yes |
| `Compact(rev)` (k8s compactor) | `KV_Compact_dist` (`Γ.kv.cmp = true`, `kvRevLbZ Γ.kv (rev + cret)`) | yes at `cmp = true`, `cret = 0` (as the in-process compactor cluster, `compactor/ClusterN.lean:111`). **Error arm: GAP-2** |
| `Put` (`SeedShared`, the compactor's writer) | `KV_Put_dist` | yes |
| `clientv3.New` / `kubernetes.New` | proved (`kvClient_of_new`) | **needs `clientNoProxy`: Go fix G3** (`newKubeClient`, `store.go:55`, passes no `grpc.WithNoProxy()`) |
| leases (`leaseManager.GetLease` → `Lease.Grant`) | none | unreachable: the driver sets no TTL (as in-process) |
| `Endpoints`, `Ctx`, `Close` | proved, local | yes |

**Gaps (each a new or strengthened interim axiom: rule #8, Upamanyu's OK, an `axiom`-skill review):**

- **GAP-1, `KV_Get_dist`'s error arm.** Today it gives `err ≠ nil ∧ resp = null ∗ statusErrOk err` only. The
  review explicitly left out `clientErr` and `errCellOk` (`notes/axiom-review/kv-get-dist-statuserr.md`). k8s
  needs:
  - `clientErr` and `errCellOk`, for the store's `unkErr`, `errors.Is`/`As` on client errors, and
    `errDeleteRejected` told apart;
  - the future-revision half of `rangeErrSound`;
  - **for one cluster, a new compacted half**: a compacted description means the read asked a revision below
    the compaction. This is what proves that the "compacted at no old revision" panic is unreachable: a
    one-page List at the latest revision must never see `ErrCompacted`. Today's `kubernetes.Client.Get`/`List`
    specs do not state it.

  In-process both halves are derivable (`rangeErrΨ`, `KVService.lean:1248`, has `rangeCompactedAt`), so S2
  can retire them. Proposed form: a variant `KV_GetE_dist` whose error arm is `kvErr ∗ rangeErrΨ`-at-`Γ`, as
  §29.7 strengthened `KV_Get_dist` for the cache.
- **GAP-2, error arms of `Txn_Commit_dist` and `KV_Compact_dist`.** Both give only `err ≠ nil`, not even
  `statusErrOk`. The store's `unkErr` and the compactor's logging (`klog` with `%v`) need `kvErr`. This is the
  same strengthening as GAP-1, without a revision half.
- **GAP-3, possibly none.** `metav1.Status` through `encoding/json` in the Raw codec (`storecodec.go:194,234,265,302`)
  needs a `json.Marshal`/`Unmarshal` spec for `Status`. Recommended instead: Go change G5 (encode `Status` with
  `enc`), which adds no axiom.
- Already covered: `reflect.DeepEqual` (RawOK, `storecodec.go:409`) on the store's values, if
  `Spec/reflect/DeepEqualK8s.lean` covers `Obj`/`ObjList`/`Status`/errors; K10 checks this, and otherwise
  extends that spec.

### 2.3 Rework risk when #24 S2 replaces the `_dist` specs

- If the k8s library keeps `StoreCfg`'s `ms`/`V` and is re-stated over `kvClientAt`, the S2 swap re-threads
  through about 550 modules (80k lines, `etc/importers.py --count Store.lean`).
- **Mitigation (K5):** abstract the client first. One predicate and its laws, `k8sClient` (Get/List,
  OptimisticPut/Delete, Watch, RequestProgress, Txn, Compact; as the cache's `isEtcdClient`,
  `etcd/dist/client/CacheWorkDefs.lean:341`), would be instantiated twice: in-process from today's proofs,
  and dist from the `_dist` axioms (K7). S2 then re-proves only the dist instance.
- The GAP-1/2 error arms must be statements S2 can prove. In-process they are (`kvErr`, `rangeErrΨ`), so the
  risk is low. The compacted half is new at the k8s client level only.

## 3. New Go code to verify

| Code | Status |
|---|---|
| `examples/lib/remote` (`Do`, `Serve`, `Report`, rwire persistent predicates §28) | verified (`Net/Proof/.../lib/remote/`) |
| `net` | verified (Net part) |
| etcd-dist `server.MainDeployment`/`Main` (the members) | verified for etcd_safe_nocrash (over its interim axioms) |
| etcd-dist `client.Rotate`, `CallAll`, `enc` | verified (`Spec/.../etcd/dist/client/{Rotate,CallAll}.lean`, `dist/enc/`) |
| etcd-dist `client.AwaitCluster`, `ConnectRetry`, `AwaitAccept` (`client.go:90`, `nodes.go:202`, `await.go:17`) | **new** (small: a Get loop, `New` with no proxy, dials) |
| `etcdstart.NewClients` | verified |
| `dist.go`: `MainReady`, `NodeMain`, new `Orchestrator`/`NodeDeployment`/`WellFormed` (G1) | **new**, small |
| `store.go`: `StoreNode`, `RunStore`, `CheckShared` | **new** (RunStore's check orchestration: 100 lines) |
| `storecopy/export.go`: `SharedModel` (settle, landings, `histHashes`, `watchOkIdx`/`hview` memo, three modes), `HistoryRevs`, `NoForeign`, `PastRead`/`PinnedRead`, `SeedShared`, `Serve`/`Record` | **new, the bulk** (969 lines). `Serve`/`Record` are `Apply` split at its prophecy and reuse its proof |
| `storecopy/{k8setcd3,watch,realcheck}.go` | byte-for-byte copies of the proved driver. **Reuse needs G2** (below) or generated proof copies |
| `storecodec.go` (Input/StoreOut/Raw codecs, 443 lines) | **new** (kvremote's codecs are the pattern) |
| `compactor.go`: `CompactorNode`, `RunCompactor`, codec | **new**, small |
| `compactorcopy`: `WriterAt` (the writer with a key parameter), `NewOwn`/`NewShared`, `Sample`/`CheckLog` (`check` split in two) | **new**, a modification of the proved `writer`/`check` |

**Go changes the Lean side needs (G-list; a Go session; G2 needs the user's OK):**

- **G1.** Make `Deployment`/`WellFormed` program code (out of `deploy_test.go`), add the client machines'
  addresses, and add the entry points `Orchestrator(d, j)` and `NodeDeployment(d, n)` (check, then dispatch),
  as etcd-dist's `client.Orchestrator` (`client.go:186`). The members keep `server.MainDeployment(d.Cluster, i)`.
  The `ready` callback becomes the harness's file marker, outside the verified path.
- **G2.** Put `export.go` into the drivers' own packages (`examples/k8s/etcd3`, `examples/k8s/compactor`) and
  drop the copies.
  - Adding files changes no proved function, so `k8s_safe`'s proof is unaffected.
  - Without this, every proof of the copied 2,955 lines must be duplicated under the copies' Go path: a
    generated copy (as `etc/gen-raft-tla.py` or `etc/copy-part.py`), about 40k lines.
  - It reverses k8s-dist.md's "Copies" decision, so it needs the user's OK.
- **G3.** Add `DialOptions: []grpc.DialOption{grpc.WithNoProxy()}` in `newKubeClient` (`store.go:57`), which
  every dist axiom's `clientNoProxy` requires.
- **G4.** Take `dumpHistory`/`LoadHistory` (`gob`, `os`, `DIST_DUMP`: `store.go:201-255`) off the binaries' path:
  a test-only hook, since `gob` has no model.
- **G5.** Encode `metav1.Status`/`StatusError` with `enc` instead of `encoding/json` (`storecodec.go`).
  Otherwise GAP-3 needs an axiom.
- **G6.** Add a goose project `k8s-dist` (`etc/goose.py`: its own `go.mod`'s pins, `GO_MOD_PINS`/`CLIENT_GO_PINS`
  as in k8s-dist.md), translated into the main tree. Its names are distinct once G2 drops the copies.

## 4. Stages (riskiest first), with estimates

A "session" is one agent session (about 150k context). The build figures are rough: the k8s library cone is
550 modules and 80k lines; the k8s driver's `Inv.lean` cone is 129 modules and 21k lines. All heavy builds run
under `systemd-run --scope -p MemoryMax=56G` on the 61G hosts.

| Stage | What | Risk | Sessions | Build |
|---|---|---|---|---|
| **K4** | **`SharedModel`'s full mode is complete**, a pure proof. If the cluster's real history linearizes with foreign revisions, compactions and pending writes, then the full mode's search reaches a configuration that answers it. It needs the canonical-placement argument (k8s-dist.md: a pending write moves down to one above the greatest revision named below it); the "Still open" eager timeouts do not matter for soundness. First on paper, then as Lean functions mirroring `settle`/landings and the theorem | **highest** (if it fails: two clusters) | 2-4 | light (pure modules over the driver's `Model` defs) |
| K5 | The client abstraction of the k8s library (`StoreCfg`'s `ms`/`V` → `k8sClient` and its laws), in-process instance re-proved; `k8s_all` unchanged | medium (wide, mechanical) | 2-3 | heavy: k8s cone rebuilt, several hours at 16 cores |
| K6 | Interim-axiom packet: `KV_GetE_dist` (kvErr + rangeErrΨ at `Γ`), Txn/Compact error arms (kvErr); the `kubernetes.Client.{Get,List}` compacted half proved in-process | medium (review) | 1 + reviews | light |
| K1/K2/K3 | Statement packet (§1) for approval; Go changes G1-G6 and a TestDist re-run; the `k8s-dist` translation and `etc/gen-init.py` entries | low | 0.5 + 1-2 + 1 | translation: moderate |
| K8 | **The store over a shared KV** (one cluster): the driver's invariant over a `/registry/` prefix share (`KVPfxDist`, §23.1) with foreign revisions and compaction; the ghost linearization into `SharedModel`'s (via K4); `PastRead`/`PinnedRead` cover every compacted error (GAP-1's half); `NoForeign ∧ FailureFree ∧ no compacted ∧ RawOK` ⇒ the in-process `realCheck` argument | **high** | 4-8 | heavy (driver cone) |
| K9 | `SharedModel`'s Go code verified against K4's Lean model (hash-consing, memo, modes), `HistoryRevs`, `NoForeign`, `SeedShared`, `CheckShared` | medium-high | 3-5 | moderate |
| K10 | Codecs (`storecodec`, `compactorCodec`, Raw/RawOK with DeepEqual), the `remote.Do` instance for the store (`opMaybe` from `Serve`'s spec, as kvremote's), the `remote.Report` instance for compactor logs (a pure `CheckLogOk` wire predicate) | medium | 2-3 | moderate |
| K11 | The compactor on one cluster: its invariant over its own keys (`/k8sdist-compactor/`, `compact_rev_key`) with foreign writes; `Rounds` with the shared compactor's restart; `Sample`/`CheckLog` from the proved `check` | medium | 2-3 | moderate |
| K7 | The dist instance of `k8sClient` from the `_dist` axioms and `kubernetes.New` | low | 1 | moderate |
| K12 | Machines and start: `StoreNode`, `RunStore`, `CompactorNode`, `RunCompactor`, dispatch; `AwaitCluster`/`ConnectRetry`/`AwaitAccept`; the k8s start (the cluster at `cmp = true`, `cret = 0`; prefix shares for both workloads; **two remote protocols at one start**, which etcd-dist never needed, §27.1); `TopLevelRobustness`, a premise witness, a `tcb-collections/k8s-dist.txt` | medium | 3-4 | heavy (assembly) |
| K13 | Gates and the F9-style trust packet; landing via `etc/land.sh` | low | 1-2 | full build |

**Total:** about 22-35 sessions for one cluster. The two-cluster fallback drops K4, most of K8 and part of K9:
about 12-18.

**What can start now on fk-lean1/fk-lean2, without waiting on anyone:**

- **K4 (fk-lean1).** Pure; touches nothing shared; settles the one-cluster decision. Its first deliverable is a
  paper proof in `notes/`, then Lean.
- **K5 (fk-lean2).** In-process only; `k8s_all`'s statement and TCB stay unchanged; it is worth doing for S2
  in any case. Builds are heavy: one full k8s-cone rebuild per checkpoint, using `etc/importers.py --leaves`
  targets.
- **K6 drafting** (no build): the axiom texts and the in-process lemma for the compacted half. It only lands
  after rule-#8 approval.
- **G3/G4** are trivial Go fixes, safe to do now. G1/G5/G6 also need no approval. G2 waits for the user's OK.

### 4.1 K5: the client interface (design, 2026-11-27)

**What the library uses today** (callees of `etc/link-lean-first-k8s-etcd3.txt` in the client packages, and
the `StoreCfg` fields their statements name):

- the store (unary and list paths): `kubernetes.Client.{Get,List,OptimisticPut,OptimisticDelete}`, over
  `isNewClient c.cl (c.ms.map addr) c.V ∗ clientWriteOnce ∗ [∗list] x ∈ c.ms, kvRegsAt x` (`isStore`), with
  per-member updates `[∧list] x ∈ c.ms, … x.γr.kv …` and the premise `∀ x ∈ c.ms, noRefusalAt x.addr`;
- the watch (`watchChan.{syncPaginated,startWatching}`): the client's `KV.Get` (`client_range_any.law`,
  wrapped by `wp_syncGet`, which already states it abstractly: `□ Qr σ ∗ srvRangeOk …` or `kClientErr`) and
  its `Watcher.Watch` (`isClientWatcher V w`);
- the compactor (`Compact`, `compactor.{getCompactRev,runWatchLoop,runCompactLoop}`,
  `StartCompactorPerEndpoint`): `KV.Txn`/`If`/`Then`/`Else`/`Commit` (one CAS), `Client.Compact`
  (`client_Compact_kv.law`), `KV.Get` at a revision, `Watcher.Watch`, `Client.Endpoints`; its own
  `cl ms V γk` arguments, not a `StoreCfg`.

`V` is used only to pass to these specs and in `isNewClient`. `ms` is used for three things: the
linearization ghosts (`x.γr.kv`), the no-refusal premise (`x.addr`), and the endpoints (`ms.map addr`).

**The interface** (new defs module `Proof/k8s_io/apiserver/pkg/storage/etcd3/EtcdClient.lean`):

- `K8sEtcd GF`, the data, a structure:
  - `kvs : List KVNames`: the KV ghosts a request may linearize at; every update a spec takes is given at
    each (`[∗list]`/`[∧list] γ ∈ K.kvs`). In-process: `ms.map (·.γr.kv)`; dist (K7) and S2: `[Γ.kv]`.
  - `live : Prop`: the premise under which a range error is sound (no refusal). In-process:
    `∀ x ∈ ms, noRefusalAt x.addr`; dist: what the `_dist` axioms need (`True` if none).
  - `eps : List GoString`: the endpoints (`Client.Endpoints`). In-process: `ms.map SrvAt.addr`.
- `k8sClient K cl : IProp GF`, persistent, as the cache's `isEtcdClient` (`CacheWorkDefs.lean:341`): the
  triples of the client calls the library makes, on `cl` (the `*clientv3.Client`), each the in-process
  spec with `isNewClient … ∗ clientWriteOnce … ∗ [∗list] kvRegsAt` dropped, `[∧list] x ∈ ms, F x.γr.kv`
  become `[∧list] γ ∈ K.kvs, F γ`, and `∀ x ∈ ms, noRefusalAt x.addr` become `K.live`. Fields, in
  batches (one conjunct group each):
  - **C1** (store): `kubernetes.Client.{Get,List,OptimisticPut,OptimisticDelete}` on any `kc` with
    `kc.Client' = cl`;
  - **C2** (watch): `∃ api w`, `cl.KV ↦□ kvIfaceOf api`, `cl.Watcher ↦□ watcherIfaceOf w`, with
    `wp_syncGet`'s triple (readAus over `K.kvs`) and the watch-open triple the watch proofs use;
  - **C3** (compactor): the CAS `Txn` chain on an abstract txn handle, `Compact`, `KV.Get` at a
    revision, the compactor's `Watch`; `Endpoints` returning `K.eps`;
  - `Ctx` (the client's context, read-only), as today's `isNewClient_ctx`.
- The in-process instance, `k8sClient_inProc` (defs tier, the specs as hypotheses, linked in `Link`):
  `isNewClient cl (ms.map addr) V ∗ clientWriteOnce cl (ms.map addr) ∗ [∗list] x ∈ ms, kvRegsAt x ⊢
  k8sClient (inProcEtcd ms) cl`, from today's specs (`kubernetes.Client.*.spec`, `client_range_any.law`, …).
- Users: `StoreCfg` replaces `ms`/`V` by `K : K8sEtcd GF`, and `isStore` holds `k8sClient c.K c.cl` in
  place of the three in-process conjuncts; the compactor's `cl ms V γk` become `cl K γk`. The library's
  proofs call the client through the predicate (`iapply` of its triple) and no longer take the client's
  specs as callees. `etcd3.New`'s spec takes `k8sClient K cl`; the driver (`examples/k8s/etcd3`,
  `compactor`) applies `k8sClient_inProc` where it builds the store, so `k8s_all`'s statement and its
  premises are untouched (its proof only re-threads).

**Batches** (each built on fk-lean2 with `etc/importers.py --leaves` targets):

1. `EtcdClient.lean` with C1 and the instance's C1 part; ledger entries for the Spec files batch 2 changes.
2. `StoreCfg`/`isStore` and the store's specs and proofs (unary + list paths, `FirstRead`, `ListDefs`,
   `State`, `Updates`): `c.ms`/`c.V` gone.
3. C2 and the watch path (`WatchDefs` `readAus`, `syncPaginated`, `startWatching`, `run`, `Watch`).
4. C3 and the compactor.
5. The drivers (`examples/k8s/{etcd3,compactor,all}`: `Apply`, `Check`, `Main*`, `kInv` over `K.kvs`),
   `Link` regenerated, `k8s_all` rebuilt; `etc/tcb-report.py --check`, byte-identity of the two
   `TopLevelRobustness` Spec files checked against `lean`.

#### Handoff K5-1 (2026-11-27)

- **Done.** Design above (§4.1). Batch 1, commit `a84dfc1ecb`: `Proof/k8s_io/apiserver/pkg/storage/etcd3/EtcdClient.lean`
  (`K8sEtcd` = `kvs`/`live`/`eps`/`handle`; `K8sEtcd.Laws`, C1 = `get`/`list`/`optimisticPut`/`optimisticDelete`,
  each the `kubernetes.Client` spec over `K.handle kc.Client'`; `k8sClient K cl := ⌜K.Laws⌝ ∗ □ K.handle cl`)
  and `EtcdClientInProc.lean` (`inProcEtcd ms V`, `inProcEtcd_laws` from the four specs taken
  `∀ [kubernetes.Assumptions]`, `k8sClient_inProc`). Ledger entry for the Spec changes of batches 2-5 written
  (`notes/specs-only/ledger.md`, 2026-11-27). Laws are Prop-level triples (not WPs inside the predicate), so the
  library's proofs call `hK.get …` with `wp_apply` as they call `wp_Get` today, after `icases` of `k8sClient`
  into `⟨%hK, #Hh⟩`.
- **Build host.** fk-lean2 refused to seed a worktree (64 GB free, needs 65 GB; its `wt/` holds 10 other
  sessions' worktrees), so batch 1 was built on **fk-lean1** (`wt/k8s-dist-k5/2026-11-27` there), against the
  brief. The next session should go back to fk-lean2 once it has disk (or keep fk-lean1 with the coordinator's OK).
- **Build state.** Built on fk-lean1 (log `/home/ubuntu/eg/logs/k8s-dist-k5_2026-11-27-20261127-192136.log`):
  `EtcdClient` builds; `EtcdClientInProc` failed only because `bigAndL_map` was unqualified (the follow-on
  `iframe` errors came from the `simp` that did not run). Fixed to `BigAndL.bigAndL_map` in the handoff commit,
  **not rebuilt**: the next session builds `Proof.k8s_io.apiserver.pkg.storage.etcd3.EtcdClientInProc` first
  (if `simp only` does not reduce the `K8sEtcd` projections, `show` the old forms before `iapply`).
- **Next (batch 2).** `StoreCfg`: `ms`/`V` → `K : K8sEtcd GF`; `isStore`'s `isNewClient … ∗ clientWriteOnce … ∗
  [∗list] kvRegsAt` → `k8sClient c.K c.cl` (about 20 proofs `icases` isStore with `#Hcl, #Hone, #Hregs`: one slot
  now). The watch (`syncPaginated` via `client_range_any.law`, `WatchDefs.readAus`) and compactor consumers of
  `c.ms` break at the same time, so batch 2 cannot build alone unless C2 (the `wp_syncGet` triple) is added to
  `Laws` first; do C2 before or with batch 2. Spec rewrites: `∀ x ∈ c.ms, noRefusalAt x.addr` → `c.K.live`,
  `[∗list]/[∧list] x ∈ c.ms, F x.γr.kv` → `… γ ∈ c.K.kvs, F γ` (`bigSepL_map`/`bigAndL_map` give back the
  in-process forms). Then rerun `etc/gen-link.py --k8s-etcd3`.

#### Handoff K5-2 (2026-11-27)

- **Done.** Batch 1's instance builds (`EtcdClientInProc` built on fk-lean1 at `625bb29adb`). Batch 2, commit
  `78ca909eb9`: `K8sEtcd` gains `kvAt : Loc → IProp GF` (what a `*kv`'s `Get` needs); `Laws` gains `ctxFields`
  (the client's ctx and `clientCheckFields`, for `New`), and C2 = `kvField` (`K.handle cl ⊢ ∃ api, clientF cl
  "KV" ↦□ … ∗ □ K.kvAt api`) and `kvGet` (`wp_syncGet`'s triple over `K.kvAt api` and `□ [∗list] γ ∈ K.kvs,
  kvReadAu γ Qr`); `K8sEtcd.Laws.getLatest` (`Client.Get.latest` over `K`); in-process proofs of all three
  (`inProcEtcd_laws` now also takes `client_range_any.law`). The watch's `Watcher` needed no law: the library
  already sees it through `clientWatchOk`. `StoreCfg`'s `ms`/`V` → `K`; `isStore` holds `k8sClient c.K c.cl`;
  the store and watch specs and proofs switched (`c.K.live`, `[∗list]/[∧list] γv ∈ c.K.kvs`,
  `k8sAusRW_kvAu1` over `ks : List KVNames`); `New.spec` takes `K` and `k8sClient K cl`;
  `etc/link-lean-first-k8s-etcd3.txt` drops the `Client__*` and `client_range_any` callees of the store/watch
  proofs; `Link.lean` regenerated.
- **Build** (fk-lean1, log `/shared/tmp/k5-2-b2.log`, targets `EtcdClientInProc` + etcd3 `Link`): everything
  builds (store proofs, `New`, `startWatching`, `GetList`, ...) but **one error**:
  `watchChan__syncPaginated.lean:95:23`, `iintro: c.K.kvAt api not persistent` (in `wp_syncGet`'s `iintro`,
  the pattern `#Hkv`). Fix: `Hkv` (spatial) there, or `□ c.K.kvAt api` in `wp_syncGet`'s precondition (the
  caller holds it as `#Hkv` from `kvField`). `Link` was not reached; rebuild the same targets after the fix.
- **Left.** Batch 4 (C3, the compactor: `Compact`, `compactor.{getCompactRev,runWatchLoop,runCompactLoop}`,
  `NewCompactor`, `StartCompactorPerEndpoint` still take `cl ms V`; the Txn chain, `Compact`, `Get` at a
  revision, `Endpoints` → laws, `cl K γk`). Batch 5, the drivers (`examples/k8s/etcd3`: `Calls`, `Apply`,
  `WatchQ`, `Main*` (`storeCfgD … ms V` → `K := inProcEtcd ms V`, with `k8sClient_inProc` and
  `inProcEtcd_laws` linked from the `kubernetes.Client.wp_*` and `client_range_any_law_holds`), Specs
  `Check`/`Apply`/`call`/`runWatch`/`watchEvents` with `c.ms` → `c.K.kvs`/`c.K.live`, `c.ms ≠ []` →
  `c.K.kvs ≠ []`); they do not build now. Then `etc/gen-link.py --k8setcd3`, `k8s_all`, `etc/tcb-report.py
  --check`, the two `TopLevelRobustness` Spec files byte-identical to lean. Extend the ledger entry if
  `kvAt`/`ctxFields` count as a design change (they are additions inside the K5 interface).

## 5. Approvals

| What | Who |
|---|---|
| The statement (name, shape, premises, one vs two clusters, `Apiservers`/`Rounds` as parameters) | coordinator-E, then Upamanyu (statement review); one vs two clusters goes to the user with K4's result |
| GAP-1/GAP-2 strengthened interim axioms (and GAP-3 if G5 is not done) | rule #8: Upamanyu's OK, each with an `axiom`-skill review |
| `RealClock.After`'s contract becomes an axiom in its file (was the premise `Hafter`) | rule #8, unless it is proved over Perennial's `time` |
| G2: the drivers gain `export.go`, and the copies go | the user (reverses k8s-dist.md "Copies") |
| Two remote protocols at one start (`remote`/start generalization) | `remote`'s owner, the coordinator (#28) |
| Landing | `etc/land.sh` after the coordinator's go |
