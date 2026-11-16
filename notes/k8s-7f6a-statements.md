# k8s 7f-6 stage A: the closed statements, old → new (2026-11-16; HARD STOP before linking)

Stage A of `notes/k8s-7f6-scope.md` §5: the cluster and partition theorems for `k` members,
`1 ≤ k ≤ 1000`, on the generic `etcdstart.Members`/`StartMembers` start (the user's decision (b),
2026-11-16; Q1: replaced in place, same names). No watches yet. `k8s_etcd3_safe` (one member) is
unchanged in stage A.

**What is built** (unlinked, branch `k8s-7f6`): the Go (`startCluster(k)`, `MainCluster(k, …)`,
`MainPartition(k, …)`), its translation, and the proofs `startCluster.wp_proof`,
`MainCluster.wp_proof`, `MainPartition.wp_proof` (+ `bridgeAddr`, `holdToken`, the vocabulary
`ClusterN.lean`, the pure facts `DirN.lean`, the regenerated `Init`/`PkgTable`). What waits for the
user's approval of the statements below: `Adequacy.lean`, `MainLinked.lean`, `Link.lean`,
`Results.lean`, the tcb collection, interfaces.

The two `Main*` spec results (`k8setcd3_MainCluster`, `k8setcd3_MainPartition`, statements
`MainCluster.spec`/`MainPartition.spec` in `Spec/github_com/mit_pdos/etcd_grove/examples/k8s/etcd3/`)
change the same way (proved, in the diff).

## 1. `k8s_etcd3_cluster_safe`

**Old** (lean `ee15ea8d45`, `Proof/.../examples/k8s/etcd3/Results.lean`):

```lean
theorem k8s_etcd3_cluster_safe [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : …k8s.etcd3.Assumptions] [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [k8s_io.apiserver.pkg.storage.etcd3.Assumptions] [k8s_io.apimachinery.pkg.runtime.Assumptions]
    [k8s_io.apimachinery.pkg.runtime.schema.Assumptions] [k8s_io.apiserver.pkg.storage.Assumptions]
    [k8s_io.apiserver.pkg.storage.value.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC k8setcd3GF, ContextReadErrs (GF := k8setcd3GF) (hG := k8setcd3HeapAt hG lctx))
    (id₁ id₂ id₃ : w64) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hbf : cluster3.BootFacts id₁ id₂ id₃ ps ctxs boot)
    (Haf : authRecordsFit) (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit) (Hdbo : storage.diskOk)
    (clients ops : w64)
    (Hc0 : 0 ≤ sint.Z clients) (Hc31 : sint.Z clients < 2 ^ 31) (Hops : 0 ≤ sint.Z ops)
    (Hmul : sint.Z clients * sint.Z ops < 2 ^ 60)
    (HNs : prometheus.namesUnclaimed (k8setcd3CProgram clients ops) k8setcd3Names)
    (HAs : addrsUnclaimed (k8setcd3CProgram clients ops) k8setcd3CAddrs)
    (HDs : dataDirsAbsent (k8setcd3CProgram clients ops) k8setcd3CDataDirs)
    (HEnv : verifyEnvOff (k8setcd3CProgram clients ops))
    (n : Nat)
    (Hprem : ∀ hG : HeapGS .hasLC k8setcd3GF,
      ⊢ cluster3.premises (GF := k8setcd3GF) (hG := k8setcd3HeapAt hG lctx) k8s_etcd3.clusterCfg n
        id₁ id₂ id₃ ps ctxs boot)
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([k8setcd3CProgram clients ops], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 28) :
    (∀ v t2', t2 = Val v :: t2' → v = #(go!"Ok") ∨ v = #(go!"Unknown")) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false)
```

with `k8setcd3CProgram clients ops := initialize' #() ;; MainCluster(clients, ops)`, `k8setcd3CAddrs`
the nine addresses of `clusterCfg` and `k8setcd3CDataDirs` its three data directories.

**New** (lines marked `-- changed`/`-- new`; the rest is word for word the old):

```lean
theorem k8s_etcd3_cluster_safe [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : …k8s.etcd3.Assumptions] [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [k8s_io.apiserver.pkg.storage.etcd3.Assumptions] [k8s_io.apimachinery.pkg.runtime.Assumptions]
    [k8s_io.apimachinery.pkg.runtime.schema.Assumptions] [k8s_io.apiserver.pkg.storage.Assumptions]
    [k8s_io.apiserver.pkg.storage.value.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC k8setcd3GF, ContextReadErrs (GF := k8setcd3GF) (hG := k8setcd3HeapAt hG lctx))
    (k : Nat) (hk1 : 1 ≤ k) (hk : k ≤ 1000)                                         -- new
    (ids : List w64) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)  -- changed (ids)
    (Hlen : ids.length = k)                                                          -- new
    (Hbf : k8s_etcd3N.BootFacts ids ps ctxs boot)                                   -- changed
    (Haf : authRecordsFit) (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit) (Hdbo : storage.diskOk)
    (clients ops : w64)
    (Hc0 : 0 ≤ sint.Z clients) (Hc31 : sint.Z clients < 2 ^ 31) (Hops : 0 ≤ sint.Z ops)
    (Hmul : sint.Z clients * sint.Z ops < 2 ^ 60)
    (HNs : prometheus.namesUnclaimed (k8setcd3CProgram k clients ops) k8setcd3Names)              -- changed (k)
    (HAs : addrsUnclaimed (k8setcd3CProgram k clients ops) (k8s_etcd3N.k8setcd3NAddrs k))       -- changed
    (HDs : dataDirsAbsent (k8setcd3CProgram k clients ops) (k8s_etcd3N.k8setcd3NDirs k))        -- changed
    (HEnv : verifyEnvOff (k8setcd3CProgram k clients ops))                                       -- changed (k)
    (n : Nat)
    (Hprem : ∀ hG : HeapGS .hasLC k8setcd3GF,
      ⊢ k8s_etcd3N.premises (GF := k8setcd3GF) (hG := k8setcd3HeapAt hG lctx) k n ids ps ctxs boot)  -- changed
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([k8setcd3CProgram k clients ops], ((σ, g) : CfgState)) κs (t2, σ2))  -- changed (k)
    (Hn : n + 2 ≤ 2 ^ 28) :
    (∀ v t2', t2 = Val v :: t2' → v = #(go!"Ok") ∨ v = #(go!"Unknown")) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false)
```

The definitions it is written in (new or changed):

```lean
/-- The program: the package's initialization, then `MainCluster(k, clients, ops)`. -/
def k8setcd3CProgram [GoSemanticsFunctions] (k : Nat) (clients ops : w64) : Expr :=
  github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.initialize' #() ;;
  App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.MainCluster))
    (Val #(W64 (k : Int)))) (Val #clients)) (Val #ops)

-- ClusterN.lean / DirN.lean (txnlinfaultsN's, at these names and ports)
abbrev k8s_etcd3N.members (k : Nat) : List GMember := membersOf go!"k8setcd3N" k (W64 20000) (W64 21000)
abbrev k8s_etcd3N.token : GoString := go!"k8setcd3N-6285"
def k8s_etcd3N.bridgeAt (i : w64) : GoString := go!"127.0.0.1:" ++ decStr (W64 22000 + i)
def k8s_etcd3N.bridges (k : Nat) : List GoString := (List.range k).map (fun i : Nat => bridgeAt (W64 (i : Int)))
abbrev k8s_etcd3N.BootFacts (ids ps ctxs bl) : Prop := etcd_putgetN.BootFacts ids ps ctxs bl
def k8s_etcd3N.premises (k N ids ps ctxs boot) : IProp GF :=
  ([∗list] m; id ∈ members k; ids,
     etcdstart.bootPremise N ps (LogEntry.toEntries boot 0) ctxs (etcd_putgetN.dirN (members k) ids)
       token m.Name' (urlsN (members k) m) id) ∗
  bootMarshal ps ctxs (LogEntry.toEntries boot 0) ∗ etcdstart.commonPremises
def k8s_etcd3N.k8setcd3NAddrs (k : Nat) : List GoString :=
  (members k).map (·.Peer') ++ (members k).map (·.Client') ++ bridges k
def k8s_etcd3N.k8setcd3NDirs (k : Nat) : List GoString := (members k).map (fun m => m.Name' ++ go!".etcd")
```

`k8setcd3CAddrs`, `k8setcd3CDataDirs` and `k8s_etcd3.clusterCfg` (`Cluster.lean`) are deleted.

**In plain English.** Old: for the three named members `k8setcd3c-1..3` (cluster3's start), every
real run of `MainCluster(clients, ops)` ends with `Ok` or `Unknown`, never sticks, never panics.
New: **for every member count `1 ≤ k ≤ 1000`**, the same, for `MainCluster(k, clients, ops)` over
the `k` members `k8setcd3N-0 … k8setcd3N-(k-1)` started by `etcdstart.Members`/`StartMembers`, each
behind a bridge, with one kubernetes client of the `k` bridges. The premises change only in their
shape for `k` members:
- the boot facts: putgetN's list form (`ids` in the members' order, `ps` a permutation of them,
  their 16 low bits distinct and non-zero, the bootstrap log) in place of cluster3's three ids;
  `TestMemberIDs` checks the ids' premise for the token at every `k ≤ 1000`;
- the Iris premises: putgetN's, at these members and token, in place of cluster3's at `clusterCfg`;
- the addresses unclaimed: the `3k` peer, client and bridge addresses (ports `20000+i`, `21000+i`,
  `22000+i`) in place of the nine; the data directories absent: the `k` `k8setcd3N-i.etcd` in place of
  the three.
Nothing else: no new kind of premise, no new trust (the start's specs are those putgetN and
txnlinfaultsN already rest on; `kubernetes.New` is the same spec the 3-member proof used).
`k = 3` is an instance (with the list-form boot facts).

## 2. `k8s_etcd3_partition_safe`

The same changes, on the old statement (which is `k8s_etcd3_cluster_safe`'s with `(steps : List
cluster3.Step) (Hsteps : steps.length < 2 ^ 63)` and the program `k8setcd3PProgram clients ops steps`):

```lean
theorem k8s_etcd3_partition_safe … (Hctx : …)
    (k : Nat) (hk1 : 1 ≤ k) (hk : k ≤ 1000)                                         -- new
    (ids : List w64) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)  -- changed
    (Hlen : ids.length = k) (Hbf : k8s_etcd3N.BootFacts ids ps ctxs boot)            -- new / changed
    (Haf …) (Hbuq …) (Hrf …) (Hdbo …) (clients ops : w64) (Hc0 …) (Hc31 …) (Hops …) (Hmul …)
    (steps : List github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step) (Hsteps : steps.length < 2 ^ 63)
    (HNs : prometheus.namesUnclaimed (k8setcd3PProgram k clients ops steps) k8setcd3Names)        -- changed (k)
    (HAs : addrsUnclaimed (k8setcd3PProgram k clients ops steps) (k8s_etcd3N.k8setcd3NAddrs k)) -- changed
    (HDs : dataDirsAbsent (k8setcd3PProgram k clients ops steps) (k8s_etcd3N.k8setcd3NDirs k))  -- changed
    (HEnv : verifyEnvOff (k8setcd3PProgram k clients ops steps))                                 -- changed (k)
    (n : Nat)
    (Hprem : ∀ hG, ⊢ k8s_etcd3N.premises (GF := k8setcd3GF) (hG := k8setcd3HeapAt hG lctx) k n ids ps ctxs boot)  -- changed
    (σ …) (g …) (Hlctx …) (Hinit …) (Hthreads …) (κs …) (t2 …) (σ2 …)
    (Hsteps' : RealNsteps n ([k8setcd3PProgram k clients ops steps], ((σ, g) : CfgState)) κs (t2, σ2))  -- changed (k)
    (Hn : n + 2 ≤ 2 ^ 28) :
    -- conclusion unchanged
```

```lean
def k8setcd3PProgram [GoSemanticsFunctions] (k : Nat) (clients ops : w64)
    (steps : List github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step) : Expr :=
  github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.initialize' #() ;;
  App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.MainPartition))
    (Val #(W64 (k : Int)))) (Val #clients)) (Val #ops)) (schedLit steps)
```

**In plain English.** For every `1 ≤ k ≤ 1000` and **every** partition schedule (its steps name
members by index; a step naming a member `≥ k` does nothing, as `cluster3.PeerStep`/`ClientStep`
check), every real run of `MainPartition(k, clients, ops, sched)` ends with `Ok` or `Unknown`, never
sticks and never panics, under the premises of §1.

## 3. Evidence

- Go: `go test .` of `examples/k8s/etcd3` passes (364 s), with the cluster tests at `k = 3`;
  `TestMainCluster` and `TestMainPartition` (five schedules) pass at `k = 1` and `k = 5`; `TestMemberIDs`
  checks the token for every `k ≤ 1000`.
- Lean: `startCluster`, `MainCluster`, `MainPartition` (and their new callees) build; no axiom or
  `sorry` added.
