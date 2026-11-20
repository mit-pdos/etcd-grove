# The compactor driver on k members, threaded into `k8s_robust`: plan (2026-11-20)

Branch `k8s-compactor-n`, worktree `/shared/etcd-grove-compactorn` (compactor-N agent of etcd-grove-03), off
lean `d45f8b140e`. Goal (the user, 2026-11-20): `examples/k8s/compactor`'s `MainPartition` on `k` members
(`1 ≤ k ≤ 1000`) in place of `cluster3.StartCluster`'s fixed three, as the etcd3 driver's `MainPartition`
already is, changed in place (no twin; the single-member `Main` unchanged), and `examples/k8s/all`'s
closed theorem (`k8s_safe`/`k8s_robust`) restated as "etcd3 on k₁ members and the compactor on k₂".
No Lean edited yet; one Go measurement (the member ids, §3, a Python replica of etcd's
`computeMemberID`, checked against the etcd3 token: its 1000 ids come out distinct, as `TestMemberIDs`
says).

## 1. The Go change

`examples/k8s/compactor/compactor.go`:

- **Members, addresses, names** (as etcd3's `PeerBase`/`ClientBase`/`BridgeBase`/`Token`): exported
  constants `PeerBase = 23000`, `ClientBase = 24000`, `BridgeBase = 25000`, `Token =
  "k8scompactorN-235946"` (§3), members `etcdstart.Members("k8scompactorN", k, PeerBase, ClientBase)`:
  member `i` named `k8scompactorN-i`, peer `127.0.0.1:(23000+i)`, client `127.0.0.1:(24000+i)`, bridge
  `127.0.0.1:(25000+i)`, data directory `k8scompactorN-i.etcd`. etcd3's are `[20000, 23000)` and
  `k8setcd3N-i`, so for every `k₁, k₂ ≤ 1000` the ports are disjoint (by range: `[20000,23000)` vs
  `[23000,26000)`, all five-digit, below Linux's ephemeral range 32768) and so are the names and
  directories (prefixes differ). The single-member `Main`'s `127.0.0.1:2397x/2398x` are another
  program's, untouched.
- `startCluster(k, lg) (srvs, brs, baddrs, ok)`: etcd3's `startCluster` without the kubernetes
  client, returning the bridges' addresses (members started by `etcdstart.StartMembers`, then per
  member `go holdToken()`, `etcdstart.Serve`, `cluster3.StartBridge`). A `holdToken` in the package (as
  etcd3's). `bridgeAddr(i)`.
- `MainPartition(k uint64, sched []cluster3.Step)`: `k == 0` returns; `startCluster`; the writer's client
  and each API server's client by `etcdstart.NewClients(baddrs, lg)` (txnlinfaultsN's call, spec
  exists) in place of `cluster3.NewClient(cfg)`; the rest unchanged (partitioner on `srvs, brs`,
  writer, 3 + 2 API servers, the shared compactor registered at the `k` bridges).
- `clusterConfig()` and the `cluster3.Config` literal go (nothing else uses them).
- `examples/k8s/all/all.go`: `Main(k1 uint64, clients, ops, watchers, wops int, sched1 []cluster3.Step,
  k2 uint64, sched2 []cluster3.Step)`, calling `compactor.MainPartition(k2, sched2)`.
- Tests: `compactor_test.go`'s partition tests at `k ∈ {1, 3, 5}`; `all_test.go`'s `TestMemberIDs` over
  both ranges (every `k₁ ≤ 1000`, `k₂ ≤ 600`, by the prefix argument: the ids of a member depend only on
  its peer URL and the token, so checking the 1000 + 600 ids once covers every pair), `TestAddrs` over
  both ranges (ports, names, directories, for every pair: by the same prefix argument, `k₁ = k₂ = max`),
  `TestMain` with `k2 = 3`.

## 2. The proofs (reuse from etcd3's k-member proofs)

| Piece | Source | New/changed lines (est.) |
|---|---|---|
| `etcdstart.memberPre`/`StartMembers.spec` take the compaction mode `cmp` (default `false`; today fixed `false` through `memberBoot`'s default); `AllocN` already takes `cmp` | internal spec generalization, callers pass `false` | ~40 |
| etcd3 `startCluster.lean`'s generic lemmas (`startOf_peers`, `freshRes_split`, `memberPres_of`, `memberBoots_raft`, `memberOf_of_gOk`, `watchRegAt_forwards`, `kvRegs_forwards`) moved down to a defs module (`lib/etcdstart/StartClusterN.lean`), names and statements unchanged, `memberPres_of` at `cmp` | move (tiers: a proof may not import a proof) | ~0 net |
| `compactor/ClusterN.lean`: `k8s_compactorN.members/bridgeAt/bridges/startOf/BootFacts/premises/clusterUp` (etcd3's `ClusterN`, `clusterUp` with the bridges' address slice and the members' watch registrations, in compaction mode, no kubernetes client) | copy of etcd3's | ~170 |
| `compactor/DirN.lean`: names/peers/bridges nodup, ports, plain endpoints, addresses/dirs lists and perms | copy of etcd3's (`decStr` five digits) | ~200 |
| `startCluster`, `bridgeAddr`, `holdToken` specs + proofs | etcd3's, minus `kubernetes.New` | ~550 |
| `MainPartition` spec + proof at `k` | today's proof with the three members' unrolled steps (`memberWatch_of_cinv` ×3, `kvRegsAt` ×3, `epOf_alloc` ×3, the partitioner's lists) replaced by inductions over the `k` members; the watch environment `etcdstart.watchEnvL` (etcd3's) in place of `cluster3.watchEnv` | ~450 (replaces 447) |
| `clusterConfig` spec/proof, `Cluster.lean` | deleted | −130 |
| `k8s/all`: `Main` spec/proof, `Disjoint` (now two `k`-member lists, by port ranges), `TopLevelDefs`, `Adequacy`, `Results`, `TopLevelRobustness` | edits | ~250 changed |
| generated: goose (2 packages), `gen-init`, `gen-link` (compactor, all), interfaces | regenerated | — |

About 1,700 hand-written lines new or changed, ~600 deleted; 2–3 sessions; 3–4 incremental builds and one
full build. Risk: the `MainPartition` induction (the shared-compactor registry over `k` bridges needs
`bridges_nodup`; the watch environment's `conn` lemma at `k` members: etcd3's `MainPartition` already
has it through `clusterUp`, which is why `clusterUp` carries the watch registrations).

## 3. Member ids: `Hlow` over `k₁ + k₂` members

etcd computes a member's id as the first 8 bytes of `sha1("http://<peer>" ++ token)`: it depends only on
the member's own peer URL and the token, so the ids of `(k₁, k₂)` are a prefix of etcd3's 1000 and a prefix
of the compactor's. `Hlow` holds for all pairs `k₁, k₂ ≤ B₁, B₂` iff the first `B₁` and first `B₂` 16-bit
suffixes are jointly distinct and nonzero.

**It cannot hold for `k₂ ≤ 1000` with etcd3's ids fixed** (or for `k₁, k₂ ≤ 1000` at all): 2000 suffixes in
65536 values collide with probability `1 − e^{−2000²/2¹⁷} ≈ 1 − 10^{−13}` per token choice. With
etcd3's token unchanged (`k8setcd3N-6285`, its 1000 suffixes distinct), the compactor's first `n` must
avoid 1000 fixed values and each other: probability `≈ exp(−1000n/2¹⁶ − n²/2¹⁷)`. A search over 2·10⁶
compactor tokens (`k8scompactorN-<j>`, base port 23000) found at best `n = 687`. First tokens reaching:
`n ≥ 500`: `-20711`; `n ≥ 600`: `-235946` (holds to 629); `n ≥ 650`: `-656305` (holds to 654).

**Recommendation:** `1 ≤ k₁ ≤ 1000`, `1 ≤ k₂ ≤ 600`, token `k8scompactorN-235946`; `TestMemberIDs` checks
it over the 1000 + 600 ids. (Alternatives: `k₂ ≤ 650` with `-656305`; a symmetric `k₁, k₂ ≤ 700` by
re-searching both tokens, which changes etcd3's driver; or `k₂ ≤ 1000` by weakening idutil's trusted
model to "no two generators of one cluster issue one id", which only requires per-cluster distinctness
but is a trust-base change to `GooseLang/Ext/IdIssue` and the idutil model: not recommended.)

## 4. The new `k8s_robust.spec` (premises)

The changed binders only (everything else as today):

```lean
    -- the store's cluster: `k₁` members
    (k₁ : Nat) (hk₁1 : 1 ≤ k₁) (hk₁ : k₁ ≤ 1000) (ids : List w64) (ps : List w64)
    (ctxs : List (List w8)) (boot : List LogEntry) (Hlen : ids.length = k₁)
    (Hbf : k8s_etcd3N.BootFacts ids ps ctxs boot)
    -- the compactor's cluster: `k₂` members
    (k₂ : Nat) (hk₂1 : 1 ≤ k₂) (hk₂ : k₂ ≤ 600) (ids' : List w64) (ps' : List w64)
    (ctxs' : List (List w8)) (boot' : List LogEntry) (Hlen' : ids'.length = k₂)
    (Hbf' : k8s_compactorN.BootFacts ids' ps' ctxs' boot')
    -- the process's every member: their ids' 16 low bits distinct (idutil's trusted model)
    (Hlow : ((ids ++ ids').map (fun id => uint.Z id % 2 ^ 16)).Nodup)
    ...
    (HNs : prometheus.namesUnclaimed (k8sProgram k₁ clients ops watchers wops steps₁ k₂ steps₂) k8sNames)
    (HAs : addrsUnclaimed (k8sProgram k₁ clients ops watchers wops steps₁ k₂ steps₂) (k8sAddrs k₁ k₂))
    (HDs : dataDirsAbsent (k8sProgram k₁ clients ops watchers wops steps₁ k₂ steps₂) (k8sDirs k₁ k₂))
    (HEnv : verifyEnvOff (k8sProgram k₁ clients ops watchers wops steps₁ k₂ steps₂))
    (Hprem₁ : ∀ n : Nat, n + 2 ≤ 2 ^ 28 → ∀ hG : HeapGS .hasLC k8sGF,
      ⊢ k8s_etcd3N.premises (GF := k8sGF) (hG := k8sHeapAt hG lctx) k₁ n ids ps ctxs boot)
    (Hprem₂ : ∀ n : Nat, n + 2 ≤ 2 ^ 28 → ∀ hG : HeapGS .hasLC k8sGF,
      ⊢ k8s_compactorN.premises (GF := k8sGF) (hG := k8sHeapAt hG lctx) k₂ n ids' ps' ctxs' boot')
    (σ : state) (g : GlobalState) (Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world))
    (HWal : etcdWalAreasInit (extLocal Fs.fsExt σ.world) (k8sDirs k₁ k₂)),
    Robustness.Robust [] [(k8sProgram k₁ clients ops watchers wops steps₁ k₂ steps₂, σ)] g (2 ^ 28 - 1)
```

with, in `TopLevelDefs.lean`: `k8sProgram k₁ clients ops watchers wops steps₁ k₂ steps₂` the program
calling `Main(k1, clients, ops, watchers, wops, sched1, k2, sched2)`; `k8sAddrs k₁ k₂ :=
k8s_etcd3N.k8setcd3NAddrs k₁ ++ k8s_compactorN.addrs k₂` (each member's peer and client address and
bridge); `k8sDirs k₁ k₂ := k8s_etcd3N.k8setcd3NDirs k₁ ++ k8s_compactorN.dirs k₂`;
`k8s_compactorN.BootFacts := etcd_putgetN.BootFacts` (as etcd3's) and `k8s_compactorN.premises` putgetN's
at the compactor's members and token (etcd3's `premises` text at `k8s_compactorN.members`/`token`).
The compactor's `cluster3.BootFacts id₁ id₂ id₃`/`cluster3.premises clusterCfg` premises go. Every
premise keeps its kind: no new premise beyond `k₂`'s range; `Hlow` widens from `ids ++ [id₁, id₂, id₃]` to
`ids ++ ids'`.
