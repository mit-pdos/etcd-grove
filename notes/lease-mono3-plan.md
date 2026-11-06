# lease-mono3: a multi-member lease example, step 1 (monotone mode on `cluster3`)

Requested by the user 2026-11-06 (via etcd-grove-82), after S2–S4. Phase: **Scope** (drafted read-only; S2–S4 has since landed at lean `49b1b890c1`; line numbers are at that commit unless marked r2c). The cross-member lease-id finding of §7 is recorded as `issues/etcd-lease-id-mask-member-prefix.md`.

## Scope, a multi-member lease example, step 1 (monotone mode on `cluster3`)

**Base.** `lean` after `lease-snap` lands. R2c (`/shared/etcd-grove-r2cscope`, `f1baf1c5c3`) is merged when it lands (section 6).

### 1. What `alloc3` needs, and what changes

- **The monotone mode's prefix 0 does let every member grant.**
  - `srvMemberBoot_alloc`'s `hpfx` binds only in the revocable mode (`NewServerAlloc.lean:346`).
  - `kvPfx` is `0` outside the revocable mode (`InvRequest.lean:510`), so `kvInv_congr`'s prefix field (`NewServerAlloc.lean:73`) agrees across the three members.
  - In the monotone mode, `kvGrantIds` and `grantIdOwn` say nothing: only the revocable mode collects grant ids (`logRevGrantIds`/`rqRevGrantId`, `InvRequest.lean:481-490`; `grantIdOwn_nonRev`, `:542`).
  - `srvClusterBoot_alloc` already takes `lm` and the cluster's prefix `gp` (default 0), and at a granting mode it returns `if γk.lg then True else etcdKV` (`NewServerAlloc.lean:162-172`).
  - Each member keeps its own request-id prefix (`ρ.ids.pfx`, `memberBoot`, `etcdstart/Defs.lean:224-235`). In the monotone mode an id collision is only `ErrLeaseExists`, which the specs allow.
- **`alloc3` hardcodes the mode `.none` in three places:**
  - `memberBoot_of` takes `Hklg : γk.lm = .none` and closes with `lease.runCfg_none` (`Alloc3.lean:105,154`);
  - `alloc3Http` simplifies `etcdKV` out at `lg = false` (`:238`);
  - both posts return `etcdKV` (`:197,323`).
- **The change** (one spec, as `alloc1` does at `Alloc.lean:45-61`): `alloc3Http`/`alloc3` take `(lm : lease.Mode)`, `(hrun : lease.runCfg lm lm)` and `(hrev : lm ≠ .revocable)`. They post `memberBoot … cmp lm` and `(if decide (lm ≠ .none) then True else etcdKV …)`.
  - `memberBoot_of` takes `Hklg : γk.lm = m` and gives `srvMemberBoot_alloc`'s `hpfx` from `hrev`.
  - The four callers (putget3, partition/Alloc, restart/Run, `cluster3.StartCluster`) pass `.none` with `lease.runCfg_none`.
  - `NewServerAlloc.lean` is not touched.
- **Per member, nothing new.**
  - `lease.bootCfg`/`lease.srvInv` (`LeaseApi.lean:65,140`) and `lease.runCfg` (`LeaseRun.lean:77`) are per member and already take the mode.
  - Each member's lessor is monotone through `srvInv`'s `lessorModeIs (decide (m = .mono))`.
  - `srvStop.keep` does not depend on the mode; R2c moves it into `isServerBuiltC` (r2c `Defs.lean:300-322`).
  - `etcdstart.NewMember`/`StartMember` already take `lm` (`Spec/.../etcdstart/NewMember.lean:43,63,77`).
- **Cluster-wide, one change:** there is no client `etcdKV` at `lg = true`, so `clusterAt`'s `etcdKV` (`cluster3/Defs.lean:309`) must be gated by the mode.
- **Precedents traced.** leasegrant `Main` uses `alloc1 … .mono .mono (lease.runCfg_mono HnE)` and `kv_lease_served … .mono` (`leasegrant/Main.lean:100,155`). putget3, partition and K6's `MainPartition` run `alloc3` at `.none` (inside `StartCluster.lean:116,134,159,185`).

### 2. The Go program: `examples/etcd/leasecatchup/` (not `leasesnap`, which is S2–S4's Go test)

- **Setup.**
  - `cluster3.StartCluster(cfg)` with `SnapCount 1` and `SnapCatchUp 1`, as `linkv3p.go:65-71` and `k8s/compactor.go:63` do.
  - Two single-member clients: `etcdstart.NewClients([]string{cfg.Bridge3})` (c3) and the same at `Bridge1` (c1). `cluster3.NewClient`'s failover cannot be used: the Grant spec differs per member (`γl`), and `isGrpcRpcs` needs one spec at every address (`lessor__Leases.lean`).
- **Main:**
  1. `g1 := c3.Lease.Grant(TTL)`.
  2. `cluster3.PeerStep` cuts 3↔1 and 3↔2.
  3. Up to k filler grants through c1 (errors ignored). They grow the log, and the leader takes snapshots and compacts.
  4. Mend both links.
  5. Poll `c3.Lease.Leases()` (bounded) until it lists the last filler: member 3 has caught up, through a snapshot because the log was compacted. If it never does, return.
  6. `panic` unless that listing also lists `g1`.
- **Why the check is true of Go.** `LeaseLeases` reads only the local lessor (`v3_server.go:737-738`). Member 3 applied g1's grant before answering it. `applySnapshot` only installs snapshots above the applied index. `Recover` reloads every lease in the backend's lease bucket, so g1 is relisted.
- **Why it is provable.**
  - c3's Grant gives `∃ i, leaseGrantedAt γl₃ i g1` (`etcdLeaseGrantSpec`, `InvLeaseGrant.lean:57`).
  - `etcdLeaseLeasesSpec γl₃` with `G = [g1]` lists it (`:119`).
  - Monotonicity through the restore is S2–S4's frozen `Recover` mode premise (`mono → L ⊆ recs`), proved inside `run`.
- **What the TTL check would need is not available (flagged).**
  - A follower's `TimeToLive` forwards to the leader (`v3_server.go:636-648`); the examples' peers answer 404.
  - The trusted `leaseTimeToLive` says nothing of the TTL without `leaseTTLRow`, which holds only for a single-member cluster (`EtcdServer__leaseTimeToLive.lean:50-90`).
  - So "TTL ≥ request on the follower" is neither observable on the follower nor stateable. Asking for it is a hard stop (a new trusted statement).
- **What the snapshot proofs assume.** Sending is lease-generic: `sendMergedSnap.spec` mentions no lease; `merged_image`/`mergedObsM`/`bkRestAtM` take `lg` and `LeaseTable` (`SnapSendBranch.lean:656-675,1009`). Receiving and `applyAll`/`applySnapshot` hold in every lease mode since S2–S4.
  - The remaining `lg = false` facts are on the auth-on path only (`ApplyAllSnapOn.lean:115-135`, `UberOn.lean:75`). Auth on grants no lease (`lease.bootCfg_auth`, `LeaseApi.lean:102`), so they do not block this example.
  - `specSnapM` requires a first start (`γr.raft.pre = []`). That holds: nothing restarts.
  - Unknown: `cmp = true` with the monotone mode (`KVApply.lean:185` takes both `false`). Run this example at `cmp = false`.
- **Go test, before any Lean ("Go first").**
  - `leasecatchup_test.go` counts "sending merged snapshot", "applied snapshot" and "restored lease store", as `linkv3p_test.go:912-956` and `leasesnap_test.go:245` do.
  - It fails if no run sends member 3 a snapshot.
  - Watch the 30 s `releaseDelayAfterSnapshot` pause (`linkv3p_test.go:122`).
- **Time budget for `leasesNoExpiry`:** roughly start-up + (1 + k) × 5 s + polls × 5.25 s, well under the TTL. Recommended TTL: 3600 s.

### 3. The closed theorem (draft)

```lean
theorem etcd_leasecatchup_safe [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [Float64ToInt64Semantics] [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC leasecatchupGF,
      ContextReadErrs (GF := leasecatchupGF) (hG := heapAtLcu hG lctx))
    (Hcec : ∀ hG : HeapGS .hasLC leasecatchupGF,
      ContextErrsClient (GF := leasecatchupGF) (hG := heapAtLcu hG lctx))
    (id₁ id₂ id₃ : w64) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hbf : cluster3.BootFacts id₁ id₂ id₃ ps ctxs boot)
    (Hck : ckptEffectsOk) (Haf : authRecordsFit) (Hbuq : apply.backendUnderQuota)
    (Hrf : grpcRepliesFit) (Hdbo : storage.diskOk)
    (Hlp : leasePeersOk) (Hlne : lease.leasesNoExpiry)
    (HNs : prometheus.namesUnclaimed leasecatchupProgram leasecatchupNames)
    (HAs : addrsUnclaimed leasecatchupProgram leasecatchupAddrs)   -- 3 peer, 3 client, 3 bridge
    (HDsNd : leasecatchupWalDirs.Nodup)
    (HDs : walDirsAbsent leasecatchupProgram leasecatchupWalDirs)
    (n : Nat)
    (Hprem : ∀ hG : HeapGS .hasLC leasecatchupGF,
      ⊢ cluster3.premises (GF := leasecatchupGF) (hG := heapAtLcu hG lctx)
          etcd_leasecatchup.clusterCfg n id₁ id₂ id₃ ps ctxs boot)
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([leasecatchupProgram], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 28) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧ (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false)
```

It has the premises of `k8s_compactor_partition_safe`, plus leasegrant's `Hlp`/`Hlne`, minus `steps`/`Hafter` (Main uses fixed steps and `time.Sleep`). `etcd_adequate_members` applies with `Bs := bridges`, as A3 does.

Proof-wise, the trust base is what leasegrant already reaches since S2–S4 (the generic `run`). What is new is a closed result over a configuration where the leased restore actually happens in Go. Say so in its docstring.

### 4. Statements touched

| statement | file | change | kind |
|---|---|---|---|
| `alloc3`, `alloc3Http`, `memberBoot_of` | `etcdstart/Alloc3.lean:99,163,291` | `lm`, `hrun`, `hrev`; `memberBoot … cmp lm`; `etcdKV` gated | etcdstart API (`etc/api/etcdstart.txt:24`, `interface/…/Alloc3.txt`): a hub request to 82 |
| `cluster3.memberServed` | `cluster3/Defs.lean:162` | `(m := .none)`; KV registrations become `etcdLeaseServedAt m …` plus `client.etcdLeaseReadAt` (Q2) | `.none` reduces to today's text by `rfl` |
| `memberAt`, `clusterAt`, `clusterUp` | `cluster3/Defs.lean:267,297,314` | `(m := .none)`; `etcdKV` by a `match` on `m` | the same |
| `cluster3.StartMember.spec` | `Spec/…/cluster3/StartMember.lean:39,83` | post `memberServed … lm`; premise `lm ≠ .none → leasePeersOk` | FROZEN (hub step 7 E1) |
| `cluster3.StartCluster.spec` | `Spec/…/cluster3/StartCluster.lean:42,63` | binder `lm`, `lease.runCfg lm lm`, `lm ≠ .revocable` (a scope premise, removed in step 2), gated `leasePeersOk`; post `clusterUp … lm` | FROZEN (E2); a hub request |
| StartMember/StartCluster proofs | `StartMember.lean:136`, `StartCluster.lean:116-185` | `srvLeaseRd` kept (today `-`); lease serving by `kv_lease_served` (`ServedLease.lean:107`) or an `etcd_kv_started` analogue | proofs |
| partition `startCluster`, K6 `MainPartition`, putget3/restart | callers | pass `.none`; statement text unchanged | proofs only |
| unchanged | | `NewServer.specG`, `lease.bootCfg`/`srvInv`/`runCfg`, `memberBoot`/`memberBuilt`/`memberUp`, every S2–S4, lease-grant and lease-expiry frozen statement, raft/backend APIs | |

### 5. Trust base and sizes

- **No new axiom or trusted model is expected.** The expected trust base is linkv3p's (633 axioms) ∪ leasegrant's lease axioms (for example `EtcdServer.leaseTimeToLive.wp_proof`, through `kv_lease_served`). `sorry`s: none, because the monotone mode does not reach `srvRevokeOpen_open`.
- `etc/gen-init.py` may give the new package init axioms; check at Draft. The new collection is `etc/tcb-collections/leasecatchup.txt`.
- **Sizes (est.):**

| part | size |
|---|---|
| Go program + stats test | 150 + 250 lines |
| goose project, init, `PkgTable` (copied) | ~800 lines |
| `alloc3` | ~70 lines |
| cluster3 definitions + 2 proofs | ~250 lines |
| example `Defs`/`Main`/`MainLinked`/`Adequacy`/`Results` | ~900 lines |
| callers | ~20 lines |

  The build touches etcdstart and cluster3 importers, not `NewServerAlloc`.

### 6. Relation to R2c (etcd-grove-83, branch `r2c`)

- **Builds on:** R2c-4's `memberUp` gains `srvStopRight` (r2c `etcdstart/Defs.lean:356`). This example never stops a member and drops it.
  - `cluster3.StartMember`'s `icases … HWR, -⟩` absorbs it today. My change to name `srvLeaseRd` there must keep a trailing `-`: a small textual merge.
- **No conflict:**
  - R2c-1 changes only `srvClusterBoot_alloc`'s proof; this stage does not edit that file.
  - R2c-3 removes `memberBuilt`'s `K`; this stage does not touch `memberBuilt`.
  - `srvStop.scope` (r2c `InvRestart.lean:208`: auth off, `cmp = false`) does not depend on the lease mode.
- **Shared file:** `alloc3` is also R2d's A4 base (`restart/Run.lean`). This stage keeps the `.none` instance unchanged in meaning.
- **Order:** draft now on lease-snap + lean, merge R2c when it lands, land after it. Its frozen batch and this stage's do not overlap.

### 7. Step 2 (later): the revocable mode across members

- `kvGrantIds`'s single prefix `kvPfx` (`InvRequest.lean:510-520`) becomes the set of member prefixes. `srvMemberBoot_alloc`'s `hpfx` and `kvInv_congr`'s prefix agreement must then become member-independent.
- `leaseIdMask_nodup_of_pfx` (`:649`) holds within one prefix only. The mask drops bit 63, which is bit 15 of a member's 16-bit prefix (`idPfxOf`, `idutil/Defs.lean:101`). So two members whose ids agree in the low 15 bits generate the same masked lease ids.
  - Go then answers `ErrLeaseExists`, or re-grants a revoked id: no wrong result.
  - **Finding:** this is not recorded. It should go in `nonissues/`, next to `etcd-request-id-member-prefix.md`.
  - Step 2 then needs either a scope premise on `BootFacts` (low 15 bits distinct) or a per-prefix `U`.
- `srvRevokeOpen_open` is still a `sorry` (its discharge waits on P1).
- `leaseTTLRow` is single-member. A multi-member `TimeToLive` row is a trusted restatement: a hard stop, with an `axiom` attack before its Freeze.

### 8. Questions for the user (recommendation first)

1. **The check.** Recommended (A): member 3 grants a lease, and its own listing still has it after its snapshot restore. The alternatives:
   - (B) a lease granted through member 1 is listed by member 3 once member 3 lists a later grant. This needs new cluster-level grant and lessor vocabulary, and changes the frozen `etcdLeaseGrantSpec`/`etcdLeaseLeasesSpec`: a later step 1b.
   - (C) TTL on the follower: infeasible (section 2), a hard stop.
2. **Serving in the monotone mode.** Recommended: cluster3 registers the lease specs in place of the KV ones, following lease-grant's (c). Today's proof already registers KV and watch at any `lm`, vacuously.
3. **Partition steps.** Recommended: fixed `PeerStep`s in `Main`, not `Main(sched)` with a `Partitioner`.
4. **`StartCluster.spec`'s premises.** Recommended: `lease.runCfg lm lm`, the scope premise `lm ≠ .revocable` (cites this Scope), and `leasePeersOk` gated on `lm ≠ .none`, so no existing closed theorem gains a premise.
5. **TTL.** Recommended: 3600 s, for margin on `leasesNoExpiry`.
6. **Compaction mode.** Recommended: `cmp = false` only.
7. **Name.** Recommended: `examples/etcd/leasecatchup`.

No hard stop is in the recommended path. Hard stops arise only from 1(C), or from step 2's new trusted TTL row.
## Go first (2026-11-06)

**Outcome: the check holds in Go and the run exercises the leased restore.** `examples/etcd/leasecatchup/` (commit `25f0f94fac`): `leasecatchup.go` (`Main`, 182 lines) and `leasecatchup_test.go` (`TestMemberIDs`, `TestMainRun`, 216 lines).

- **Shape.** `Main()` is `run(zap.NewNop())`; `run(lg) int` is §2's six steps (Checked / StartFailed / NotCaughtUp), so that the test runs Main's body with a counting logger (linkv3p's precedent). The Draft specifies `run` (or folds it into `Main`). Ports 24011-13 (peer), 24021-23 (client), 24031-33 (bridge). TTL 3600, k = `fillers` = 20, 60 polls 250 ms apart. Bridges are returned by `StartCluster` and unused.
- **Runs** (go1.27.3, `go test ./etcd/leasecatchup -count=1 -v`, three times; all PASS; `go vet` clean):

| run | `run` took | sent merged snapshot (to member 3 / others) | applied snapshot | restored lease store | raft restores on member 3 |
|---|---|---|---|---|---|
| 1 | 6.86 s | 1 / 0 | 1 | 1 | 1, index 29 |
| 2 | 1.58 s | 1 / 0 | 1 | 1 | 1, index 29 |
| 3 | 1.85 s | 1 / 0 | 1 | 1 | 1, index 29 |

  Earlier development runs: 1.6, 7.6, 1.3, 6.6 s, the same counts. The ~5 s extra in some runs is presumably one filler timing out (`RequestTimeout`) while a new leader is elected (member 3 led at the cut).
- **Why k = 20 suffices.** At `SnapCount 1` the leader snapshots every second applied entry and compacts its log to `SnapCatchUp` (1) entry below it, so two applied fillers already compact member 3's index out; 20 leaves margin for fillers lost to a re-election. The restore at index 29 (about 9 entries before the cut, then the 20 fillers) holds every filler. The 30 s `releaseDelayAfterSnapshot` pause would defeat this only after an earlier snapshot (a member lagging at start-up); none happened in any run. If one did, member 3 would catch up by entries: `Main` would still pass, the test would fail (no restore above the fillers' count).
- **What the test checks** (beyond `run` returning Checked): a snapshot sent to member 3 (the `to` field of "sending merged snapshot", against the ids `membership.NewClusterFromURLsMap` computes); raft on member 3 restoring a snapshot above index k ("`<id> [commit: c] restored snapshot [index: i`"; raft logs a restore twice, the "lastindex" line is skipped); more "restored lease store" than snapshots sent to members 1 and 2. The last is how member 3 is identified: etcd's "applied snapshot" and "restored lease store" name no member.
- **A race in the counts.** `run` returns once member 3's lessor lists the filler. `applySnapshot` logs "applied snapshot" in a `defer`, after the KV store's restore, sometimes after `run` returns (one development run counted 0). The test waits for it (at most 5 s).
- **Goose.** The pinned translator (Perennial `84d5380639`, built from `/shared/perennial-84d538063`), with leasegrant's lean roots and the repository's `Code/` configuration, translated the package (Code 598 lines, GeneratedProof 27) with no error or unsupported construct. Not added to `etc/goose.py` (the Draft does that).
- **What the Scope got wrong or left out.** No error. Two small points: §2's time budget, (1 + k) × 5 s, is an upper bound; the measured runs take 1.3-7.6 s. `Main` needs the `run(lg)` split for the test, which adds one function to specify.
