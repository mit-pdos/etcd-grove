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

## Draft pass 1 (2026-11-06)

Pass 1 of the Draft (`notes/spec-first-plan.md`, "A large Draft: pass 1 small, pass 2 wide"): only
what more than one package names, as statements; proofs that break are `sorry -- DRAFT lease-mono3`.
Branch `lease-mm`.

### Frozen and exported changes, old → new

| statement | old | new | cause |
|---|---|---|---|
| `etcdstart.memberBoot_of` (`Alloc3.lean`, etcdstart API) | `Hklg : γk.lm = .none`; post `memberBoot … id cmp` | `(lm) (hrun : lease.runCfg lm lm) (hrev : lm ≠ .revocable) (Hklg : γk.lm = lm)`; post `memberBoot … id cmp lm` | Scope §1; `srvMemberBoot_alloc`'s `hpfx` from `hrev` |
| `etcdstart.alloc3Http` (private), `etcdstart.alloc3` (etcdstart API; hub request accepted by 82) | `(cmp := false) (cret := 0)`; posts `memberBoot … cmp`, `etcdKV ρ₁.rd.kv …` | `… (cmp := false) (cret := 0) (lm) (hrun : lease.runCfg lm lm) (hrev : lm ≠ .revocable)`; posts `memberBoot … cmp lm`, `(if decide (lm ≠ .none) then True else etcdKV ρ₁.rd.kv …)` | Scope §1 (alloc1's shape); proved, no sorry |
| `cluster3.StartMember.spec` (FROZEN, hub step 7 E1) | post `memberServed γn s id ρ E₀ client` | premise `(lm ≠ .none → leasePeersOk)` after `v3rpc.ServerMethodSets`; post `memberServed γn s id ρ E₀ client lm` | Scope §4, Q2 |
| `cluster3.StartCluster.spec` (FROZEN, hub step 7 E2) | binders `… (lg) (cmp)`; post `clusterUp cfg cmp … srvs brs` | binder `(lm : lease.Mode)` after `cmp`; premises `lease.runCfg lm lm → lm ≠ .revocable → (lm ≠ .none → leasePeersOk)` after `v3rpc.ServerMethodSets`; post `clusterUp cfg cmp … srvs brs lm`; the docstring cites the Scope for `lm ≠ .revocable` | Scope §4, Q4 |
| `cluster3.memberServed`, `memberAt`, `clusterAt`, `clusterUp` (`cluster3/Defs.lean`) | — | last parameter `(m : lease.Mode := .none)`; the KV registrations become `servedRegs m …` (new, below); `clusterAt`'s `etcdKV` by a `match` on `m` | Scope §1, §4, Q2 |
| `cluster3.servedRegs` (new, `Defs.lean`) | — | `servedRegs m c s E ρ cid mid rest`: at `.none` the five KV registrations then `rest`; otherwise `client.etcdLeaseReadAt c ∗ etcdstart.etcdLeaseServedAt m c s E ρ ρ.rd cid mid ∗ rest` (`kv_lease_served`'s post) | so that `.none` is today's text by `rfl` (the `∗`s associate as before) |

No other frozen or exported statement changed (the batching rule had nothing more to apply).
`cluster3/Defs.lean` now imports `etcdstart.ServedLease` (importable, `etc/api/etcdstart.txt`).
Callers: `putget3/Main`, `restart/Run` pass `false 0 .none lease.runCfg_none (by decide)` to `alloc3`
and simplify its `if` away; `partition/startCluster`, `k8s/compactor/MainPartition` pass `.none`,
`lease.runCfg_none`, `(by decide)`, `(fun h => absurd rfl h)`; their statements are unchanged.
(`partition/Alloc.lean` names `alloc3` only in comments.)

**The `rfl` checks.** At `.none` each definition is its old text: `memberServed_none`,
`memberAt_none`, `clusterAt_none`, `clusterUp_none` (`Defs.lean`, theorems proved by `rfl`, named so
that proofs can `simp only [..._none]`; the brief asked for `example`s).

**DRAFT sorries** (all `-- DRAFT lease-mono3`): `StartMember.wp_proof`'s `.mono` and `.revocable`
cases, `StartCluster.wp_proof`'s `.mono` case (its `.revocable` case is `hrev`'s; its and
StartMember's `.none` cases are the old proofs, checked). Reach: below.

### Findings for pass 2 (not decided here)

1. **A thread token for the lease reads' gRPC slot.** `kv_lease_served` takes `threadTok` for the one
   gRPC slot (`raftLeaseRead_server`'s `E.RD ∗ threadTok`). leasegrant's `Main` gets it by forking
   `go holdToken()` (`wp_fork_tok_self`). `cluster3.StartMember`'s Go forks only `go gs.Serve(cl)`,
   whose spec (`grpc.Server.Serve.spec`) returns `True`, and its one `threadTok` goes back to
   `StartCluster` through `srvGoRes` (for the next member). So `StartMember.spec` at `.mono` has no
   token for the slot. Options: (i) Go: `go holdToken()` in `cluster3.StartMember` (a shared
   library: a re-translation; harmless at `.none`); (ii) a mode-gated `threadTok` premise in the
   frozen `StartMember.spec`/`StartCluster.spec` and `holdToken`s forked by the example's `Main`
   (a Go change to `leasecatchup.go`); (iii) a serving lemma whose slot needs no token when the
   TTL read is not registered (and `memberServed` without `client.etcdLeaseReadAt`, which
   leasecatchup does not use). (i) changes no statement. (ii) is a frozen change, (iii) an exported
   one: both go to the user.
2. **The watch stream in the monotone mode.** `memberServed`/`memberAt` keep the `Watch` stream and
   `noRefusalAt` in every mode (Q2 replaces only the KV calls). Today's proof gets the stream from
   `etcd_kv_started`'s `grpcStreamServerAt`; `kv_lease_served` returns none. Pass 2 needs a serving
   lemma that returns it too (`etcd_kv_started_with` has the shape). If that is not available, the
   choice is (iii)'s kind: an exported change to the user.

### Pass-2 work list

- **(a) cluster3** (owns `Proof/.../examples/lib/cluster3/StartMember.lean`, `StartCluster.lean`,
  and, if needed, `Defs.lean` below the statements): prove `StartMember.wp_proof` at `.mono` (and
  `.revocable`: `kv_lease_served` covers every mode; the scope premise is only `StartCluster`'s), with
  `memberUp`'s `srvLeaseRd` (today `-`), `kv_lease_served` for the lease registrations, the watch
  stream and `etcd_noRefusal` (findings 1 and 2); prove `StartCluster.wp_proof` at `.mono`: `alloc3 …
  .mono hrun hrev`, `StartMember` at `.mono` with `HlP`, no `etcdKV` (the `if`), `clusterAt … .mono`.
  Keep a trailing `-` in `memberUp`'s `icases` (R2c's `srvStopRight`, §6).
- **(b) the example `examples/etcd/leasecatchup`** (owns `etc/goose.py`'s new project and the
  translation `Code/`/`GeneratedProof/` of the package, `Proof/.../examples/etcd/leasecatchup/`
  `Init.lean` (`etc/gen-init.py`, its `SPECIAL` if needed), `PkgTable`, `Defs`, `Main` and `run`,
  `MainLinked`, `Adequacy`, `Results`, the link generation for it, and
  `etc/tcb-collections/leasecatchup.txt`): §3's theorem `etcd_leasecatchup_safe`, over
  `StartCluster.spec` at `.mono` (`lease.runCfg_mono Hlne`, `(by decide)`, `fun _ => Hlp`), two
  `etcdstart.NewClients` of one bridge each (the bridge forwards `servedRegs`'s registrations,
  `isGrpcRpc_forwards`), `Grant`/`Leases` at `etcdLeaseGrantSpec`/`etcdLeaseLeasesSpec` of member
  3's `E.γ.leases`, `PeerStep`. Depends on (a)'s statements only (built now).
- **(c) everything else**: `etcdstart` (owns `ServedLease.lean`): the serving lemma findings 1–2
  need, if (a) needs one; the decision on finding 1 (with the user if (ii) or (iii)), and, for (i),
  the Go change to `examples/lib/cluster3/cluster3.go` with its re-translation (`etc/goose.py
  --project` of the examples) before (a) proves `StartMember`.

## Draft pass 2(c) (2026-11-06)

The serving lemma findings 1–2 need, an addition to etcdstart's API (accepted by etcd-grove-82,
2026-11-06), in `etcdstart/ServedLease.lean` (already importable; `etc/api/etcdstart.txt` unchanged):

```lean
theorem kv_lease_served_watch (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (γr : ReadNames) (gs : Loc) (lis : GoInterface) (addr : GoString) (cid mid : w64)
    (R : v3rpc.WSrv GF) (Hrb : receiptBound GF ≤ 2 ^ 48) (HT : threadBound GF ≤ 2 ^ 30 - 1)
    (Hrf : grpcRepliesFit) (hP : leasePeersOk) (hρ : ρ.rd = γr) (m : lease.Mode)
    (hm : ρ.rd.kv.lm = m)
    (hset : go.typeSetContains
      (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.watchServer.ty)
      go_etcd_io.etcd.api.v3.etcdserverpb.WatchServer.ty = true) :
    isPkgInit v3rpc ∗ isPkgInit etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗ srvLeaseRd s E m ∗ threadTok ∗
        kvServeStocks s E γr ∗ grpcUp s E ρ γr gs lis addr cid mid R ⊢
      |={⊤}=> grpcServeTok gs lis ∗ srvGoRes s ∗ client.etcdLeaseReadAt addr ∗
        etcdLeaseServedAt m addr s E ρ γr cid mid ∗
        (∃ pw : Loc, v3rpc.isWatchServer pw R) ∗ ⌜R.s = s ∧ R.E = E⌝ ∗
        isGrpcStreamMd addr "/etcdserverpb.Watch/Watch" (v3rpc.watchUp R)
          (fun md γs Dn => v3rpc.watchStreamSpec γs R.γ R.s (auth.mdTokenOf md) R.cid R.mid Dn) ∗
        ⌜noRefusalAt addr⌝
```

Why this shape:
- **`kv_lease_served`'s premises, unchanged, plus `hset`** (the caller's `Hms.watch_impl`): the
  `threadTok` for the one gRPC slot stays a premise (finding 1; the caller's `go holdToken()`, not
  this pass's). The watch run slot needs no new premise: it is made of two of `grpcUp`'s 64
  watchable-store readers and one of `kvServeStocks`' `E.RD` (one of the two `kv_lease_served`
  dropped), under `HT` (`threadBound ≤ actualMaxReaders`).
- **The post is what `cluster3.memberServed` needs at a lease mode from the serving step**:
  `servedRegs m`'s lease registrations, the watch stream with its server (`∃ pw` and
  `R`'s facts, which the caller packs under `memberServed`'s `∃ pw R`), `noRefusalAt` (from
  `grpcUp_noRefusal`, before `grpc.start`: authentication off from `isServerReq_authOff`), and
  `srvGoRes s` back to the caller, which `grpcUp` holds and `memberServed` keeps (`kv_lease_served`
  dropped it: its callers had theirs elsewhere).
- **Over `grpcUp`, as `kv_lease_served`**, not over `Server`'s raw post as `etcd_kv_started_with`:
  `grpcUp` holds the Lease service (`grpcLeaseUp`) the lease registrations need; `StartMember`
  packs `wp_Server`'s post into `grpcUpM E.authOn` and `grpcUpM_false` as `etcdstart.Serve` does.
- **One proof**: `kv_lease_served`'s body became the private `kv_lease_served_core`, whose post also
  returns `srvGoRes`, the stream registrations (`etcd_kv_started_with`'s `grpcStreamServerAt`), the
  watch server and stream interceptors and the one watch run slot; `kv_lease_served` (statement
  unchanged) drops them, `kv_lease_served_watch` runs `v3rpc.etcd_watch_served_chain` on them.

Proved, no `sorry`, no new axiom (it uses `etcd_noRefusal`, which `StartMember`'s `.none` case and
linkv3p's trust base already rest on); `kv_lease_served`'s statement and its interface are unchanged. Left to (a): in `StartMember`
at a lease mode, pack `wp_Server`'s post into `grpcUp` (as `etcdstart.Serve` does), take the
`threadTok` from the new `go holdToken()` (finding 1, option (i)), and apply `kv_lease_served_watch`
with `Hms.watch_impl`.

## Draft pass 2(b) (2026-11-06)

Pass 2(b) of the Draft: the example `examples/etcd/leasecatchup` (branch `lease-mm`), over pass 1's
statements as they stand.

**What was added.**

- `etc/goose.py`: project `leasecatchup` (leasegrant's lean roots); the translation
  `Code/`/`GeneratedProof/github_com/mit_pdos/etcd_grove/examples/etcd/leasecatchup.lean`
  (`etc/goose.py --check --project leasecatchup` passes).
- `etc/gen-init.py`: the package in `ROOTS` and `PROGRAMS`; its generated `Init.lean` (fact `True`,
  no new init axiom) and `PkgTable.lean`. `Base.lean` (the package fact) imports cluster3's `Base`
  as well as etcdstart's.
- One spec and one proof per Go function (the layout), `Spec/…/leasecatchup/` and
  `Proof/…/leasecatchup/`:
  - `config` (returns `clusterCfg`, `Defs.lean`, with `clusterCfg_ok : cluster3.cfgOk clusterCfg`);
  - `grant`/`leases` (`lessor.Grant`/`lessor.Leases` through the client's `Lease` field, in a
    request-timeout context: for an `isNewClient cl eps V`, a `Spec` registered at every endpoint and
    the caller's `Q`, the reply's id field (`ID`, read-only) or listing slice (`Leases`, read-only)
    with `Q`, or an error);
  - `listed` (returns `decide (id ∈ ids)` over a read-only listing);
  - `run` (Scope §2's six steps) and `Main` (`run(zap.NewNop())`); both specs below.
- `MainLinked.lean` (by hand, as leasegrant's: `etc/gen-link.py` has no mode combining several
  packages' Links), `Adequacy.lean`, `Results.lean` (`leasecatchup_Main`, `etcd_leasecatchup_safe`,
  `#print axioms` of each), and the collection `etc/tcb-collections/leasecatchup.txt`.

**`run.spec`** (and `Main.spec`, the same without `lg`): `StartCluster.spec`'s premises at
`clusterCfg` (`cluster3.BootFacts`, the thread and receipt bounds, the write budget, `ckptEffectsOk`,
`authRecordsFit`, `apply.backendUnderQuota`, `grpcRepliesFit`, `storage.diskOk`,
`v3rpc.ServerMethodSets`), leasegrant's `leasePeersOk` and `lease.leasesNoExpiry`, the client's
context premises (`ContextReadErrs`, `ContextErrsClient`, `errors.AsTarget` of `rpctypes.EtcdError`);
pre `isPkgInit leasecatchup ∗ cluster3.startRes clusterCfg ∗ threadTok ∗ cluster3.premises
clusterCfg N id₁ id₂ id₃ ps ctxs boot`; post `∃ r : w64, RET #r; True` (`Main`: `RET #(); True`).

**`run`'s proof** (complete, no `sorry` of its own): `StartCluster` at `cmp = false`, `.mono`,
`lease.runCfg_mono Hlne`, `(by decide)`, `fun _ => Hlp`; from `clusterUp … .mono`, members 1 and 3's
`servedRegs .mono` unfolded to `etcdLeaseGrantAt` (the grant at `etcdLeaseGrantSpec E.γ.leases`, the
listing at `etcdLeaseLeasesSpec E.γ.leases`), forwarded to the bridges (`isGrpcRpc_forwards`); two
`NewClients` of one bridge each (`plainEndpoints_singleton`); `grant(c3)` keeping
`∃ i, leaseGrantedAt E₃.γ.leases i g1`; `PeerStep` four times over the members' `srvPeerCtl`s; the
fillers at member 1's grant spec with `Q = True`; each poll's `leases(c3)` handing in `[g1]`, so the
listing has `g1` and the panic branch is dead. As the Scope said, the proof does not reason about
the catch-up: member 3's listing lists `g1` because its lessor's history is monotone, which S2–S4
proved inside `run` of the server (the `Recover` premise).

**Frozen and exported statements.** None changed: the batching rule had nothing to apply. No
statement of another package was needed beyond those pass 1 built (`StartCluster.spec` at `.mono`,
`clusterUp`/`clusterAt`/`memberAt`/`servedRegs`, `NewClients.spec`, `PeerStep.spec`,
`lessor.Grant.spec`/`lessor.Leases.spec`, `etcdLeaseGrantSpec`/`etcdLeaseLeasesSpec`,
`etcdstart.etcdLeaseServedAt`/`etcdLeaseGrantAt`, `isGrpcRpc_forwards`, `isGrpcRpcs`).

**DRAFT sorries.** None in this example's files. Its results reach pass 1's
`-- DRAFT lease-mono3` sorries in cluster3 (`StartMember.wp_proof`'s `.mono` case,
`StartCluster.wp_proof`'s `.mono` case), which pass 2(a) proves; the collection's baseline records
them (below).

**Trust base.** No new axiom, trusted model or non-DRAFT `sorry`: the package initializer is
generated with no init axiom, and the example's own files have no `sorry`. `Results.lean` built
(lean `19669977e6` plus this pass, with pass 2(a)'s cluster3 edits as they stood then): `#print
axioms etcd_leasecatchup_safe` lists `sorryAx` (pass 1's DRAFT sorries) and the axioms of linkv3p
and leasegrant's lease reads, as Scope §5 expected. The collection
`etc/tcb-collections/leasecatchup.txt` has its `roots` line but no baseline yet:
`etc/tcb-report.py` needs every root module up to date, and cluster3's `StartCluster.lean`, which
pass 2(a) is editing in the worktree, did not build when this pass ended. Run
`LAKE_OPTS=--packages=… etc/tcb-report.py --collection etc/tcb-collections/leasecatchup.txt --check
--update` once it does (after pass 2(a), whose sorries it would record otherwise).

**Gates to note.** `etc/bounds-check.py --check` counts the new package's specs (`spec-receipt` 4,
`spec-thread` 2, as leasegrant's `spec-receipt 2`/`spec-thread 1`, which the baseline lists): the
baseline needs the package's lines at landing (`etc/bounds-baseline.txt`, not changed here).
`etc/goose.py --check --project leasecatchup` and `etc/gen-init.py --check` pass.

## Draft pass 2(a) (2026-11-06)

`cluster3`'s two proofs at the lease mode. No `sorry` is left in them, and no statement changed.

- **The Go change (R1, accepted by etcd-grove-82 on 2026-11-06).** `cluster3.StartMember` runs
  `go holdToken()` just before `go gs.Serve(cl)`. `holdToken` sleeps forever and touches no lock;
  it and its doc comment are leasegrant's and leasekv's. The translation was regenerated
  (`etc/goose.py --project cluster3`: `Code/` only, `GeneratedProof/` unchanged), `etc/goose.py
  --check` passes, and `etc/gen-init.py --check` reports nothing to regenerate. The reasoning is in
  `notes/decisions.md`, "A thread token for a cluster member's lease reads".
- **`holdToken`**: `Spec/.../cluster3/holdToken.lean` and `Proof/.../cluster3/holdToken.lean`
  (leasegrant's spec and proof). It is linked in `etc/link-lean-first-cluster3.txt` as a callee of
  `StartMember`, and `Link.lean` is regenerated. `StartMember.wp_proof` takes `wp_holdToken` as a
  last hypothesis. Its spec is unchanged.
- **`StartMember.wp_proof`** is one proof for every mode. The mode's KV names come from
  `memberBoot`'s `lease.runCfg` (`lease.runCfg_lm`). The proof runs `NewMember` and `Start` at
  `lm`, names `memberUp`'s `srvLeaseRd` (`#HLR`, previously `-`), and forks `holdToken` with
  `wp_fork_tok_self`. It then splits on `lm`:
  - **`none`**: the token is dropped. The rest is the old ghost step (`memberServed_none`).
  - **`mono` and `revocable`**: `v3rpc.Server`'s and `Listen`'s results are packed straight into
    `etcdstart.grpcUp`, with `grpcLeaseUp` from `Server`'s lease registrations. Then comes
    `etcdstart.kv_lease_served_watch` (`Hms.watch_impl`, `HlP`, the token in the gRPC slot). Its
    post gives `memberServed … lm` with `srvGoRes` included, through the private
    `servedRegs_of_lease`.
  - **Two differences from the plan.** The plan said to pack the results into `grpcUpM E.authOn`
    and then apply `grpcUpM_false`, as `etcdstart.Serve` does. The direct `grpcUp` is shorter:
    `StartMember`'s configuration is already `grpcCfgOk_of_started_w`'s, at `srvKVAns`.
    `.revocable` needs no `hrev`: `kv_lease_served_watch` covers every mode, and the scope premise
    is only `StartCluster`'s.
- **`StartCluster.wp_proof`** is one proof for `none` and `mono`; `revocable` is excluded by `Hrev`.
  It calls `alloc3 … lm Hrun Hrev`, then `StartMember` at `lm` with `HlP`. Each member's
  registrations are split off `memberServed` (`servedRegs_sep`) and put back under `memberAt`
  (`servedRegs_join`), both private lemmas proved by cases on the mode. `clusterAt`'s `match` is
  resolved at the end by `cases lm`:
  - `none` keeps `alloc3`'s `etcdKV`;
  - `mono` drops `alloc3`'s `if` (`True`).
- **R2c's merge.** In `StartMember`, `memberUp`'s `icases` now ends `…, HWR, #HLR⟩`. R2c's
  `srvStopRight` follows `srvLeaseRd`, so merging R2c must change it to `…, HWR, #HLR, -⟩`. Until
  then, `#HLR` fails to build: it would bind a non-persistent `srvLeaseRd ∗ ∃ dd, srvStopRight …`.
  `StartCluster` does not destructure `memberUp`.
- **Frozen or exported statements changed:** none. `StartMember.spec` and `StartCluster.spec` keep
  pass 1's text. The new `holdToken.spec` is `cluster3`'s, which has no API list. The closed
  theorems are unchanged: `git diff lean` of partition's, k8s compactor's and putget3's
  `Results.lean` is empty, and no `interface/` file of theirs exists.
- **Trust base.** `etc/tcb-report.py --check` matches `etc/tcb-baseline.txt` (785 axioms, 3
  `sorry`s): no new axiom, trusted model or `sorry`. putget3's collection matches its baseline (611
  axioms, no `sorry`). No root reaches a `sorry -- DRAFT lease-mono3` any more.
- **Collection growth, for etcd-grove-82 (baselines not updated).** linkv3p's and k8scompactor's
  collections each gain two axioms that are already in the repository's trust base:
  `EtcdServer.leaseTimeToLive.wp_proof` and `sort.Sort.wp_anyLess`. Both are leasegrant's lease-read
  axioms, reached through `kv_lease_served_watch`.
  - **Cause.** `StartMember.spec` quantifies over `lm`. Its one linked proof therefore rests on the
    lease branch's axioms, even for callers that use only `.none`. Pass 1's DRAFT `sorry`s hid this.
  - **Options.**
    - Accept the growth (`--check --update`).
    - Split the frozen `StartMember.spec`/`StartCluster.spec` per mode, a frozen change. The
      `.none` instance would then link without the lease axioms.
  - **Left open:** the choice. leasecatchup's collection still has no baseline (pass 2(b)'s);
    `--check --update` it now that cluster3 builds.
- **Go checks (82's condition on R1; go1.27.3, `TMPDIR=/shared/tmp`, `-count=1`).** `go vet` is clean
  for cluster3, partition, putget3 and `k8s/compactor` (its own module, which replaces the examples
  by `../..`).
  - **Pass**: k8s compactor (`TestCompactor`, `TestHistory`, `TestMissingKey`, `TestShared`,
    `TestMainPartition`, `TestMemberIDs`); putget3 (`TestPutGet3`, `TestMemberIDs`); partition's
    `TestMemberIDs`, `TestMainRun`, `TestClientCuts`, `TestWriteOnce`, `TestWatchFailover` and
    `TestMainWatch`.
  - **Fails, and not because of R1**: partition's `TestFailover`. It hangs in its control loop,
    which waits for all three clients to be served after the last stall, until the test times out
    (554 s, then 571 s alone). It fails the same way at `lean` `6691b46860`, which has no
    `holdToken` (575 s), so R1 did not cause it. Its cause is not investigated: it may be machine
    load or a regression on `lean`. It needs a look before landing, under the gates.

## Review round 1 fixes (2026-11-06)

The findings of `notes/spec-review/lease-mono3-r1.md` (round 1, on `2a4632ab5c`), fixed on branch
`lease-mm` as DRAFT under the batching rule: each frozen, exported or new statement that changed is
listed old → new with its cause. No axiom, trusted model or `sorry` was added.

### Frozen statements (text only; docstrings and comments)

| statement | old | new | cause |
|---|---|---|---|
| `cluster3.StartMember.spec` (FROZEN, E1) | header: "etcd's KV and watch services at its client address"; comment on the bounds: "the members' workload, granting no lease" | "etcd's watch service and, by the lease mode (below), etcd's KV calls or the lease services"; "the members' workload" | r1 §1 NIT (stale at a lease mode); the triple's text is unchanged |
| `cluster3.StartCluster.spec` (FROZEN, E2) | header: "every member at its bridge with its KV and watch registrations …, and etcd's KV at the start store" | "with its watch registration, its KV or lease registrations by the lease mode (below), …, and, in the mode `none`, etcd's KV at the start store" | r1 §1 NIT; the triple's text is unchanged |

The frozen specs keep their pure premises as Lean implications (r1 §1's third NIT): about twenty
older implications, and converting only the three new ones would mix the two styles in one triple.
The rule ("convert one when you change it") applies at their next statement change.

### Exported statements (`cluster3`'s vocabulary, etcdstart's API)

| statement | old | new | cause |
|---|---|---|---|
| `cluster3.servedRegs` (`Defs.lean`) | `servedRegs m c s E ρ cid mid rest`: at `.none` an inline copy of the five KV registrations then `rest`; otherwise `etcdLeaseReadAt c ∗ etcdLeaseServedAt m … ∗ rest` | `servedRegs m c s E ρ cid mid` (no `rest`): `.none => etcdstart.etcdKVAt c E ρ ρ.rd cid mid`, otherwise `etcdLeaseReadAt c ∗ etcdstart.etcdLeaseServedAt m c s E ρ ρ.rd cid mid` | SF3: built from etcdstart's definitions, no continuation parameter |
| `cluster3.memberServed`, `memberAt` (`Defs.lean`) | `… ∗ servedRegs m … iprop(<the rest>)` | `… ∗ servedRegs m … ∗ <the rest>` | SF3 |
| `cluster3.memberServed_none`, `memberAt_none` | `=` by `rfl` | the same equations (statement text unchanged), proved by unfolding `servedRegs` and `etcdKVAt` and reassociating `∗` (a private `sep_assoc_eq`, `BI.sep_assoc.to_eq`) | SF3: `rfl` no longer holds |
| `cluster3.memberAt_mono` (new, `Defs.lean`) | — | `memberAt γn s id ρ E cid mid R b c γ cmp .mono ⊢ isGrpcRpc b "/etcdserverpb.Lease/LeaseGrant" (etcdLeaseGrantSpec (EM := v3rpc.etcdModelOfServer E) E.γ.leases) ∗ isGrpcRpc b "/etcdserverpb.Lease/LeaseLeases" (etcdLeaseLeasesSpec E.γ.leases)` | SF2: the bridge's registrations, `isGrpcRpc_forwards` folded in; leasecatchup's `run` uses it in place of unfolding `memberAt`, `servedRegs`, `etcdLeaseServedAt` and `etcdLeaseGrantAt` (it still unfolds `clusterUp`/`clusterAt`, the bundles every cluster3 client destructures) |
| `cluster3.clusterAt` (`Defs.lean`) | `(match m with \| .none => etcdKV … ∗ ⌜P⌝ \| _ => ⌜P⌝)` | `(match m with \| .none => etcdKV … \| _ => True) ∗ ⌜P⌝` | r1 §2 NIT: the pure conjunct once; `clusterAt_none` still `rfl` |
| `etcdstart.etcdLeaseServedAt_persistent` (new instance, `ServedLease.lean`) | — | `Persistent (etcdLeaseServedAt m addr s E ρ γr cid mid)` | SF4; `servedRegs_persistent` uses it instead of unfolding |
| `etcdstart.alloc3` (etcdstart API), `alloc3Http` (private) | `… (cmp := false) (cret := 0) (lm) (hrun) (hrev)` | `… (lm) (hrun) (hrev) (cmp := false) (cret := 0)` | r1 §3 NIT: the defaults serve their callers again (putget3 and restart drop `false 0`) |

`cluster3.servedRegs_persistent` lost its `[Persistent rest]` argument. `StartMember`'s private
`servedRegs_of_lease` lost `rest`; `StartCluster`'s private `servedRegs_sep`/`servedRegs_join` are
gone (the registrations are a conjunct of their own now).

### New statements (leasecatchup)

| statement | old | new | cause |
|---|---|---|---|
| `etcd_leasecatchup.run.spec` | the pure premises as implications before the triple | the same premises as `⌜…⌝` conjuncts at the end of the precondition, grouped: `⌜BootFacts … ∧ lg ≠ null⌝`, `⌜threadBound GF ≤ 2 ^ 28 ∧ receiptBound GF ≤ 2 ^ 48 ∧ receiptBound GF ≤ N + 1 ∧ N + 7 + bootWB ≤ backend.wbInit⌝`, `⌜ckptEffectsOk ∧ authRecordsFit ∧ apply.backendUnderQuota ∧ grpcRepliesFit ∧ storage.diskOk⌝`, `⌜leasePeersOk ∧ lease.leasesNoExpiry⌝`, `⌜v3rpc.ServerMethodSets ∧ errors.AsTarget …⌝`; the bound premises stay `run.spec`'s (etcd-grove-82) | SF5 (the 2026-11-03 rule) |
| `etcd_leasecatchup.Main.spec` | the same, without `lg` | the same conversion | SF5 |
| `etcd_leasecatchup.grant.spec`, `leases.spec` | `errors.AsTarget … →` | `… ∗ ⌜errors.AsTarget …⌝` in the precondition | SF5 |

The closed theorems (`etcd_leasecatchup_safe`, `_adequate`, `leasecatchup_Main`) are unchanged:
`Adequacy` discharges the precondition's pure conjuncts where it passed the implications' arguments.
The header of `run.spec` and of `Adequacy.lean` now paraphrase `leasesNoExpiry` by its own wording
("no lease of any lessor the program creates, granted or reloaded by `Recover`, expires while the
program runs"; r1 §5 NIT). `etc/tcb-collections/leasecatchup.txt`'s header no longer speaks of
DRAFT `sorry`s (r1 §5 NIT).

### Left, with the reason

- **The duplicated `LeaseLeases` registration** (r1 §2 (a)): at `.mono`, `servedRegs` holds
  `LeaseLeases` at `etcdLeaseLeasesSpecAny` (inside `client.etcdLeaseReadAt`) and at
  `etcdLeaseLeasesSpec E.γ.leases` (inside `etcdLeaseGrantAt`). Dropping one is not trivial: it
  needs a TTL-only registration predicate in the client's API or a change to `etcdLeaseGrantAt`, both
  exported, and `kv_lease_served(_watch)`'s posts would change with them. The surplus is harmless
  (both are persistent, and the `Any` one is derivable from the other).
- **The TTL read in `memberServed`** (r1 §2 (b), and §1's SHOULD-FIX on the two lease axioms the
  `.none` closed results gained): kept for step 2, as `notes/decisions.md`'s R1 entry ("A thread
  token for a cluster member's lease reads", Rejected) decided; the axioms' growth is H1 (A),
  recorded there and in the committed baselines (`e9ec46b4b1`). Putting it before the user at
  Freeze stays open.
- **`alloc3`'s `if decide` gate** (r1 §3 NIT): consistent with `alloc1`; not in this round's list.

### Checks

`lake build` of the eight importer leaves (lease, leasecatchup, leaseexpiry, leasegrant, partition,
putget3, k8s compactor `Results`, restart `Run`) passes. `etc/gen-interface.py etc/api/etcdstart.txt`:
`Alloc3.txt` (the binder order) and `ServedLease.txt` (the new instance) moved, `--check` passes;
`etc/api-check.py` passes. `etc/tcb-report.py --check`: 785 axioms, 3 `sorry`s, as the baseline;
collections leasecatchup (624, 0), linkv3p (635, 0), k8scompactor (684, 0), putget3 (611, 0) match.
`etc/bounds-check.py --check`: 390, baseline 390. No Go changed.

## Test (2026-11-06)

`examples/etcd/leasecatchup/leasecatchup_premises_test.go` (tests only; `leasecatchup.go` is
unchanged, so the translation is too). Each test runs Main's steps (`scenario`: `run`'s six steps,
with observations between them, the same helpers `config`/`grant`/`leases`/`listed`) on a cluster of
its own addresses (`configAt`: 241xx, 242xx, 243xx, 244xx, 245xx), because `run` never stops its
members and TestMainRun holds 240xx. The lessor is read through `EtcdServer`'s unexported field, as
leasesnap's test does. `leasecatchup_test.go` only gains `memberIDsOf` (memberIDs at a config).
**Five tests, 3 of 3 runs pass** (go1.27.3, `go test ./etcd/leasecatchup -count=1 -v`, three
separate processes; `go vet` and `gofmt` clean). **Nothing contradicts a spec or a premise.**

- **`TestLeasePeersOk`** (`leasePeersOk`, `LeaseRead.lean`). At every peer URL, after the start and
  after the catch-up, it sends `POST /leases/internal` (a marshalled `LeaseInternalRequest`, as
  `TimeToLiveHTTP` sends it) and `POST /leases` (the lease handler's other path, the renew). Both
  answer **404**, never 200, so the premise's "200 only with a full `LeaseInternalResponse`" holds
  trivially. etcd's own `leasehttp.TimeToLiveHTTP` reads the reply as `ErrLeaseNotFound`, as
  `leaseTimeToLive.spec`'s docstring says. `GET /raft/probing` answers 200, so the probed address is
  the member's raft handler, not a closed port. 3/3, 6 probes × 3 peers each.
- **`TestLeasesNoExpiry`** (`lease.leasesNoExpiry`, TTL 3600). After the catch-up it checks:
  - every member's lessor and lease bucket hold all 21 leases granted (g1 and the fillers), with
    TTL 3600;
  - on the leader (the only lessor with finite expiries; the others are demoted, `Remaining` =
    forever) the least remaining time is 59m59.7s, so `findExpiredLeases` finds nothing and nothing
    goes on `expiredC`;
  - the process's `etcd_debugging_lease_revoked_total` counter (every `Revoke`, where an expiry
    ends) moved by **+0**, while `lease_granted_total` moved by +43. That is 3 for g1 plus 2 × 20
    for the fillers: members 1 and 2 applied every filler's grant, and member 3 got all of them
    from the snapshot, none by entries.

  `expiredC` itself is not read: it is the server's run loop's channel, and a test that read it
  would take the leases from the server. The test observes it through its consumer instead
  (revoke) and through its producer's condition (`Remaining() > 0`). Runs take 1.3–10.3 s against
  the 3600 s TTL. 3/3.
- **`TestCatchUpClaim`** (`run.spec`'s claim, and that it is not vacuous). Once member 3's listing
  has the last filler, it has g1, and member 3's recovered lessor holds g1 (`Lookup`). To show the
  case is not vacuous (`requireRestore3`, shared by every scenario test), the test also checks:
  - member 3's lessor lacked the last filler while cut off;
  - its backend field `b` was replaced, so `Recover` ran on member 3's lessor, not on another
    member's;
  - raft on member 3 restored a snapshot at index 29, above both member 3's applied index when g1's
    grant returned (7–9) and the filler count, so the grant through member 3 came before the
    restore;
  - one snapshot was sent to member 3, and one lease store was restored.

  3/3. In two runs one filler timed out during a re-election (19 fillers, 8–10 s), and the restore
  was still at 29.
- **`TestCatchUpMutant`** (the check is not blind). The cluster is `cluster3`'s steps, except that
  member 3's lessor field is replaced, before `Start`, by `dropLessor`. Its `Recover` deletes, from
  the snapshot's lease bucket, the leases the lessor held before (as if the snapshot had not
  carried them), then calls the real `Recover`. Every other method delegates to the real lessor.
  The restore happens exactly as in the real runs (`requireRestore3` passes, at index 29). Member 3
  then lists the last filler but **not g1**: `run`'s `panic` condition holds. In each of the 3/3
  runs it dropped exactly g1. This is feasible in-process because `applySnapshot` calls `Recover`
  through `s.lessor`, and setting that field before `Start` changes no etcd code.
- **`TestHoldTokenPerMember`** (cluster3's `go holdToken()`). It calls `cluster3.StartMember` three
  times. After each call the goroutines running `cluster3.holdToken` rise by exactly 1 (+1, +2,
  +3), and those created by `cluster3.StartMember` (holdToken and `gs.Serve`) by exactly 2. After a
  grant served by the cluster, the three `holdToken` goroutines are still there (it never returns).
  The process's raw goroutine count rises by about 50–70 per member (etcd's own), so this test
  counts by stack frame and creator instead. 3/3.

## Review round 2 fixes (2026-11-06)

The NITs N1, N2 and N4 of `notes/spec-review/lease-mono3-r2.md` (round 2, on `00edf6d0f3`), fixed on
branch `lease-mm` as DRAFT under the batching rule: each frozen, exported or new statement that
changed is listed old → new with its cause. No axiom, trusted model or `sorry` was added.

### Exported statements (etcdstart's API, `cluster3`'s vocabulary)

| statement | old | new | cause |
|---|---|---|---|
| `etcdstart.etcdKVAt_eq` (new, `Served.lean`) | — | `etcdKVAt addr E ρ γr cid mid = iprop(<its five registrations>)`, `rfl` | N1: `memberServed_none`/`memberAt_none` rewrite with it instead of unfolding `etcdKVAt` |
| `etcdstart.etcdLeaseServedAt_none` (new, `ServedLease.lean`) | — | `etcdLeaseServedAt .none addr s E ρ γr cid mid = etcdKVAt addr E ρ γr cid mid`, `rfl` | N1 (the reviewer's restatement); no client uses it yet (`servedRegs`'s `.none` arm is `etcdKVAt` itself) |
| `etcdstart.etcdLeaseServedAt_mono` (new, `ServedLease.lean`) | — | `etcdLeaseServedAt .mono addr s E ρ γr cid mid = etcdLeaseGrantAt addr E`, `rfl` | N1: `memberAt_mono` uses it |
| `etcdstart.etcdLeaseGrantAt_elim` (new, `ServedLease.lean`) | — | `etcdLeaseGrantAt addr E ⊢ isGrpcRpc addr "/etcdserverpb.Lease/LeaseGrant" (etcdLeaseGrantSpec (EM := v3rpc.etcdModelOfServer E) E.γ.leases) ∗ isGrpcRpc addr "/etcdserverpb.Lease/LeaseLeases" (etcdLeaseLeasesSpec E.γ.leases)` | N1: `memberAt_mono` uses it |
| `cluster3.memberServed_none`, `memberAt_none`, `memberAt_mono` (`Defs.lean`) | proofs unfold `etcdstart.etcdKVAt` (`_none`), `etcdstart.etcdLeaseServedAt` and `etcdLeaseGrantAt` (`_mono`) | statements unchanged; the proofs rewrite with `etcdKVAt_eq`, `etcdLeaseServedAt_mono` and eliminate with `etcdLeaseGrantAt_elim` | N1 |
| `cluster3.clusterAt` (docstring) | "…; the client's view of etcd's KV at the start store; …" | "…; in the mode `none`, the client's view of etcd's KV at the start store; …" | N2; the definition is unchanged |

The other clients that unfold these definitions (leasegrant's `Main.lean`, leaseexpiry's
`Main.lean`, txnlin's and k8s etcd3's `etcdKVAt`) are pre-existing debt, not changed in this round
(r2 N1 names them); the laws are there for them.

### New statements (leasecatchup)

| statement | old | new | cause |
|---|---|---|---|
| `etcd_leasecatchup.run.spec` | `⌜cluster3.BootFacts id₁ id₂ id₃ ps ctxs boot ∧ lg ≠ null⌝ ∗ …` | `⌜cluster3.BootFacts id₁ id₂ id₃ ps ctxs boot⌝ ∗ ⌜lg ≠ null⌝ ∗ …` (the rest unchanged) | N4: unrelated facts in separate conjuncts, in `StartCluster`'s premise order |

`run`'s proof introduces the two conjuncts with `%Hbf, %Hlg`, and `Main`'s proof passes them
ungrouped. `Main.spec`, `Adequacy` and the closed theorems are unchanged.

### Left, with the reason

- **N3, an elimination law for `clusterUp`** (the three `memberAt`s, the `srvPeerCtl`s and the
  bridges): `run` still unfolds `clusterUp` and `clusterAt` and destructures them positionally. It
  is the shared cluster3 pattern (partition's `startCluster.lean` and `Main.lean` do the same), so
  the law belongs to a change of cluster3's clients together, for later.
- P1 and P2 of round 2 (the user's acknowledgement of the two lease axioms at Freeze; leasecatchup's
  baseline after merging `lean`) are process items, not spec fixes. P2 is closed by the merge below;
  P1 goes to the Freeze.

### Checks

`lake build` of the sixteen importer leaves of the changed files (`etc/importers.py --leaves`, `old.*`
filtered out: the `Results` of cache, compacted, compactwatch, lease, leasecatchup, leaseexpiry,
leasegrant, partition, putget, putget3, txnlin, watch, k8s compactor and k8s etcd3, and restart's
`Run` and `restartCheck`) passes. The new laws omit the section's `[HasExt idIssueExt]` and
`cache_sem` (`omit … in`), which their statements do not need and cluster3's `Defs` does not have:
with them, `simp` could not instantiate `etcdKVAt_eq` there. `etc/gen-interface.py
etc/api/etcdstart.txt`: `Served.txt` (`etcdKVAt_eq`) and `ServedLease.txt` (the three laws) moved,
nothing else; `--check` passes; `etc/api-check.py` passes. `etc/tcb-report.py --check`: 785 axioms,
3 `sorry`s, as the baseline; collections leasecatchup (624, 0), linkv3p (635, 0), k8scompactor
(684, 0), putget3 (611, 0) match. `etc/bounds-check.py --check`: 390, baseline 390. No Go changed.

## Merge with `lean` after R2c (2026-11-06)

`lean` `6b49f77e01` (R2c, the restart stop chain, and 7c-1b) merged into `lease-mm` (`b1d0f637f7`);
only notes conflicted. R2c gives `etcdstart.memberUp` a last conjunct `∃ dd, srvStopRight …`:
`cluster3.StartMember`'s proof drops it (`68e4e8e89d`, `StartMember.lean:164`), as `lean`'s own
cluster3 already did, and its spec header now says so (review r3 N1). leasecatchup's collection
takes the six axioms `lean` added to every server collection (`933df7bb1c`: 7c-1b's
`rpctypes.ErrGRPC{Compacted,FutureRev}_init`, R2c's `lease.lessor.Stop.wp_proof`,
`apply.memberEnc_id_learner`, `apply.memberKey_inj`, `membership.membersOf_decode`): 630 axioms,
no `sorry`. No Go under `examples/` changed on `lean`, so the Go-first and Test results stand.
Review round 3 (`notes/spec-review/lease-mono3-r3.md`): no blocker; dropping the stop right is
right (a served member cannot be stopped: `HardStop` needs the readers `Serve` keeps); the merge
keeps both parents; the collection change is linkv3p's. Its N3 (an elimination law for `memberUp`'s
serving side, so a new conjunct does not break its callers) is etcdstart's, for later.

`etc/gates.sh` at `933df7bb1c`: all pass (build 12363 jobs; tcb 790 axioms, 3 `sorry`s; 52
collections match; goose, gen-init, issues, bounds 389, mode, api, import-all).

## Freeze package (2026-11-06)

**What freezes.** The statements of this stage, as on `lease-mm`:
- hub (etcdstart, accepted by etcd-grove-82): `alloc3Http`, `alloc3`, `memberBoot_of` at a lease
  mode `(lm) (hrun : lease.runCfg lm lm) (hrev : lm ≠ .revocable)`, before the defaulted
  `cmp`/`cret`, `etcdKV` gated on `lm = .none`; the new `kv_lease_served_watch` (R2) and the laws
  `etcdKVAt_eq`, `etcdLeaseServedAt_none`/`_mono`, `etcdLeaseGrantAt_elim`,
  `etcdLeaseServedAt_persistent` (additions only);
- frozen (hub step 7 E1/E2, the change approved with the Scope): `cluster3.StartMember.spec`
  (`(lm ≠ .none → leasePeersOk)`; post `memberServed … lm`) and `cluster3.StartCluster.spec`
  (`lm`; `lease.runCfg lm lm`; the scope premise `lm ≠ .revocable`; `(lm ≠ .none → leasePeersOk)`;
  post `clusterUp … lm`);
- cluster3's vocabulary: `memberServed`, `memberAt`, `clusterAt`, `clusterUp` with `(m := .none)`,
  `servedRegs` from etcdstart's definitions, the laws `*_none` (text at `.none` unchanged) and
  `memberAt_mono`;
- new: the example `examples/etcd/leasecatchup` (`run.spec`, `Main.spec`, `grant`, `leases`,
  `listed`, `config`) and `etcd_leasecatchup_safe` (Scope §3's statement).
The callers' statements (putget3, partition, restart, k8s compactor and their closed theorems)
are unchanged against `lean`.

**Go.** `examples/lib/cluster3`: `StartMember` runs `go holdToken()` (R1, accepted by
etcd-grove-82; `notes/decisions.md`, "A thread token for a cluster member's lease reads").

**Proved.** Everything: no `sorry` of this stage, no new axiom, no trusted model. **Probe: none
needed**, every proof is done (etcd-grove-82, 2026-11-06).

**For the user's acknowledgement (H1, decided by etcd-grove-82 under the user's delegation).**
linkv3p's `etcd_partition_safe` and the k8s compactor's results now also rest on
`EtcdServer.leaseTimeToLive.wp_proof` and `sort.Sort.wp_anyLess`, axioms already in the trust base
(leasegrant; the former audited `ok`, `notes/axiom-review/lease-ttl-row.md`): `StartMember.spec`
is one triple for every mode and its one linked proof takes the lease branch's callees. The
alternative, a per-mode split of the frozen specs, breaks the one-spec-per-function layout.

**Bounds (B1).** leasecatchup's `spec-thread` 2 and `spec-receipt` 4 (the bound premises of
`Main.spec` and `run.spec`, as leasegrant's `Main`); etcdstart's `stock` +1 (the watch run slot in
`kv_lease_served_watch`'s private core).

**Test.** `leasecatchup_premises_test.go`, 3 of 3 runs: `leasePeersOk` (404 at every peer
address), `leasesNoExpiry` (21 leases at TTL 3600 on all members, no revoke), the claim non-vacuous
(member 3's grant before its snapshot restore at index 29, then listed), a mutant lessor that drops
leases on `Recover` makes `Main`'s panic condition true, and `holdToken` adds one goroutine per
member.

**Inherited, unchanged:** the reading of `lease.leasesNoExpiry` over executions after `Main`
returns (leasegrant's; reviews r1, r2). **Open, not blocking:** partition's `TestFailover` hangs to
its timeout on `lean` `6691b46860` as on `lease-mm` (T1): rerun on a quiet machine, a STATUS
finding if `lean` still hangs.

**Not done here, for later:** a `clusterUp` elimination law (r2 N3), a `memberUp` serving-side law
(r3 N3), the duplicate `LeaseLeases` registration and the unused TTL read in `memberServed` (kept
for step 2, the revocable mode).

