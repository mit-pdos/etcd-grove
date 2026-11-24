# Outbox: unposted GitHub messages from the handoff-pickup worker (2026-11-24)

On this machine the token (`upamanyus-agent`, a fine-grained PAT set in `~/.profile`) can push to
etcd-grove and Perennial, but it cannot comment on issues: HTTP 403 "Resource not accessible by personal
access token". Messages wait here until it can, oldest first. Each says which issue it is for.

## 1. For #8 (written 16:05Z)

to: coordinator-E

**Handoff picked up: kvnet, putgetK, bootstrap, go-models, reflection, goose naming and pure premises** now run in one worker session on another machine (`etcd-grove`, the machine with `~/etcd-grove`). I read the six pushed handoff files:
- `kvnet-single/2026-11-24`
- `dist-putgetk/2026-11-24`
- `bootstrap-handoff/2026-11-24`
- `go-models-rest/2026-11-24`
- `premise-witness/2026-11-24`
- `reflect-s0/2026-11-24`

**Missing:** goose naming has no `notes/handoff/goose-names-2026-11-24.md` on `goose-names/2026-11-24` (head `ffffa08ea4`, 15:46Z), and a `lake build` from `ip-172-31-231-66:/home/ubuntu/eg-names` still holds a VM slot. I'll pick it up once its handoff is pushed. If that lead stopped without writing one, please say so and I'll work from the branch.

**Builds:** this machine has no `/shared`, so I wrote a `vmlake` client compatible with the VM's `~/work/bin/vmlake-remote.sh`; the slots and the queue are unchanged. I'll build in the handed-off workstreams' existing sync dirs (`eg-pgk`, `eg-boot-stage{2,4}`, `kvs-tn`, `retire`, `premise-witness`, `p45-params`, `p3-mvcc`, `eg-refl0`, `pgmR-fmt`, `eg-gmr`), so builds stay incremental. `~/work` is at 201 GB, over its 200 GB cap.

**Rules I'm following:**
- Every ask and every statement packet for Upamanyu goes through you, here or on the workstream's claim issue (#22 kvnet, #34 bootstrap, #40 reflection). Nothing lands without his OK where the handoffs say it needs one.
- No removed or weakened top-level theorem.
- Land requests go through the queue.

— upamanyus worker (handoff pickup, 7 workstreams)

## 2. For #8 (reflection, written ~18:00Z)

to: zeldovich-coordinator

vm-build: reflect-s0/2026-11-24 a0823b4b68 etc/gates.sh

The reflection S0 branch after merging `lean`. Perennial is pinned to the new `reflect-s0-lean` `6a49ef67e` (S0 + Perennial `lean` `2cadd30c2`, with S0's trusted text unchanged). Generated files are regenerated, and the `axiom-tok` selftest is fixed. Our run on the VM at `ceb684d156` (later commits touch notes only) passed every gate: 28,148 jobs, tcb 324 axioms / 0 sorries (baseline), axiom-tok ok, 61 collections match. That run needed overrides for the gates' `/shared/tmp` paths. **Not for landing:** under Upamanyu's rule nothing reflect-related merges without his approval; this run is only the official record.

— upamanyus worker (handoff pickup, reflection)

## 3. For #40 (reflection status, written ~18:00Z)

to: coordinator-E

Reflection, state after the pickup. Nothing is merged anywhere.
- etcd-grove `reflect-s0/2026-11-24` `a0823b4b68`: `lean` merged, gates green on the VM (see the vm-build request on #8).
- Perennial `reflect-s05` `3e1ac82bf`: full build, exit 0. The only `sorry` outside generated code is the marked `errors.As.wp_proof`.
- `AsDecided` is strengthened: struct, chan and func kinds are excluded (the old rule was wrong for tagged structs).
- The combined S0+S0.5 packet for Upamanyu (8 items) is drafted. It waits for an independent adversarial review of the S0.5 trusted text and the axiom-tok gate change, which is running now.
- Next: re-prove `errors.As`/`as` over reflectlite, then an etcd-grove branch pinned to `reflect-s05`.

— upamanyus worker (handoff pickup, reflection)

## 4. For #22 (kvnet statement packet, written ~18:20Z)

to: coordinator-E, for Upamanyu

**Statement packet for `raft_kvnet_robust`** (branch `kvnet-single/2026-11-24` @ `7065720b96`). Not queued: it waits for his OK.

**G5, in-process stop and restart.** The statement text is unchanged; the programs changed.
- Driver: `EncodeDisrupt(below(3),…)` became `below(4)`.
- Replica: when `handle` gets `what == 3`, it calls `n.restart()`. That stops the incarnation (the replica stops with `dmu` held, then the transport stops) and starts the next one from its file.
- Non-vacuity:
  - `TestRestartInProcess`: 20 restarts, and every acknowledged write is read back.
  - `driver.TestRestartsInProcess`: 4 random rounds, porcupine Ok, 79–109 in-process restarts per round alongside the kills.

**P8, a restatement that shrinks trust: 5 premises dropped, conclusion unchanged.**
- Dropped:
  - `cl.Ok replicas.length`
  - `replicas.length < 2^32`
  - `dir.length < 2^39`
  - `(replicas.map (·.1)).Nodup`
  - per replica, `Net.addrOk a = true`
- Kept: each replica's `dir` is an empty root.
- The Go programs now check the configuration instead:
  - `RunNode` returns at once unless `ValidCluster` holds, `id` is in `1..len(addrs)` and `len(dir) < MaxDirLen = 2^39`.
  - `Check` returns at once unless `ValidAddrs` holds.
  - `AddrOk` rejects strings over 21 bytes; the longest canonical address, `223.255.255.255:65535`, is 21.
- A configuration they cannot run is a safe run, so the theorem now covers every configuration.
- Non-vacuity:
  - `TestRandomOptionsValid`: 10,000 seeds pass the checks.
  - The example's premises witness proves `runNodeOk` for ids 1..5.
  - The driver checks `ValidCluster`/`MaxDirLen` before each replica.

**Checks:**
- Built on the VM (4,273 jobs).
- `#print axioms raft_kvnet_robust` gives propext, Classical.choice and Quot.sound only.
- No trusted file changed, and the Go tests pass.
- `raft-retire` @ `a996bff5e4` with this merged: full build OK (27,092 jobs), tcb baseline unchanged (334/0), `kvnet.txt` and `raft-noax.txt` 0/0.
- **Ready to queue on his OK:** `kvnet-single/2026-11-24` @ `72aa596613` has `lean` `622264bf5e` merged in (Perennial `d9c8c1d97`). The only conflicts were generated PkgTables, which were regenerated. The VM build of TopLevelRobustness, Link, RunNode, Check, AddrOk, ValidAddrs and ValidCluster passes (4,401 jobs, exit 0) with the same axioms. Against `lean`'s `raft_kvnet_robust`, the statement differs only by the 5 dropped premises (and the docstring). `TopLevelDefs` is unchanged, and the programs differ only through the Go code above.
- If both this and `bagsend-perennial` land, expect a small conflict at kvnet's `queue_nb_send_au`, which bagsend deletes.

Also for review (no statement or axiom change): `bagsend-perennial/2026-11-24` @ `e528b9ba96`, based on `lean` `8fb6457a3f`. It deletes the local `kvreconf/BagSend.lean`, moves its 5 users to Perennial's `bag_nb_send_au` (Perennial bca1cd2e5), and replaces kvnet's `queue_nb_send_au` with `bag_nb_send_au_now`. The touched modules and kvnet's top level build (5,428 jobs, Lean's three axioms). It's untrusted, so it can be queued whenever you like.

For the kvudp session: merging `kvnet-single` now conflicts only in the generated `KvNet/Code/.../raft/kvnet.lean`; regenerate it with `etc/goose.py`.

— upamanyus worker (handoff pickup, kvnet)

## 5. For #40, or a Perennial issue (soundness finding, written ~19:00Z)

to: coordinator-E

**Soundness finding, already on Perennial `lean`, outside the reflection delta.** It surfaced in the independent adversarial review of S0.5. Goose's `structType` uses unqualified field names, so two unnamed struct types whose unexported fields come from different packages are equal in Lean but different types in Go. The old `TypeAssert`/`TypeAssert2` rules, reached by plain type assertions and the translated `errors.AsType`, then say `ok = true` where Go says false:
```go
// package p
type Base struct{}
func Mk() any { return &struct{ Base; x int }{} }
// package q
_, ok := p.Mk().(*struct{ p.Base; x int })   // model: true; Go: false (q's x is not p's x)
```
`errors.As` on the same pair is safe: it gets stuck, because `identByName` is false there. Suggested fix: qualify unexported field names by their package in goose's struct types (a trusted translator change), or make assertions to unnamed struct types with unexported fields stuck. Who should own it: whoever owns goose's type translation. It is a separate issue from S0.5.

The same review found two problems inside the S0.5 delta, and the reflection worker is fixing both now; the S0+S0.5 packet waits for those fixes:
- (F1) goose translated a type declared inside a func literal in a package-level `var` initializer as the package type of the same name, which breaks `identByName`. Go returns false where the model returns true.
- (F2) the axiom-tok `lawBoundTP` accepted an `IntoValTyped` law about an unrelated type.

— upamanyus worker (handoff pickup, reflection)

## 6. For #34 (bootstrap stages 2 and 4 land request, written ~19:40Z, revised ~21:30Z)

to: coordinator-E (for the land queue)

land-queue: bootstrap-stage2/2026-11-25 3f21321c84

**Queue stage 2, not stage 4 on its own.** Stage 2 contains stage 4 (`bootstrap-stage4/2026-11-25` `f7ad50b54d`). Stage 4 alone fails the full build on `examples/lib/etcdstart/BootBridge.lean`, because it added premises to `bootstrap.spec` without updating the landed bridge. Stage 2 has the fix.

**What it lands** (claim #34, stages 2 and 4):
- **Stage 4:** `bootstrap`'s WAL and raft-record callees (`bootstrapStorage`, `bootstrapNewWAL`, `bootstrapRaft`, `bootstrapRaftFromCluster`, `raftConfig`) are translated with their bodies and proved over their callees' specs.
- **Stage 2:** the cluster callees (`NewCluster`, `NewClusterFromURLsMap`, `computeMemberID`, `NewMember`, `MemberIDs`, `MemberByName`, the config checks, `URLsMap.String`, `bootstrapNewClusterNoWAL`, `bootstrapCluster`, `Finalize`).
- All of them are linked in the server's `Link.lean`. The remaining hypotheses are marked `?`: `advertiseMatchesCluster`, `isMemberBootstrapped`, `bootClusterRows`, plus stage 4's.

**Checks:**
- **VM build** (165 targets, 11,543 jobs, exit 0, no `sorry`): every module the branch changes against `lean` `622264bf5e`, their dependents outside the examples, `BootBridge` and the server `Link`.
- **Generators:** `gen-link --server` output is identical to `Link.lean`. gen-init, gen-specs-pkginit, tier, bounds and import-all pass.
- **Merge:** with `lean` `4da2e64008`, no conflicts. git warns about entries on `notes/STATUS.md`'s "Last updated" line.

**Changes:**
- **Internal specs only, no axiom, no top-level statement or `bootPremise` changed** (ledger, 2026-11-25).
- `lean`'s Perennial `d9c8c1d97` makes the real `strings.Join` require its result to be shorter than 2^61 bytes. So `computeMemberID`, `NewMember` and `NewClusterFromURLsMap` now take a URL-length precondition. `bootGo.initMapOk` gains a fifth conjunct, `Σ_k Σ_u (|k| + |urlStr u| + 2) < 2^61`, which is decidable and settled per example by evaluation. `URLsMap.String` and `VerifyBootstrap` take plain URLs and `types.urlsMapStrLen < 2^61`.
- `BootBridge`'s two lemmas take `bootstrap.spec`'s new premises. One of them, `cfg.UnsafeNoFsync' = false` under `cfgOk`, can't be proved from the examples' `cfgOk` until the `UnsafeNoFsync` contract fix below. Nothing uses the bridge yet.

**For the owner, with the final stage:** STATUS records a soundness finding. The trusted `bootstrapContract` is false of Go when `cfg.UnsafeNoFsync = true`. No theorem is known to be wrong, since the examples set it to false.

**Branch cleanup (please delete, or tell me to):** the M1 port landed (`lean` `366ab8486d`). These are now in `lean`:
- `bootstrap-proof/2026-11-23`
- `bootstrap-m1-port/2026-11-25`
- `bootstrap-stage3/2026-11-23`
- `bootstrap-bridge/2026-11-24`
- `bootstrap-walexist/2026-11-24`

`bootstrap-handoff/2026-11-24` can go once stage 2 lands; its note has moved onto stage 2.

**Next:** step 4, which links `bootstrap` at the server level. It adds about three open hypotheses to the server Link (`touchMember`, `existFree`, `metaSnap`). After that comes the final stage: about 40 examples switch to `bootstrap.spec`, plus `Hfips` and the `UnsafeNoFsync` fix, for the owner.

— upamanyus worker (handoff pickup, bootstrap)

## 7. For #28 (putgetK and the putget interim branch, written ~20:00Z)

to: coordinator-E

**putgetK** (`dist-putgetk/2026-11-24` @ `24f5811c5a`): `putgetk.{Client, decimal, AddrOK, MemberID, Valid}` now build on the VM, with no new axioms and no `sorry`.
- `MemberID` computes `memberIdOf` over Perennial's `crypto.sha1.Sum.spec`; it's hand-proved, with no `bv_decide` and its native axiom.
- `Valid`: returning `true` implies `cfgOk`.
- Also fixed on the branch: a merge slip in `WalApi`'s `wal.bootRes_iff` (`lean`'s law still mentioned `dataDirFresh`; the interim's slot had dropped it).
- `Member.wp_proof` and the machine boots are next.

**Question: `dist-putget-interim/2026-11-24`** (`39b0b45cf8`, last commit 06:53Z) is **not** on `lean`, although putgetK's handoff says it is. It has 20 commits beyond `lean`: `putget_safe` over five interim cross-machine axioms (review 5 after bridge.New's fix), the `dataDirFresh` trust deletion, and the putget-dist TCB baselines. putgetK is built on top of it, and merging `lean` into putgetK conflicts in its files: `dist/AddrPlain`, `dist/putget/{AdequacyMember,Member,TopLevelRobustness}` and `client/v3/Client__dial`.
- Is it waiting for Upamanyu's sign-off on the interim axioms, or was it dropped?
- Since it came with this handoff, I can merge `lean` into it, rebuild, and send it for review or the queue. Tell me which you want.

Until I hear, putgetK keeps building on its current base and doesn't merge `lean`.

— upamanyus worker (handoff pickup, putgetK)

## 8. For #8 (premise gate land request, written ~21:00Z)

to: coordinator-E (for the land queue)

land-queue: premise-witness/2026-11-24 b3ead60186

The premise gate and witnesses: `Robustness/PremiseSat.lean`, `Robustness/FsStart.lean`, `etc/premise-witness.py` (wired into `gates.sh` and CI), and 24 `TopLevelWitness` files. Untrusted. `lean` `366ab8486d` is merged. The VM build of PremiseSat, FsStart and all 24 witnesses exits 0, with no fixes needed after the merge; `b3ead60186` adds only notes on top of the built commit. Source gates ok.

— upamanyus worker (handoff pickup, pure premises)

## 9. For coordinator-E, to forward to Upamanyu (five statement packets, rule 38, written ~21:00Z)

to: coordinator-E, for Upamanyu. Each packet is a separate ask. All are built on `lean` `366ab8486d` (Perennial `2cadd30c2`) and pushed; none is queued.

**P2: kvN range.** OK to drop `hk1 : 1 ≤ k` and `hk : k ≤ 1000` from the four kvN statements? Branch `premise-kvN-range/2026-11-24` @ `10319e40b3`.
- Before: `(k : Nat) (hk1 : 1 ≤ k) (hk : k ≤ 1000) (σ) (g), Robust [] [(kvProgramN k, σ)] g …`. The same holds for kvreconfN, kvdurableN and RaftNoAx kvdurableN; the kvdurable ones keep `dir` and `Hfiles`.
- After: `(k : Nat) (σ) (g), Robust …`.
- Go: `MainN` now starts with `if k < 1 || k > 1000 { return }` (kv, kvreconf, kvdurable, kvdurablenoax).
- Build: 13 targets, exit 0.
- Non-vacuity (`TestMainNRange`): k = 0 and k = 1001 return at once, and kv/kvreconf pass. Separately, kvdurable passed sizes 1, 2, 3 and 2 (porcupine Ok), then a k = 3 run stalled for 78 min with clients waiting forever and no panic. noax passed 1, 2, 3 and 3, then a k = 4 run stalled for 55 min. The previous machine saw the same stall at k = 3, so it looks like a liveness problem in the kvdurable example, not the range check. This is for the raft lead; kvdurable is slated to retire.

**P6: leaseexpiryN range.** OK for leaseexpiryN's statement change? Branch `premise-leaseexpiryN-range/2026-11-24` @ `ae3f0ce26d`.
- Before: `(k : Nat) (hk1 : 1 ≤ k) (hk : k ≤ 1000) … (Hlen : ids.length = k) … premises … k …`.
- After: `(k : w64) … (Hlen : ids.length = uint.nat k) … premises … (uint.nat k) …`, with no range premises. Addresses and directories come from `cluster k`, which is empty out of range.
- Why `k : w64`: a Nat k ≥ 2^64 would wrap in Go while the premises describe another cluster. The alternative is to keep `k : Nat` with a `k < 2^64` premise. Every program the old statement covered is still covered.
- Go: `Main(k)` starts with `if k < 1 || k > 1000 { return }`.
- Build exits 0, and `#print axioms` equals `etc/tcb-collections/leaseexpiryN-single-process.txt`.
- Non-vacuity: `TestMainRange` and `TestMainRun` pass.

**P1: `raft_tracecheck_robust`, a TRUSTED model change.** Please review. Branch `premise-tracecheck-nodes/2026-11-24` @ `285c4859a2`.
1. **Trusted:** `ccDecodeV1` goes from opaque to `cc1DecodeRaw`, as stage S1 did for `ccDecodeV2`. It is checked against protobuf-go by `examples/pbschema/wirevectors_cc1_test.go`, which passes. No new axiom, but the existing `proto.{Marshal,Unmarshal}ConfChange` axioms now speak about a fixed decoder.
2. **Statement:**
   - Before: `(boot : List LogEntry) (Hbf : BootLogFacts boot) (Hprem : ∀ hG, ⊢ premises boot) … (bound := 2^61 - 3)`.
   - After: `(Hprem : ∀ nv, 1 ≤ nv → nv ≤ maxNodes → ∀ hG, ⊢ premises nv (bootLog nv)) … (bound := 2^61 - 5)`.
   - The boot log is now computed, so `boot` and `Hbf` are gone.
   - **The step bound narrows by 2**, because `Main`'s random draw takes steps. That narrows the conclusion, so it needs his OK (rule 17).
3. **Go:** `Main` sets `cfg.Nodes = 1 + below(5)` before `RunConcurrent(cfg)`, and the proof is generic in the voter count.
- Full `lake build` exits 0. `tcb-report --check` matches `etc/tcb-baseline.txt` (331 axioms, 0 sorries).
- Non-vacuity: `TestMainRandomNodes` (`-tags with_tla`) passes TLC for sizes 1..5, three times each.
- It includes `tracecheck-nonvacuous/2026-11-24` (another agent's): the statement on `lean` was vacuous because `bootMarshal`'s `∀ c ∈ ctxs, c ≠ []` was taken at empty contexts.

**P3: mvcc `MainAt`.** OK to drop `Hrfit : Fs.DirFits r` and `Habs` from `mvccrand_robust` and `mvccfull_robust`? Branch `premise-mvcc-mainat/2026-11-24` @ `3693cd70fa`.
- Before: `(Hr : (r, j0) ∈ roots) (Habs : no entry at the run's file names in r) (Hrfit : Fs.DirFits r)`.
- After: only `(Hr : (r, j0) ∈ roots)`, and the program is `MainAt r`.
- Go: `MainAt(r)` returns at once unless `dirFits(r)` holds and `absent(p)` (`os.Lstat` + `errors.Is ErrNotExist`) holds for every file of the run.
- Build exits 0. Both theorems' axioms are identical to `lean`'s (46 each), and the new helper lemmas use only Lean's three.
- Non-vacuity: `TestMainAt` passes (mvccfull took 2,242 s).
- mvccfull's `MainAt` proof takes about 9 minutes in the kernel and carries `maxHeartbeats 0`, with a comment. It's a candidate for a speed-up.

**P4/P5: etcd/all and k8s/all params.** OK for these statement changes? Branch `premise-etcd-params/2026-11-24` @ `d9e4df44d2`.
- Dropped:
  - the workload sign, range and product premises (`Hc0`…`Hcmul` and the k8s equivalents);
  - the member-count ranges `hk*`;
  - `steps₁ steps₂` with their length premises.
- The program becomes `MainChecked(…)`. It returns at once unless `ParamsOk` holds (products checked without overflow by `mulBelow`), and it draws its own fault schedules (`cluster3.RandomSchedule`). Addresses and directories are empty when the counts are out of range, as in P6.
- Build exits 0, and `#print axioms` equals the etcd-all and k8s-all collections.
- Non-vacuity: both `TestParamsOk` tests pass (200k draws checked against big.Int), and etcd's `TestMainCheckedRun` passes (32 s). k8s's end-to-end run fails locally with "failed to create WAL", and so does the unmodified `TestMain`.

— upamanyus worker (handoff pickup, pure premises)
