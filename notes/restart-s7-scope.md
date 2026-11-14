# Restart S7: Scope for the first closed restart theorem (2026-11-14, for etcd-grove-81; notes only, nothing built)

DRAFT for review. Written at `restart-s56` after S6 landed (`lean` `a10cbbfb26`, `NewServer.specR` proved and
linked as `wp_NewServerR`). Inputs: `notes/restart-scope.md` (S7-S9, §4 decisions D1-D7, the crash ladder),
`/shared/tmp/restart-s56/plan.md`, `notes/restart-vs-crash.md`, `notes/wal-crash-handoff/restart-wal-interface.md`.
Abbreviations: `E/` = `Proof/go_etcd_io/etcd/server/v3/etcdserver/`, `SE/` = `Spec/go_etcd_io/etcd/server/v3/etcdserver/`,
`X/` = `Proof/github_com/mit_pdos/etcd_grove/examples/`, `SX/` = `Spec/github_com/mit_pdos/etcd_grove/examples/`.
Estimates are marked (est.).

**A note on the name.** In `notes/restart-scope.md`, S7 is R2s-A: following a merged snapshot, so that the
restart-only rows (`srvWinPend`, row 4 `rnSnapTermAbove`) can be deleted. The brief asks for something else
under the name S7: the first *closed* restart theorem, with one member, a graceful stop and a restart, and no
acknowledged write lost. This Scope recommends getting that theorem **without R2s-A**. With one member, no
snapshot is ever sent, so the two rows hold trivially (§3, gap G2). R2s-A stays the prerequisite of
`restart3_safe` (old S9), where a restarted follower is caught up by a leader's snapshot. In what follows,
"S7" means the closed one-member theorem, and R2s-A keeps its own name.

---

## 1. The theorem in plain words

**Claim.** One etcd member runs in a process. Its client's writes are acknowledged. The member is then stopped
gracefully, and started again in the same process on the same data directory. A read through the
restarted member returns every acknowledged write. The program never panics.

**Recommended first form (R1):**
- **One member** (`restart1`), not three.
  - With three members, a restarted follower is caught up by the leader's `MsgSnap`. That is exactly R2s-A
    (6-9 weeks). It is also exactly where `srvWinPend` is false.
  - With one member there are no peers. Nothing sends a `MsgSnap`, and nothing elects another leader.
  - The restart still runs every server-side restart path the proofs cover: the WAL replayed past a
    snapshot record (`σ.b > 0`), the backend opened at its consistent index, replay skipping the entries at
    or below it, `RestartNode` from the WAL's hard state, and the restored lessor, auth and alarm buckets.
  - This is the crash ladder's rung 4 shape (`notes/restart-scope.md`, "Intermediate milestones"), but with a
    graceful stop in place of power loss.
- **The workload: in-process writes, then one read after the restart.**
  - Before the stop, `N` sequential `Put`s of distinct keys `k_i := v_i`, through the server's own API
    (`EtcdServer.Put`, the call v3rpc's `kvServer.Put` makes). `N` is large enough with `SnapCount = 1` that
    the WAL holds a snapshot record. If any `Put` fails, `Main` returns without checking (as `putget` and
    `restart3` do), so a check happens only when all `N` writes were acknowledged.
  - After the restart, one linearizable `Range` over the keys' prefix. It is either in-process
    (`EtcdServer.Range`) or through a client after `Serve` (as `restart3`'s restarted member does). The
    program panics unless the `Range` returns exactly the `N` pairs.
  - This checks "no acknowledged write lost" for every write, not only the last one. It also checks that no
    write was applied twice or invented, because the values are distinct.
- **How the stop is triggered: `HardStop` from the driver, after the writes, with no gRPC ever served by
  the first incarnation.**
  - Today's `HardStop.spec` stops only a member that never served gRPC (`SE/EtcdServer__HardStop.lean:8-15`).
    Its serving stocks go to `Serve`, and no `grpc.Server.Stop` spec returns them.
  - In-process writes keep the first incarnation off gRPC. Each `Put` borrows a reader (`E.RD`,
    `srvLeadTimeReader`, `idCred`) and gives it back (`SE/EtcdServer__Put.lean:44-53`). So once the `Put`s
    have returned, the stop can collect the raw stock that `srvStopReaders` (`E/InvRestart.lean:282`) needs.
    This is probe P1.
  - The driver waits for `AppliedIndex() ≥ NBoot` before the stop (`srvBootApplied`, as `restart3`'s `stop`
    does).
  - There is no peer listener. A one-member cluster does not need incoming peer connections. So
    `restart3`'s HS3 (`http.registerClosable_spec`, listener close) is not needed.

**Statement (draft, `X/etcd/restart1/Results.lean`),** shaped as `etcd_putget_safe`
(`X/etcd/putget/Results.lean:56-86`):
```lean
theorem etcd_restart1_safe [lctx] [sem] [package_sem : …restart1.Assumptions] [cache_sem]
    [DialWithBalancerBody] [log.NewModel]
    (Hctx : ∀ hG, ContextReadErrs …) (Hcec : ∀ hG, ContextErrsClient …)
    (id : w64) (ctxs : List (List w8)) (boot : List LogEntry) (Hbf : etcd_restart1.BootFacts id ctxs boot)
    (Haf : authRecordsFit) (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit) (Hdbo : storage.diskOk)
    (HNs : prometheus.namesUnclaimed restart1Program restart1Names)
    (HAs : addrsUnclaimed restart1Program restart1Addrs)
    (HDs : dataDirsAbsent restart1Program [go!"restart1.etcd"])
    (HEnv : verifyEnvOff restart1Program) (n : Nat)
    -- bootstrapContract (first start) and bootstrapRestartContract (the restart), D4 of restart-scope
    (Hprem : ∀ hG, ⊢ etcd_restart1.premises n id ctxs boot)
    (σ g) (Hlctx) (Hinit : IsInit σ) (Hthreads : σ.threads = 1) (κs t2 σ2)
    (Hsteps : RealNsteps n ([restart1Program], (σ, g)) κs (t2, σ2)) (Hn : n + 2 ≤ 2 ^ 28) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧ (∀ e2 ∈ t2, RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false)
```
The only hypothesis that `etcd_putget_safe` does not have is `bootPremiseR` inside `Hprem` (§5).
`srvRestartRows` must **not** appear (strong-theorems goal). Its docstring says "graceful stop in one
process; not a kill or a power loss" (restart-scope D1 (a)).

**Second form (later, R1'):** the same program with the writes through a gRPC client, using txnlin's
porcupine workload. It needs a `grpc.Server.GracefulStop`/`Stop` spec that returns the serving stocks
(restart-scope D5). That spec is trusted text, and it was ordered after stage B, which has landed
(`51e51adb99`). Est. +1.5-2.5 wk. Not in S7.

## 2. What exists to reuse

| Piece | Where | State | Use in S7 |
|---|---|---|---|
| `NewServer.specR` | `SE/NewServerR.lean` (premise `Hrows` at `:105`); proof `E/NewServerR.lean` (`wp_proofR`) | proved, linked (`wp_NewServerR`), used by no closed theorem | the restart construction |
| `HardStop.spec` → `srvDiskImage` | `SE/EtcdServer__HardStop.lean:55-60`; `E/InvRestart.lean:160,191` (`srvDiskImageAt`, `srvDiskImage`) | proved, linked | the stop |
| `bootstrapRestartContract` / `bootOkR` | `E/InvRestart.lean:659`, `:406` (WAL slot `"Hwal" ∷ wal.restartOk` at `:429`) | premise (trusted text about names-only `bootstrap`), reviewed at CP2/CP3 | the restart's boot |
| `wal.restartOk` + laws | `E/WalApi.lean:448-468` | defined sealed body over the graceful model, both laws proved | the WAL (§4) |
| `etcdstart.bootPremiseR` | `X/lib/etcdstart/Restart.lean:36` | DRAFT def, the contract per member | `Hprem` |
| `etcdstart.memberBuiltR` | `X/lib/etcdstart/Restart.lean:51` | DRAFT def (`memberBuilt` at any start index) | `BuildServer`'s restart post |
| `BuildServer.specRestart` | `SX/lib/etcdstart/BuildServer.lean:87-127` | statement only, **no proof** | the restart's `BuildServer` |
| `Start_builtR_spec` | `X/lib/etcdstart/StartStop.lean:39` | DRAFT hypothesis | to become `wp_Start_built` at `ai₀ ≠ 0` |
| `memberRestartRes` and laws | `X/lib/etcdstart/StartRes.lean:144-193` | proved | the restart bundle |
| `restart3` Go program + test | `examples/etcd/restart/restart3.go`, `restart3_test.go` | done, 15/15 | template for `restart1`'s Go and its counting test |
| `restart3` proofs | `X/etcd/restart/{Run,restartCheck,startMember,stop,put,Main}.lean` | proved over hypotheses (`startMember.specRestart`, `Start_builtR_spec`, HS3) | templates: `stop.wp_proof` (`:32`), `restartCheck.wp_proof` (`:57`, the read after the restart against the stopped incarnation's KV invariant, `putGetInv_st`), `startMember.wp_proofRestart` (`:138`) |
| `putget` adequacy | `X/etcd/putget/{Adequacy,MainLinked,Results}.lean`, `etc/tcb-collections/putget.txt` | closed (`etcd_putget_safe`) | template for `restart1`'s link, adequacy and collection |
| `EtcdServer.Put` / `.Range` | `SE/EtcdServer__Put.lean:44`, `SE/EtcdServer__Range.lean`; `E/Link.lean:1882` | proved, linked | in-process writes and the read |
| `kvInv_restartNames`, `restartNames` | `E/InvRestart.lean:721-734` | proved | the KV invariant carried across the restart |

## 3. What is missing

| # | Gap | file:line | Kind | Est. |
|---|---|---|---|---|
| G1 | `Start.spec` takes `ai₀ = W64 0`. A restarted member's apply thread starts at its image's index `i`. `run.spec` already takes the restart point (S4, `srvRunRestartR`), so the gap is `Start`/`start` only. Then `Start_builtR_spec` collapses into `wp_Start_built` | `SE/EtcdServer__Start.lean:47`; `X/lib/etcdstart/StartStop.lean:39` | a spec change: a premise dropped, so the spec is stronger. The callers are unaffected. Linked spec, so Freeze review | 1-1.5 wk |
| G2 | `NewServer.specR`'s premise `srvRestartRows` (row 4 and `srvWinPend`) must be discharged for one member. Both rows are about `MsgSnap`s this incarnation sends: row 4 says each is above `t0`, and `srvWinPend` that its term is not the replay's. With the configuration `{id}`, raft sends no message at all (no peers). So both hold if the node API says "a sent message's `To` is a voter other than the sender". Probe P2: is that derivable from `isRaftMsg`/`isMessageC` (`Proof/go_etcd_io/raft/v3/ApiVocab.lean:424`), or is a raft API law needed (a proved law, an interface diff in `interface/`)? Then `srvRestartRows_single : γ.cfg = {id} → ⊢ srvRestartRows γ id A σ`, with the configuration from the image (`srv_confAt_eq_simple`) | `E/InvRestart.lean:709`; `SE/NewServerR.lean:105` | internal (a lemma), plus maybe a raft API law | 1-2 wk |
| G3 | `BuildServer.specRestart` has no proof: Go's `BuildServer` (config, then `NewServer`) over `NewServer.specR`, its post as `memberBuiltR`. `specR` wants the image at explicit witnesses (`srvDiskImageAt`), `restartNames ρo ρ` and the fresh per-incarnation names (`Hkvs`, `Hcok`, `Hrev`, `Hrd`, `Hids`, `Hwtok`). `memberRestartRes` must carry them, or the proof must allocate them | `SX/lib/etcdstart/BuildServer.lean:87`; `X/lib/etcdstart/Restart.lean:51`; `X/lib/etcdstart/BuildServer.lean` (first-start proof, template) | proof; `memberBuiltR`'s DRAFT body fixed (form) | 1-1.5 wk |
| G4 | The program: `examples/etcd/restart1` (Go: start, `N` in-process `Put`s, wait for `AppliedIndex() ≥ NBoot`, `HardStop`, `BuildServer` + `Start` again, `Range`, check), its test (counting logger: a WAL snapshot replayed (`σ.b > 0`), the backend's consistent index above `NBoot`, every check passing), its Goose translation (`etc/goose.py` configuration) | new | Go + translation | 3-4 d |
| G5 | The example's proofs: `Main`/`Run`/`restartCheck`-like, from `restart3`'s templates. In-process `Put`/`Range` needs a request context and the server's request view (`isServerReqM`), and the borrowed readers back before the stop (P1). Then `Link.lean` (`etc/gen-link.py`), `MainLinked`, `Adequacy`, `Results.lean`, `etc/tcb-collections/restart1.txt` | new, `X/etcd/restart1/` | proof + linking | 2-2.5 wk |
| G6 | `bootOkR`'s `#Hmembers`: a WP about the translated `Members()`, stronger than its proved spec (restart-scope S11, D7). The same flaw is in `bootOk` and every closed theorem today, so it is inherited, not new. For a single member, `Members()` returns one member | `E/InvRestart.lean:498`; `E/InvBoot.lean:335` | trusted-text repair (contract) | 1 wk (S11), **optional for S7** (D-S7-4) |
| G7 | The thread budget across the two incarnations: the first incarnation's leaked goroutines keep their `threadTok`s. With one restart this is a constant, so `Hn : n + 2 ≤ 2^28` should still do. Check in P4 | `notes/bounds-plan.md` | check | — |

Not missing for S7: R2s-A, F4 (many restarts), `GracefulStop`, HS3, the cluster driver, the crash model.

## 4. The WAL: the interface agreed with the collaborator

**What the restart takes.** S6 put the WAL behind one slot, `wal.restartOk cfg id cid w σ`
(`E/WalApi.lean:448`). Its body is sealed and defined over the graceful model:
`walOpened w dir id cid σ true ∗ walPurgeRight dir ∗ ⌜walReadFacts σ⌝`, where `walReadFacts` is I1-I4.
Two laws are proved: `wal.restartOk_facts` and `wal.restartOk_start`. `bootOkR` hands the slot out
(`E/InvRestart.lean:429`). `NewServer.wp_proofR` uses only the laws. Interface note §5 says C6 owns the body
from now on.

**Can S7 be proved now over the interface? Yes.**
- S7 adds no WAL fact. It reaches the WAL only through `NewServer.specR`, which reaches it only through
  `bootOkR`'s slot and the image (`wal.stopImage`, `srvFiles`).
- The slot is the assumption to be discharged later. Today it is discharged by a definition (no axiom,
  no opaque), over the axiomatized `walFiles` token (`Proof/go_etcd_io/etcd/server/v3/storage/WalRecs.lean:229`).
- When C6 rebases the body on `ReadAll` + `walCrashKeeps` + the server's history invariant (a)-(c), and
  re-proves the two laws, S7's proofs are unchanged. What changes is the restart contract's claim, which
  C6's own Freeze reviews.

**What S7 then assumes about the WAL** (all existing, none new):
1. **The restart contract's claim** (`bootPremiseR` → `bootOkR`, a premise of the theorem): Go's
   `bootstrap`, on the stopped directory, opens and reads the WAL into a handle with exactly the stopped
   records `σ` (sized), the member's metadata, and the purge right. Attack 4 of
   `notes/axiom-review/wal-tokens.md`, re-attacked at CP2 of S6.
2. **The graceful file model**: the `walFiles` axiom token, "the files a graceful stop in one process leaves"
   (`WalRecs.lean:209-251`). That is true here, because the restart is in the same process after `HardStop`
   returned. There is no power loss in the theorem, so `notes/restart-vs-crash.md`'s "restart = machine crash
   after sync" assumption is **not needed**: the page cache is the disk the next incarnation reads, and no
   later generation reads the disk.
3. **The size flag** (F8): `walSaveOk` (no `Save` failed), inside `storage.diskOk`. That is graceful-only as
   argued (`notes/restart-vs-crash.md:360-368`), and true here: a failed `Save` ends in `lg.Fatal`.
4. **The graceful-only conjunct** `i ≤ σ.commit` (F6), confined to `rnRestartOk`'s marked conjunct (interface
   §4). A graceful stop satisfies it.

So S7's WAL premise is the interface, not the collaborator's spec. The collaborator's spec later replaces
assumption 2 (and part of 1) without touching S7. The same theorem under power loss is rung 4 of the
ladder, and it waits for C6 and rungs 1-3.

## 5. World assumptions

**Existing (in `etcd_putget_safe` today, inherited):**
- `storage.diskOk` (no failed `Save`, `walCreateOk`), `storage.dbOpensOk`, `apply.backendUnderQuota`,
  `authRecordsFit`, `grpcRepliesFit`;
- `dataDirsAbsent` (the data directory fresh at program start), `addrsUnclaimed`, `namesUnclaimed`,
  `verifyEnvOff`, `ContextReadErrs`/`ContextErrsClient`;
- `bootstrapContract` (a premise about names-only `bootstrap`, D13b), with its `#Hmembers` flaw (G6);
- the request timeout's clock, and the thread bound `n + 2 ≤ 2^28`.

**Existing, newly load-bearing:**
- **Request-id freshness across the two incarnations.** The trusted `Generator.Next`
  (`TrustedCode/go_etcd_io/etcd/pkg/v3/idutil.lean:63`) `assume`s that no other generator issued the id.
  That is false if the clock goes back, if the restart is within the same millisecond, or if more than 256
  ids per ms were issued since the previous start (`nonissues/etcd-request-id-restart-reuse.md`).
  **Already accepted by the user (2026-11-11) as a listed world assumption.** The theorem's docstring must
  list it.

**New, for the user:**
- **N1. The restart contract as a premise of a closed theorem** (`bootstrapRestartContract` inside `Hprem`,
  restart-scope D4). It is new trust about names-only code: Go's `bootstrap` restart path (`wal.Open`,
  `ReadAll`, the snapshot load, the backend open, `cl.Recover`) yields `bootOkR`. It is satisfiable and
  testable. It was attacked with the `axiom` skill at S6's CP2 (HS1, the WAL slot, H10). `restart1`'s test
  runs the path. *Recommended: accept as a premise* (no change of practice from `bootstrapContract`), listed
  in the docstring and STATUS.
- **N2. "Restart" means a graceful stop in the same process.** This is not an assumption the theorem takes
  as a hypothesis, but a limit on what it says. The docstring must say that it does not cover a kill,
  a SIGKILL, or a power loss (D1 (a)). The user should confirm the wording, since a reader could take
  "restart" for "crash". *Recommended: accept with that docstring.*

No other new world assumption is expected. The probes (P1-P4) report any they find, as a hard stop.

## 6. Stages, hard stops, estimates, decisions

**Stages** (each in its own worktree and branch, landed through `etc/land.sh` on 81's go):

| Stage | Work | Est. | Ends with |
|---|---|---|---|
| S7.0 | `restart1` Go program + counting test + Goose translation (G4); the test run under the 32G cap | 3-4 d | CP-a: the test passes and counts a `σ.b > 0` replay |
| S7.1 | Probe, no statement changed (`Scratch/S7Probe.lean`): P1 in-process `Put`/`Range` at a request context, readers back before `HardStop`; P2 the single-voter "no message sent" fact (G2); P3 `Start.spec` at `ai₀ = i` from `srvBuiltR` (G1); P4 `BuildServer.specRestart`'s premises from `HardStop`'s image (G3) and the thread budget (G7) | 1 wk | CP-b: probe report (gaps with proposals) |
| S7.2 | G1: `Start.spec` without `ai₀ = 0`; `wp_Start_built` at a restart; `Start_builtR_spec` deleted | 1-1.5 wk | Freeze (spec change) |
| S7.3 | G2: `srvRestartRows_single` (and the raft API law if P2 needs it) | 1-2 wk | CP (internal, or raft interface diff) |
| S7.4 | G3: `BuildServer.specRestart` proved; `memberBuiltR`'s body | 1-1.5 wk | CP |
| S7.5 | G5: `restart1`'s proofs, link, adequacy, `Results.lean`, collection; `etcd_restart1_safe`'s statement to Freeze **before** its proof is linked | 2-2.5 wk | Freeze of the theorem; final CP: full build, tcb `--check`, collection, gates |

Total (est.): **7-10 weeks** of work, about 6-8 weeks of calendar with S7.2-S7.4 partly in parallel. S7.0 and
S7.1 can start now. That is less than restart-scope's S7 (R2s-A, 6-9 wk) plus S8 plus S9 (≈ 9-14 wk) together,
because one member removes R2s-A, F4, HS3 and the three-member link.

**Hard stops** (report and wait):
- CP-b, the probe report, before any statement changes.
- Any trusted text: none is expected. If P1 shows that in-process writes need a new trust-boundary spec
  (for example of a `context` call no example uses yet), or P2 a raft axiom, STOP.
- G1's `Start.spec` change (a linked spec): Freeze, `spec-reviewer`.
- G2's raft API law, if one is needed: its interface diff.
- The theorem's statement (Freeze), with N1/N2 for the user.
- Every `etc/land.sh`.

**Decisions requested:**
- **D-S7-1. One member, not three.** *Recommended.* Three members need R2s-A (the restart-only rows are false
  once a restarted member leads and snapshots a follower), HS3 and F4's chaining. They stay `restart3_safe`'s
  path.
- **D-S7-2. The workload: `N` in-process `Put`s of distinct keys, one `Range` after the restart, checked
  exactly.** *Recommended* over (b) one key written many times (`restart3`'s check, which cannot see a lost
  earlier write) and (c) txnlin's porcupine workload over gRPC (needs `GracefulStop`, R1').
- **D-S7-3. The read after the restart: in-process `Range`, or `Serve` + client `Get`.** *Recommended:
  in-process* (fewer moving parts, the same linearizable read path: `linearizableReadNotify`). A client read
  would add the gRPC/client stack, already proved for `putget`, at about +3 d.
- **D-S7-4. `#Hmembers` (S11) before S7's Freeze, or after.** *Recommended: after.* It is inherited by every
  closed theorem, and S7 adds no new instance of the flaw. Fix it once for all (S11), in parallel.
- **D-S7-5. The name.** *Recommended:* call this stage "S7 (restart1)", and keep "R2s-A" for the snapshot
  work under `restart3_safe`. Update `notes/restart-scope.md`'s table when this Scope is approved.
- **D-S7-6. Deleting `srvRestartRows` from `specR`.** With one member, `specR` keeps its premise and S7
  discharges it (G2). *Recommended:* keep `specR`'s text. R2s-A deletes the premise later, for every
  configuration.

**Risks.**
- P1: the in-process `Put` may need resources the examples get only through `Serve`'s stock split
  (`srvServeStock`). Then the stop's `srvStopReaders` needs the split undone after the `Put`s. Fallback:
  `Serve` the first incarnation and take R1' (`GracefulStop`, trusted, +1.5-2.5 wk).
- P2: if raft's API does not expose the destination of a sent message, the raft law is a raft-side proof
  over `InvNode` (sealed: a law added to the API module). Est. +1 wk.
- `NewServerR.lean`'s compile peaks at 8.6 GiB. The `restart1` link adds a module of `putget`'s size. Keep the
  64G cap.
- Docstrings and STATUS must say "graceful": N2.
