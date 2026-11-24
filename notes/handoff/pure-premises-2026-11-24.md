# Handoff: pure premises of the top-level theorems (rule 38) and the premise gate, 2026-11-24

Workstream of coordinator F's "pure premises" lead. The plan this follows (classification of every
top-level statement's pure premises, the gate's design, the statement-change packets) is
`notes/handoff/pure-premises-plan-2026-11-24.md` (a copy of the lead's local plan as of the wrap-up).

## Goal and decisions

**Goal (Upamanyu, 2026-11-24).** Top-level theorems should have no pure Lean premises where avoidable.
- A premise the program can establish moves into the Go program: the program generates or validates its
  configuration (`if !ok { return }` is a safe run under `Robust`), and the theorem covers whatever the
  code produces. Where such a check might never pass, a **Go non-vacuity (NV) test** shows it passes and
  the real path runs, over many seeds where the generator is random.
- Premises that must stay (start state, environment) get a **compiled Lean satisfiability witness**. A
  gate refuses a statement whose premises lack one.
- Iris contract premises (class (a)) are out of scope here: rule 36 turns them into per-function axioms.

**Decisions made by Upamanyu:**
- The goal above.
- Statement changes are prepared as completed work for his review: built and pushed on branches. They
  are not landed without his OK.

**Decisions made overnight** (Upamanyu was away and asked for decisions to be recorded, not waited on;
each needs his look):
1. **Range checks validate rather than draw.** kvN, leaseexpiryN and the etcd/k8s workload numbers use
   `if out of range { return }`. This keeps the theorem universally quantified over the parameter,
   which is stronger than covering one randomly-drawing program.
2. **Fault schedules are drawn in Go** (`cluster3.RandomSchedule(n)`). A Lean list literal's
   `length < 2^63` premise cannot be validated from Go.
3. **Opaque or axiom-declared environment Props are a permanent gate class `opaque`.** These are
   `verifyEnvOff`, `addrsUnclaimed`, `dataDirsAbsent`, `authRecordsFit`, `backendUnderQuota`,
   `grpcRepliesFit`, `diskOk`/`dbOpensOk`, `leasePeersOk` and `leasesNoExpiry`. No Lean proof can
   establish an opaque Prop; their meaning lies in the axioms that consume them.
   - Alternative: turn each into a definition that can be witnessed.
   - Recommendation: do that only for the workload ones the example itself controls (`authRecordsFit`,
     `backendUnderQuota`, `grpcRepliesFit`).
4. **P6: leaseexpiryN's `k : Nat` becomes `k : w64`.** Without the range premise, a Nat k ≥ 2^64 wraps
   when passed to Go, while the premises indexed by k would describe another cluster.
   `cluster k := if 1 ≤ k ≤ 1000 then members k else []` names the addresses and directories.
   - Alternative: keep a `k < 2^64` premise.
   - Every program the old statement covered is still covered.
   - **Needs Upamanyu.**
5. **P1: `ccDecodeV1` made concrete** (`cc1DecodeRaw`, checked against protobuf-go by vectors, as stage
   S1 did for `ccDecodeV2`). This is a **trusted model change** and needs his review. It adds no axiom,
   but the existing `proto.{Marshal,Unmarshal}ConfChange` axioms now speak about a fixed decoder.
6. **P1: the step bound goes from `2^61 - 3` to `2^61 - 5`,** because `Main`'s random draw takes steps.
   This narrows the conclusion slightly. **Needs Upamanyu** (rule 17: no weakening lands without his OK).

**Findings:**
- **`raft_tracecheck_safe`/`_robust` was vacuous on lean until branch `tracecheck-nonvacuous/2026-11-24`.**
  Its premise had `bootMarshal`'s `∀ c ∈ ctxs, c ≠ []` at empty contexts. That branch is another
  agent's; it is merged into P1.
- **`Robust` already assumes `Fresh`, `extsInitGlobal` and `extsInitLocal`.** For the file extension
  under `fs_semantics` (osfs) and for the net extension, these cover `FsInit` and "no connection, no
  listener". So those statements' `Hfs`/`Hinit`/`Hconns` premises, and `DistDeploy`'s init conjuncts,
  are redundant. **But** the etcd examples run the file extension under `etcdFsSem`, which keeps
  Perennial's default `initLocal := True`. There `Hfs` is **not** redundant; the mvcc witnesses prove it.
- **Fs and Net had no satisfiability lemma for their initial states,** although Perennial's
  `ExtSemantics.initLocal` docstring asks for one. `Robustness/FsStart.lean` now provides `fsOneRoot`
  and `fsInit_fsOneRoot`.

## Branches (all on github.com/upamanyus/etcd-grove)

| Branch | Head | What | State |
|---|---|---|---|
| `premise-witness/2026-11-24` | see below (this handoff's commit) | The gate: `Robustness/PremiseSat.lean` (`premise_sat% X.spec [without [h,…]]`, `RobustStart`, `freshState`, `exts_init`), `Robustness/FsStart.lean`, `etc/premise-witness.py` (`--list`, `--check [--update]`), `etc/premise-witness-baseline.txt`, wiring in `etc/gates.sh` (`sec_api`) and `.github/workflows/lean.yml`; 24 `TopLevelWitness.lean` files (29 of 47 statements witnessed, 20 baseline lines) | Untrusted. `f1c3f2b4a1`: all 26 modules built on the VM (exit 0, no sorry), on lean `b0a063163c`. `66eac57c9f`: merge of origin/lean `32df6865ea` plus a baseline line for the new `etcd_wal_safe`; source gates ok; **the witnesses were not rebuilt on the merged tree** (the build was stopped at wrap-up). Not yet queued. |
| `premise-kvN-range/2026-11-24` | `c87e85ec2b` | P2: the raft kv family's `MainN(k)` range check (kv, kvreconf, kvdurable, RaftNoAx kvdurablenoax); the four kvN statements drop `hk1 : 1 ≤ k`, `hk : k ≤ 1000` | Built on the VM (5944 + 4250 jobs), gates ok. Based on premise-witness `f1c3f2b4a1`. NV `TestMainNRange`: kv and kvreconf pass; kvdurable and noax timed out under machine load in the in-range runs (early returns passed; passed earlier unloaded): rerun. A statement change: **needs his OK**. |
| `premise-leaseexpiryN-range/2026-11-24` | `74e04c603b` | P6: leaseexpiryN's `Main(k)` range check; `hk1`/`hk` dropped; `k : w64` (decision 4) | Built on the VM (10,615 jobs), no sorry, axioms match `etc/tcb-collections/leaseexpiryN-single-process.txt`. Based on premise-witness `f1c3f2b4a1`. NV: `TestMainRange` plus the existing `TestMainRun` pass. **Needs his OK** (statement text). |
| `premise-tracecheck-nodes/2026-11-24` | `75ab183ca6` | P1: (1) concrete `ccDecodeV1` (**trusted**); (2) the bootstrap log computed, `boot`/`Hbf : BootLogFacts` dropped, witness added; (3) `Main` draws `cfg.Nodes = 1 + below(5)`, harness proof generic in the voter count, `Hprem` per size | Full VM `lake build` exit 0 on the tree of `4b8bb1d373` (identical to `75ab183ca6`). Based on premise-witness `f1c3f2b4a1` + `tracecheck-nonvacuous/2026-11-24` `8002a9eab4`. NV `TestMainRandomNodes` (`-tags with_tla`): sizes 1..5 pass TLC. **Needs his review** (decisions 5, 6). `p1-tracecheck-s3-local` @ `4b8bb1d373` is a redundant intermediate. |
| `premise-etcd-params/2026-11-24` | `d30a709664` | P4/P5: etcd/all and k8s/all: `ParamsOk`/`mulBelow` validation, `cluster3.RandomSchedule`, entry point `MainChecked`; statements drop the workload bounds, k ranges and `steps` binders | **WIP, not built.** Go side done; NV: `TestParamsOk` (200k draws vs big.Int) passes for both; etcd's `TestMainCheckedRun` passed end to end (30 s). k8s's end-to-end run is blocked by a pre-existing local "failed to create WAL" in the unmodified `TestMain`. Lean specs/proofs written; the last full VM build failed (ParamsOk local macros / `rotate_left`, mulBelow b = 0 case, MainChecked's Bool destruct, Adequacy line ~304, k8s mulBelow instance). At wrap-up: merged premise-witness `66eac57c9f` cleanly (goose `--check` ok for cluster3, etcd-all, k8s-all); added, following P6, `etcdProgAddrs`/`etcdProgDirs` and `k8sProgAddrs`/`k8sProgDirs` (empty when a member count is out of range) and a `b = 0` split in `mulBelow`; no build since (the VM build b4 never got a slot). Cause of ParamsOk's "unknown tactic" not found yet. |
| `premise-mvcc-mainat/2026-11-24` | `61abfae2e0` | P3: mvccrand/mvccfull `MainAt(r)`: `dirFits(r)` and absence of every file (`os.Lstat` + `errors.Is(err, os.ErrNotExist)`); statements drop `Hrfit : DirFits r` and `Habs` | **WIP, not built.** Retranslated; helper lemmas `Proof/os/LstatAnyS.lean`, `Proof/runtime/RootClaim.lean` (check that they are proved, not axioms); specs/proofs of `dirFits`, `absent`, `MainAt` in progress. At wrap-up: merged premise-witness `66eac57c9f` cleanly; generated files consistent (goose, gen-init, gen-link); source gates pass; reviewed: no new axiom or sorry, the `etc/goose.py` change only adds the `os=`/`io/fs=` roots other file-system projects use. NV: mvccrand `TestMainAt` passes; mvccfull's timed out (go test's 10 min, inside `Run`, loaded machine): rerun with `-timeout 90m`. No Lean module of this change compiled yet. |

Not implemented (plan §5):
- **P7 putget (dist):** check `AddrOk(peer) && AddrOk(client) && peer != client` in Go. This needs kvnet's
  `AddrOk` moved to a shared package.
- **P8 kvnet:** change `panic` to `return` at `examples/raft/kvnet/node.go:115` and `kvcheck/kvcheck.go:231`,
  and add `if uint64(len(dir)) >= 1<<39 { return }` before `FileOf`. Then `cl.Ok`, `replicas.length < 2^32`,
  `Nodup`, `addrOk` and `dir.length < 2^39` go. Belongs to the raft lead (kvnet).

Nothing from this workstream is queued or landed yet. No GitHub asks are open from this workstream.

Per-packet resume notes of the helpers (their last state, logs named there are on the old machine):
`notes/handoff/pure-premises-{P1,P2,P3,P45,P6}-resume-2026-11-24.md`.

## Next steps
1. Build `premise-witness` on the merged tree:
   `vmlake build Robustness.PremiseSat Robustness.FsStart` plus every `*TopLevelWitness` module
   (`git ls-files '*TopLevelWitness.lean'`). Fix what lean's 138 commits broke, then queue it. It is
   untrusted, so it can land without review.
2. Merge the new premise-witness into P2, P6 and P1 (they are based on `f1c3f2b4a1`), rebuild, and send
   them to Upamanyu as statement packets one at a time (before/after statement, Go diff, NV test). P1
   carries the trusted `ccDecodeV1` change.
3. Finish P4/P5: fix the build errors listed above (spec-first: `ParamsOk.spec` returns true iff the
   premises hold; `MainChecked` over `Main`'s spec). If out-of-range k meets premises indexed by k,
   follow P6's precedent (`k : w64`, empty cluster out of range).
4. Finish P3: confirm `LstatAnyS`/`RootClaim` add no axiom, then prove `dirFits` (window invariant to
   `WinOk`), `absent` (per-name loop over `FilePaths`) and `MainAt`, and the closed theorems.
5. Then: Fs witnesses for osfs (lookups below a root), kvnet, etcd's `HWal` (a multi-root `fsOneRoot`) and
   WalTester's `etcd_wal_safe`; and P7/P8.

## Pitfalls
- **Meta code in `namespace Perennial` misresolves.** `Expr` becomes GooseLang's and `||`/`&&` become
  Iris notations. Keep elaborators in a root namespace (`PremiseSatMeta`) and use `Bool.or`/`Bool.and`.
- **`RobustStart` must declare every instance binder `Robust` has,** even unused ones (Lean drops
  unused section variables), so that `premise_sat%` can pass it `Robust`'s arguments.
- **A witness file must repeat its statement's `attribute [local instance] …` and `open` lines;** the
  helpers need the closed extension list. Pass `σ`/`g` explicitly (`robustStart_one (σ := …) (g := …)`):
  an anonymous constructor elaborates before they are unified. `extLocal` of a concrete tuple reduces by
  `rfl`; `exts_init` handles the extensions' init conjuncts.
- **vmlake's automatic gc can delete a new worktree's sync directory during its first long sync**
  (rsync exit 23). Workaround: create `.vmlake/last-used` in the VM sync directory and hold
  `.vmlake/inuse` with `flock` during the first `vmlake sync`; or rerun an explicit `vmlake sync`.
- **Go tests:** set `TMPDIR` to a scratch directory outside `/tmp` (the per-user `/tmp` quota ran out).
  kvdurable's NV tests take minutes and time out under load. k8s/all's `TestMain` fails locally with
  "failed to create WAL" (pre-existing).
- **`etc/api-check.py` takes one `etc/api/*.txt` per call.**

## Pickup (2026-11-24, second machine)
- premise-witness: merged origin/lean `366ab8486d` (55 more commits) as `603e7a78b8`; VM build of
  `Robustness.PremiseSat Robustness.FsStart` + all 24 `*TopLevelWitness` modules: exit 0, 5351 jobs, no
  `sorry` outside GeneratedProof (pre-existing). Nothing needed fixing. Source gates (api, import-all,
  tier, premise-witness --check) ok. Land-queue request sent through the pickup report (not queued here).
