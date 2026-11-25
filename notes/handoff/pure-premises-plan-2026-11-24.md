# Pure premises of the top-level theorems: plan (2026-11-24)

Rule 38 (Upamanyu, 2026-11-24): eliminate pure premises by moving them into the Go program (it builds or
validates its configuration; an early `return` is fine, since `Robust` only rules out stuck threads and
panics). Premises that must stay get a compiled Lean satisfiability witness, and a gate in `etc/` (wired
into `etc/gates.sh` and CI) refuses a top-level theorem whose premises lack one. Added the same day: where
a premise becomes a Go check with an early exit that might never pass, a Go test must show non-vacuity
(the check passes and the real path runs, over many seeds when the generator is random).

Basis: etcd-grove `origin/lean` @ `94767c2a2f`, Perennial pin `b3f2fc485`. Read-only so far: nothing in
this plan was built. The Dsverify, Net and KvNet rows come from a helper's read, spot-checked against
`Robustness/Statement.lean`. Class (a), the Iris contracts, is out of scope (rule 36,
`plans/premises-to-axioms.md`).

Legend: **(i)** eliminate by a Go change; **(ii)** prove in Lean outright (no Go change, but the statement
changes: the premise is dropped); **(iii)** stays, with a witness. **NV** = needs a Go non-vacuity test.

## 0. Three general findings

1. **`Robust` already assumes the machines' initial extension states.** `Robust` (`Robustness/Statement.lean:87`)
   has `Fresh`, `extsInitGlobal g` and `extsInitLocal σ g` as antecedents. For the file extension,
   `initLocal := FsInit` (`GooseLang/Ext/Fs/Impl.lean:1324`); for the net extension, `initLocal := L.init`
   and `initGlobal := g.init` (`Net/Impl.lean:815`). So these premises repeat `Robust`'s own antecedents:
   - `Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world)` (etcd/all, leaseexpiryN, k8s/all, mvccfull, mvccrand),
     and `Hinit : FsInit …` (osfs ×5);
   - Net ×7 `Hconns : (extGlobal netExt g.globalWorld).conns = ∅`;
   - the two init conjuncts of `DistDeploy` (counter, 5× dsverify, putget_safe).
   **Correction (2026-11-24, from the witness build):** this holds only where the extension's semantics
   states `FsInit`, i.e. `fs_semantics` (the osfs examples, `fsExts`) and the net extension. The etcd
   examples run the file extension under `etcdFsSem` (`Fs.fsSemWithS`), which keeps Perennial's default
   `initLocal := True` (`putget/TopLevelDefs.lean` says so). So `Hfs` in etcd/all, leaseexpiryN, k8s/all,
   mvccfull and mvccrand is **not** redundant: it stays (iii), and the mvcc witnesses prove it
   (`fsInit_fsOneRoot`). Making `etcdFsSem` state `FsInit` as its `initLocal` would make it redundant
   there too, but that is a semantics change (trusted).
   **(ii)**, for osfs and Net only: drop them. The proof gets them from `Robust`'s antecedent through a projection lemma,
   `extsInitLocal σ g → initLocal (extLocal E σ.world) (extGlobal E g.globalWorld)` for `[HasExt E]` (and the
   same for global). That lemma does not exist yet. It is general, so it goes to Perennial (rule 12), on
   a branch off its `lean`, about 30 lines.
2. **The repository's own extensions lack the satisfiability witness Perennial asks for.** Perennial's
   `ExtSemantics.initLocal` docstring (`Lang.lean:575`) says `∃ g s, initGlobal g ∧ initLocal s g` must hold,
   or every theorem is vacuous. `Sha256` proves it; Fs and Net have no such lemma (checked by grep). These
   are the base witnesses that every top-level statement needs, since `Robust`'s antecedents are part of
   what must be jointly satisfiable. Phase 2 adds them (`FsInit` of a state with given roots; Net's empty
   state).
3. **Several (c)/(d) premises are opaque or axiom-declared Props, so no Lean witness can exist.** The
   opaque ones are `authRecordsFit`, `apply.backendUnderQuota`, `grpcRepliesFit`, `storage.dbOpensOk`
   (through `diskOk`), `leasePeersOk` and `lease.leasesNoExpiry`. The axiom-declared ones are
   `verifyEnvOff`, `addrUnclaimed` (through `addrsUnclaimed`), `dataDirAbsent` and `dataDirsApart`
   (through `dataDirsAbsent`). Lean says nothing about them except through the axioms that mention them.
   An uninterpreted Prop is consistent with any witness of the other premises, but no theorem can show
   that. The gate therefore records each such binder in a baseline with the class `opaque`.
   **Decision for Upamanyu (D1):** accept `opaque` as a permanent gate class whose review is the
   `axiom` skill's review of the axioms that consume it, or require each to become a definition that can
   be witnessed (L per item). Recommendation: accept, and turn into definitions only those that are
   facts of the example's own workload (`authRecordsFit`, `backendUnderQuota`, `grpcRepliesFit`: the
   example writes those records itself), as separate work.

## 1. Per statement

### 1.1 No pure premise beyond `Robust`'s own (witness only, nothing to eliminate)
`raft_kv_porcupine_robust`, `raft_kvreconf_porcupine_robust`, `raft_kvwitness`'s two, `goose_prophkv_robust`,
`k8s_authz_robust`, lintest ×6 (`counter_robust`, logkv, logkvappend, logkvcompact, logkvrw, logkvsnap),
`osfs/walfs seglog_crash_robust` (apart from `Hinit_wp`, (a), and `Hdir`, below). Witness: `Fresh` plus the
extensions' initial states (finding 2).

### 1.2 Workload size parameters of a program family: (i) validate in `MainN`, NV
`raft_kvN`, `raft_kvreconfN`, `raft_kvdurableN` (main and RaftNoAx): `(hk1 : 1 ≤ k) (hk : k ≤ 1000)` on
`MainN(k)`.
- Go: the first statement of `MainN` is `if k < 1 || k > 1000 { return }`. The theorem keeps `∀ k` and
  drops `hk1`/`hk`.
- Proof: the spec of `MainN` loses the bound. Its proof takes the early-return branch, and the other
  branch carries the bound as today. S.
- NV test `TestMainNRange` (one per package): `MainN(0)` and `MainN(1001)` return; for 50 random `k` in
  [1, 1000], `MainN(k)` reaches the porcupine check (an exported counter, or a hook the check bumps).
- Alternative: `Main` draws `k := 1 + below(1000)` and the family collapses into one program. That is a
  weaker statement (one program, not each k), so I don't recommend it.

### 1.3 kvdurable `Hfiles` (each member's durable file absent at start)
- (i): `Main` checks each file with `durable`'s read operation and returns if one exists. Feasible only
  if `durableExt` exposes an existence result; to check. The proof then handles a present file by
  returning. M.
- Fallback (iii): witness the empty durable map (S).
- Recommendation: (iii) now, and (i) when kvdurable moves to the bodied `durable` (`WalTester/`, already
  planned). A Go existence check over a trusted extension adds no trust.

### 1.4 mvccfull / mvccrand
| Premise | Class | Action |
|---|---|---|
| `Hfs` | redundant | (ii), finding 1 |
| `Hrfit : Fs.DirFits r` (`r.length < 3800 ∧ WinOk r`) | (i), NV | `Main(r)` checks `len(r) < 3800` and that every 256-byte window holds a `/`, and returns otherwise. The proof equates the Go loop with `WinOk`, M. NV: `TestDirFits` (the test harness's real temp dirs pass; a 4000-byte path returns early). |
| `Habs` (the db names absent under `r`) | (i), NV | `os.Lstat(r+"/"+name)`: return unless every result is `ENOENT`. Needs `Lstat`'s Fs spec to give absence (the Fs model has `lookup`; to check it is exposed). M. NV: the test's fresh temp dir passes. |
| `Hr : (r, j0) ∈ roots` | (iii) | The directory exists and is a root of the model; Go cannot observe "is a root". Witness: an Fs state with roots `[(r, 0)]` and an empty tree. |
| `HEnv` | opaque | baseline |
| `Hsort` | (a) | out of scope (item I) |

### 1.5 osfs (bboltfs `bootCrashRobust`, crashlog `crash_robust`, walfs ×3)
| Premise | Class | Action |
|---|---|---|
| `Hinit : FsInit` | redundant | (ii) |
| `Hdir` (dir is a root) | (iii) | witness |
| bboltfs `Hnone` (`dir/db` absent), crashlog/walfs `Hnd` (log or segment not a directory) | (i) or (iii) | (i): boot `Lstat`s the path and returns if the absence or non-directory condition fails, M each. These are crash examples: the check runs at every boot, so the proof must show the program's own files always pass it. They do, since it only creates regular files there. Recommendation: (iii) witness (empty dir) now; (i) later, together with the next item. |
| crashlog `Hlog`, walfs `Hseg`/`Hsafe` (`Good`/`DataGood`/`SafeT` of the initial contents) | (i) L, or (iii) | (i): recovery validates the contents and starts over (truncate) on bad data. The proof must cover arbitrary initial bytes, which changes the recovery proof (L). (iii): an empty dir satisfies each premise, since the implication is vacuous when the file is absent. Recommendation: (iii). These examples are about crash recovery of the program's own writes, so arbitrary initial contents are a different theorem. |
| `Hinit_wp` | (a) | item J |

### 1.6 Net ×7, counter, dsverify ×5: `Hconns`, `DistDeploy`
- `Hconns` and `DistDeploy`'s init conjuncts: redundant, (ii).
- `DistDeploy`'s `addrs.Nodup ∧ ∀ a, addrOk a` are over closed constants (`counterAddrs`, `PaxosAddrs`,
  …): (ii) by `decide` inside the proof, so the whole `DistDeploy` premise goes. The Go program needs no
  change: its addresses are the constants.
- dsverify's other items are (a) or (d) under rule 36 (`premises-to-axioms.md` §2.3). One (i): swiftnet's
  `SwiftOsRandom` goes away if the client calls `uuid.NewRandom()` and handles the error
  (`client/client.go:56`, `client/buffer.go:206`), which needs a fork rewrite (rule 14). NV:
  the existing swift run test covers it.

### 1.7 kvnet (`raft_kvnet_robust`)
| Premise | Class | Action |
|---|---|---|
| `cl.Ok replicas.length`, `replicas.length < 2^32`, `Nodup`, `addrOk` | (i), NV | Already checked in Go, but by `panic`: `node.go:115-117` (`ValidCluster`), `kvcheck/kvcheck.go:231-232` (`ValidAddrs`). Change each `panic` to `return`. The proof's failure branch becomes a return. S. |
| `dir.length < 2^39` | (i), NV | Add `if uint64(len(dir)) >= 1<<39 { return }` before `FileOf` (`node.go:83`). S. |
| `dir` is a root and is empty | (iii) | Witness. Emptiness could be (i) by a `ReadDir`, but rootness stays (iii), so keep both together. |
NV `TestValidDefaultCluster`: the example's configuration and 100 random valid clusters from the
generator pass `ValidCluster` and reach `kvcheck`'s linearizability check.

### 1.8 etcd/all, leaseexpiryN, k8s/all (single process) and putget_safe (dist branch)
| Premise | Class | Action |
|---|---|---|
| Workload numbers: `clients ops nw nops cnw cnops watchers wops` with their sign/product bounds | (i), NV | The program's parameters become Go-drawn values (`below(n)` over the allowed ranges) or validated arguments (`if !(0 <= clients && clients < 1<<31 && clients*ops < 1<<60) { return }`). Recommendation: validate. The theorem keeps `∀` and drops the bounds. M (the product check over `int64` needs overflow care: check `ops == 0 \|\| clients <= (1<<60-1)/ops`). NV: random arguments in range reach the linearizability checks. |
| `steps₁ steps₂ : List Step` with `length < 2^63` | (ii) or (i) | A Go slice always has `len < 2^63`. If the Lean list is turned into a Go slice by the program expression, the bound may follow from that, which needs checking. Otherwise (i): the program generates its fault schedule itself (`below`), and the theorem drops `steps`. Recommendation: (i) generate; same NV test. |
| `k₁…k₅` ranges (`1 ≤ k ≤ 1000/300/600`, `3 ≤ k₅`) | (i), NV | As in 1.2: `Main` validates and returns. S each. |
| `ids … ps ctxs boot` with `Hlen`, `Hbf*` (`BootFacts`/`BootCore`), `Hlow`, `Hap` (`leaseIdsApart`) | (b), blocked | These state what Go computes (SHA-1 member ids, JSON contexts, the marshalled boot log over the opaque `ccDecodeV1`). No Lean definition of the ids exists, so no witness, no `decide` and no Go-side elimination is possible yet. Prerequisites: survey item A (`bootstrap` as an axiom stated over `memberIdOf`/`bootCtxsOf`/`bootLogOf`, #34) and a concrete `ccDecodeV1` (§2). After those: the fixed clusters (partition, compactwatch, compacted, cache/putget, cluster3/leasecatchup, restart1) are (ii) by evaluation. Kernel cost of SHA-1 is unknown, so measure before promising it. The `∀ k` families are (i), NV: `Main` computes the member ids the way etcd does (`membership.NewMember(...).ID`, verified or under A's `memberIdOf`) and returns if their low 16 (or 15) bits collide or are 0. NV: the existing `TestMemberIDs` extended to every k in range. L, owned by #34. |
| `Haf Hbuq Hrf Hdbo Hlp Hlne`, `HAs HDs HEnv` | opaque | baseline, D1 |
| `Hfs` | redundant | (ii) |
| `HWal : etcdWalAreasInit` | (iii) | Witness: an Fs state with roots for each `walAreaOf d` and each `d` of `etcdDirs`, all empty. |
| putget_safe `peer client` with `DistDeploy (addrs peer client)` | (i), NV | `Main(peer, client)` checks `AddrOk(peer) && AddrOk(client) && peer != client` (kvnet's `AddrOk`) and returns otherwise. The init parts are redundant. NV: the deployment's literal addresses pass. |
| putget_safe `MemberFiles σm`, `ClientFiles σc` | (iii) | witness |
| `etcd_robust` (dist draft: `Hd : d.WellFormed`, `BootFacts d`, `EtcdEnv`, `TrustBoundary`) | draft | Not instantiable today, so it goes in the baseline as `draft`. Later, `WellFormed` is (i): the deployment program validates its own `Deployment`. |

### 1.9 raft_tracecheck: the worked example of (i)
Today (`RaftTla/Spec/.../tracecheck/TopLevelRobustness.lean`):
```
∀ [lctx] [sem] [package_sem] [hLog : log.NewModel] (boot : List LogEntry) (Hbf : tracecheck.BootLogFacts boot)
  (Hprem : ∀ hG, ⊢ tracecheck.premises boot) (σ) (g), Robust [] [(tracecheckProgram, σ)] g …
```
`BootLogFacts boot = BootLog [1,2,3] [[],[],[]] boot`: three conf-change entries whose data `ccDecodeV1`
decodes to `AddNode i`. `ccDecodeV1` is opaque (`CCModel.lean:47`), so nothing can prove or witness it.
That is why it is a premise. `Hprem` (the `bootMarshal` contract) is (a), and the
`tracecheck-nonvacuous/2026-11-24` branch makes it satisfiable (empty context = `nil` slice;
uncommitted in that worktree as of 08:30Z). Its `premises_of_marshal` guard shows `Hprem` is the
marshal contract alone, which is what axiom B will discharge.

Proposed change, in three steps:
1. **Concrete `ccDecodeV1`** (protobuf boundary, #37; the sibling of stage S1, which made `ccDecodeV2`
   concrete as `cc2DecodeRaw` with `EntryWireVectors` checked against protobuf-go): `ccDecodeV1 :=
   cc1DecodeRaw`, plus a vector test. It adds no axiom, but it strengthens what the existing
   `proto.{Marshal,Unmarshal}ConfChange` axioms claim (decoding is now a fixed function), so it goes to
   Upamanyu with the vectors as evidence, as S1 did.
2. **(ii) for the current harness:** `tracecheck.bootLog : List LogEntry := [⟨1, 1, ccBootWire i none⟩ | i ∈ 1..3]`
   (B's encoder), and `BootLogFacts bootLog` by `decide`. The statement drops `boot` and `Hbf`, and
   `Hprem` is stated at `bootLog`.
3. **(i) random configuration:** `Main` draws the bootstrap size:
   ```go
   func Main() {
   -	c, err := RunConcurrent(DefaultCConfig())
   +	cfg := DefaultCConfig()
   +	cfg.Nodes = 1 + below(5) // the bootstrap voters, ids 1..Nodes
   +	c, err := RunConcurrent(cfg)
   ```
   Statement after:
   ```
   ∀ [lctx] [sem] [package_sem] [hLog : log.NewModel]
     (Hprem : ∀ n, 1 ≤ n → n ≤ 5 → ∀ hG, ⊢ tracecheck.premises n (tracecheck.bootLog n))   -- until axiom B retires it
     (σ) (g), Robust [] [(tracecheckProgram, σ)] g …
   ```
   Proof: `RunConcurrent.spec` drops `cfg.Nodes' = W64 3` for `1 ≤ Nodes ≤ 5`. The loop invariant is
   already written over the list `tcVoters` (`RunConcurrent.lean:388-460`); `tcVoters`/`tcCtxs` become
   functions of `n` (`ProbeA.lean`: 21 uses). `BootLog [1..n] (replicate n []) (bootLog n)` is proved for
   every `n` by a lemma over `cc1DecodeRaw (ccBootWire i none)`. M. Risk (an inference, unchecked):
   `etcdraft.CheckTrace`'s verified acceptance, which `Main` panics on, may assume three servers. To check
   in `RaftTla/Proof/.../etcdraft/` before committing to (i). If it does, keep step 2 alone.
   NV test `TestMainRandomNodes`: 200 seeds of the generator, each run passes `RunConcurrent` and
   `CheckTrace(…).TLCOK()` with `Nodes` in 1..5. The existing `concurrent_test.go` runs only the
   default config. Without such a test, a size whose runs always fail TLC would make the theorem's
   real path dead for that size, which panics and so is not vacuous, but the test is what shows the
   check holds.
   **Run 2026-11-24** (go1.27.3, `-tags with_tla`, 3 runs per size, 26 s): every size 1..5 started,
   read as a trace and passed `CheckTrace(…).TLCOK()`; with 1 node no message crosses the network but
   the trace is still validated. The test is `pure-premises-packets/tracecheck-nv-test.diff` and the Go
   change is `pure-premises-packets/tracecheck-main.go.diff`; neither is on a branch. This settles the
   Go side of the risk above. Whether the Lean proof of the check is generic in the number of servers
   is still unchecked.
   With step 3 the statement no longer names any boot value, and B then removes `Hprem`.

Order: steps 1 and 2 are independent of `tracecheck-nonvacuous` (they touch the statement and `Defs.lean`,
which that branch also edits). Build on that branch once it is pushed. Do not race it: its
`Defs.lean` edits land first.

## 2. Prerequisites and owners
- Projection lemma `extsInitLocal → initLocal` (Perennial branch, untrusted, S). Unblocks every
  "redundant" row.
- Concrete `ccDecodeV1` (#37, trusted model change, needs Upamanyu). Unblocks the trace check and every
  `BootLog` fact.
- Item A `bootstrap` axiom with `memberIdOf` etc. (#34). Unblocks every etcd `BootFacts`.
- D1 (opaque class).

## 3. NV tests needed (rule 38)
| Elimination | Test | What it shows |
|---|---|---|
| 1.2 `MainN` k range | `TestMainNRange` (kv, kvreconf, kvdurable, kvdurablenoax) | out-of-range k returns early; 50 random in-range k reach the porcupine check |
| 1.4 `DirFits`, `Habs` | `TestMvccDirChecks` | real temp dirs pass both checks and reach the mvcc check; long path and existing db return early |
| 1.5 (if (i) chosen) | `TestBootChecks` per osfs example | fresh dir passes; restart after a crash still passes |
| 1.7 kvnet | `TestValidDefaultCluster` | the example's and 100 generated clusters pass `ValidCluster`/`ValidAddrs`, `kvcheck` runs |
| 1.8 workload validation / generated schedule | `TestEtcdAllWorkloadInRange` (and k8s, leaseexpiryN) | 50 random workloads pass validation and reach each sub-check |
| 1.8 member-id check (after A) | `TestMemberIDs` over every k | every configuration in range passes the low-bit check |
| 1.8 putget addrs | `TestPutgetAddrsOk` | the deployment's addresses pass |
| 1.9 trace check | `TestMainRandomNodes` | 200 seeds: every size 1..5 passes `CheckTrace` |
Rows (ii) and (iii) need none.

## 4. The witness gate (phase 2, branch `premise-witness/2026-11-24`)
- **Lean:** `Robustness/PremiseSat.lean`, a term elaborator `premise_sat% X.spec`. It unfolds the
  definition and walks its `∀` telescope, building a goal:
  - instance binders (`[sem : go.Semantics]`, …) and the definition's own parameters stay `∀`;
  - data binders (`σ`, `g`, `k`, `ids`, …) become `∃`;
  - Prop binders become conjuncts;
  - dropped: Prop binders that mention `HeapGS` (Iris contracts, class (a), rule 36), binders named in an
    explicit `without [..]` list, and every binder that depends on a dropped one;
  - `Robust crashing stable g …` conclusion: replaced by its antecedents, `(∀ m ∈ crashing ++ stable,
    Fresh lctx m.2) ∧ extsInitGlobal g ∧ ∀ m ∈ …, extsInitLocal m.2 g`, so the witness shows the
    premises are satisfiable *together with* `Robust`'s own start conditions (the thing whose failure
    makes a theorem vacuous).
  A witness is `theorem X.premisesSat : premise_sat% X.spec without [..] := …` in
  `Proof/<example path>/TopLevelWitness.lean` (a part's under its root), a defs-tier leaf.
- **Script:** `etc/premise-witness.py --check`. For every `def X.spec` in a `Spec/**/TopLevelRobustness.lean`
  (parts included), it requires the witness file and theorem, and requires every `without` binder to be
  listed in `etc/premise-witness-baseline.txt` (`<spec> <binder> <class> <reason>`, class ∈ `opaque`,
  `pending-b` (BootFacts family, blocked on §2), `pending` (to witness), `draft`). `--check --update`
  only shrinks the baseline. The Lean build checks the proofs. The script reads source only and builds
  nothing, like `tier-check.py`.
- **Wiring:** a section in `etc/gates.sh`, and a step in `.github/workflows/lean.yml` before the build.
- **Witnesses in this branch:** the base Fs/Net initial-state lemmas, then every statement whose
  remaining pure premises are only `Robust`'s antecedents and start state. The others start in the
  baseline and are witnessed or eliminated one at a time.

## 5. Statement-change packets (prepared 2026-11-24, overnight; nothing landed)
Files are in `plans/pure-premises-packets/`. Each is a Go diff with its NV test. The Lean side (spec of
the changed Go function, its proof, and the statement) follows once a packet is accepted: retranslate
(`etc/goose.py --project …`), re-prove the changed function's early-return branch, and drop the
premise from the statement.

| # | Packet | Statement change (premises dropped) | Go change | NV test, run |
|---|---|---|---|---|
| P1 | tracecheck | `boot`, `Hbf : BootLogFacts boot` dropped (needs concrete `ccDecodeV1` first, §1.9); `Hprem` at `bootLog n`, `∀ n ∈ [1,5]` | `Main` draws `cfg.Nodes = 1 + below(5)` | `TestMainRandomNodes`: sizes 1..5 × 3 runs pass TLC |
| P2 | kvN, kvreconfN, kvdurableN (+ RaftNoAx) | `hk1 : 1 ≤ k`, `hk : k ≤ 1000` | `MainN`: `if k < 1 \|\| k > 1000 { return }` | `TestMainNRange` ×4: pass |
| P3 | mvccrand, mvccfull | `Hrfit : DirFits r`, `Habs` (db names absent); program `Run(cfg r)` becomes `MainAt r` | `start.go`: `dirFits`, `absent` (`os.Lstat` + `fs.ErrNotExist`), `MainAt` | `TestMainAt` ×2: pass, incl. long dir and existing db returning untouched |
| P4 | etcd/all | `Hc0 Hc31 Hops Hmul Hnw0 Hnw31 Hnops Hnmul Hcnw0 Hcnw31 Hcnops Hcmul hk*1 hk*` and `steps₁ steps₂ Hsteps₁ Hsteps₂`; the program becomes `MainChecked k₁ clients ops n₁ nw nops n₂ cnw cnops k₂ k₃ k₄ k₅` | `all.ParamsOk`, `all.MainChecked`, `cluster3.RandomSchedule` | `TestParamsOk` (200k boundary draws vs big.Int): pass; `TestMainCheckedRun` (k=3, random schedules): pass, 30 s |
| P5 | k8s/all | the same for `clients ops watchers wops k₁ k₂ steps₁ steps₂` | `k8sall.ParamsOk`, `MainChecked` | `TestParamsOk`: pass; end-to-end not run: the unmodified `TestMain` fails on this machine too ("failed to create WAL" in `bootstrapNewWAL`, 0.1 s), a pre-existing environment problem |
| P6 | leaseexpiryN | `hk1`, `hk` | `Main`: range check | `TestMainRange` + the existing `TestMainRun` (random k in {1,2,3,5,7}): pass |
| P7 | putget (dist) | the `addrs.Nodup ∧ addrOk` part of `DistDeploy` (init parts redundant, §0) | `Member`/`Client` check `AddrOk` (kvnet's, moved to a shared package) | deferred: it touches `examples/raft/kvnet`, which another agent is editing |
| P8 | kvnet | `cl.Ok`, `replicas.length < 2^32`, `Nodup`, `addrOk`, `dir.length < 2^39` | panic → return at `node.go:115`, `kvcheck.go:231`; a `len(dir)` check | through the coordinator to the raft lead |
Remaining after these: `BootFacts`-family (needs A + concrete decoders), opaque environment Props (D1),
start-state premises (witnessed).
