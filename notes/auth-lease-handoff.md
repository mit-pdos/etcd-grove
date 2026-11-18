# auth-lease handoff (`etcd_authlease_safe`)

## START HERE (S4, 2026-11-18 late, item 9: thaw 1 done; Cell in progress)

- Branch `auth-lease-s4`, worktree `/shared/etcd-grove-rs56`. Pin **6d365ee1a** (`--packages=/shared/tmp/manifest-6d3.json`,
  `.lake/package-overrides.json` its copy). A merge bringing pin f551a1b46 / manifest-f55 is coming: switch when merged.
- **Thaw 1 (user-approved option (A)) done** `fe14388f43`: `writeGrantG` gains grant freshness (revocable-mode grant id `g`:
  no key had lease `g` at any revision ≤ σ.rev); server proof `GrantFresh.lean` (+ `kv_prop_au_on`), client law
  `writeGrantG_grant_fresh` (`LeaseReqOn.lean`). Recorded: `notes/auth-lease-s4-freeze.md` "Thaw 1" (old/new text,
  independent attack: no refutation, X1-X3 named in the docstring), ledger 2026-11-18. No compaction premise needed.
- **Build of the thaw's 51 leaves** (`/shared/tmp/auth-lease-s4/thaw-leaves.txt`, log `thaw-build.log`): queued for a
  slot for hours at 22:45; NOT yet run. Run it (build-slot) before anything else; `tcb-report --check` after (no axiom change expected).
- **Cell**: `authlease/CellModel.lean` (pure, CHECKED 0 errors: `CellOk` and its preservation by grant/putZ/putA/txnT/
  revokeU, `cellOk_fix`, `cellOk_fresh`, `not_leaseOk_setupSt`). `authlease/Cell.lean` (Iris, WRITTEN, NOT COMPILED: needs
  the build): `cellInv` (ids ½ main, ps, gs, d with `⌜d=0⌝ ∨ lb a 1`, v = rev lb, a ½ main = revocation permit),
  `cell_writeAu`/`cell_readAu`/`cellSeen`, per-update AUs, `cell_fix`, `cell_permit`, `cell_not_revoked`.
  Design change vs the earlier sketch: the leases live in `ids` (fixed by the main thread), `ps` holds only revisions;
  the permit `a` lets the main thread refute `revoked` (foreign Revoke(Lu) successes) before u's revocation.
- **Next, in order:** compile Cell (`etc/lean-check.py --fast`), fix; refutation lemma from `clientGrant` (lease-aware
  `akOpGranted_of_grant`: `writeGrantG_granted` + `akAuthFixed_write` + `akUser_hdr` → `kvGrantedL (setupSt r)
  (leaseItemsOf σ.kvs) …`, then `not_leaseOk_setupSt` with zK↦Lz (u) / aK↦Lu (v, anon, bad)); then barriers/grantPut/
  noAuth/foreign/absent, run, Main (plan below, unchanged). STOP at Main.wp_proof.
- **Pitfalls:** no literal modes in the package; `ihave %h := lem $$ H1 H2` keeps H1/H2 for pure results (wand-form
  helpers); `set`/`by_contra` are Mathlib (not available); deprecated `if_pos` warns: use `simp only [h, ↓reduceIte]`.

## Previous START HERE (S4, 2026-11-18, item 9: lean fb68edfec8 merged; Served done; Cell BLOCKED on check 6)


- Branch `auth-lease-s4`, worktree `/shared/etcd-grove-rs56`. Pin **6d365ee1a**: `--packages=/shared/tmp/manifest-6d3.json`
  everywhere, `.lake/package-overrides.json` = its copy, `PERENNIAL_DIR=/shared/perennial-6d365ee1a` for `etc/gen-init.py`.
- **Done:** 7b, D-k, the six driver helpers (all accepted by etcd-grove-03; questions.md). Merge of lean fb68edfec8
  `b33b59741c` (one conflict: `etc/goose.py`'s usage line, both sides' project names). **Served** (see the commit after it):
  new `etcdstart/ServedLeaseOn.lean` (`etcdLeaseServedOn`, `lease_served_on`: the four Lease registrations with auth on
  from `grpcLeaseUp`, `srvLeaseRd s E .revocable`, `grpcServerAt`, the pools); `ak_served_kv`'s post + `grpcServerAt`,
  `memberUpOn_served`'s post + `srvLeaseRd` (forms; callers auth/Run, auth3/run, authN/run take `-`).
  Build: `/shared/tmp/auth-lease-s4/served-build.log`.
- **BLOCKER (stopped here; questions.md, last entry):** check 6 is not provable: at auth on the KV writes' and the grants'
  updates are persistent (no `writeOnce`: it is `noRefusalAt`, auth off only), so a re-delivered grant may re-grant `Lu`
  after the revocation (`kvOpStep` only checks the current table) and a re-delivered `Put(a/lease, Lu)` re-attach `a/lease`.
  Options (A) thaw: grant freshness in the grant's write grant (`opGrantTN`); (B) drop check 6's reads. Awaiting decision.
- **Cell design (worked out, not written):** one invariant `∃ σ ps gs d, etcdKV γk σ ∗ monoListAuthOwn γ.ps 1 ps ∗
  monoListAuthOwn γ.gs 1 gs ∗ monoNatAuthOwn γ.d 1 d ∗ monoNatAuthOwn γ.v 1 σ.rev ∗ ⌜cellOk σ ps gs d⌝` (all updates are
  persistent at auth on, so no exclusive half can ride in one; every append is guarded by `ps`'s length, a re-fire keeps
  `leaseKeptIn`): `ps : List (w64 × Nat)` = `[(Lz, rz), (Lu, ru), (Lu, rt)]` appended by root's put / u's put / u's txn
  updates at their first effective firing; `gs` = ids our grant updates fired with (`id ≠ 0` ⇒ `id` in the table after the
  firing, whatever `leaseGrantOk`), keeps `Lz`/`Lu` live for the puts; `d` = revocation flag (u's `Revoke(Lu)`, `d = 1 →
  a/lease, a/txn absent`: this is what the blocker breaks); `γ.v` = σ.rev lower bounds (the lessor law's
  `leaseKeptIn σ (F.length-1)` needs `F.length - 1 ≤ σ.rev`). Refusals at G: `writeGrantG_granted` + `akAuthFixed_write`
  (`setupSt r` denies u `z/lease`, v `a/lease`); `Lu ≠ Lz` from u's put's G. Pure lemmas: `findKey_applyChanges_other`
  (txn/WinLemmas), `KVState.commit_at`.
- **Next after the decision:** Cell, barriers/grantPut/noAuth/foreign/absent, run, Main (plan below, unchanged).
- **Pitfalls:** no literal modes in the package (mode gate); `etc/gen-link.py --bbolt`/`--walfs` and
  `gen-specs-pkginit --check` differ in a worktree without `.lake/packages/perennial`: do not commit those. Monitor
  filters: anchor `^Terminated`. `questions.md` is untracked (gitignored).

## Previous START HERE (S4, 2026-11-18, item 9: driver plan)


- Branch `auth-lease-s4`, worktree `/shared/etcd-grove-rs56`. Pin **6d365ee1a**: `--packages=/shared/tmp/manifest-6d3.json`
  everywhere, `.lake/package-overrides.json` = its copy, `PERENNIAL_DIR=/shared/perennial-6d365ee1a` for `etc/gen-init.py`.
- **Done:** 7b (accepted, 2026-11-18; record in STATUS at the land stop). D-k `e7d56912d6` (accepted by etcd-grove-03,
  texts 1–3 and `server_cluster_alloc_on` mirrored; build of its 29 leaves green, tcb 892/4). Merge of lean 49bd7924e6
  `e180852712` (Hctx Part B, incomingof; no textual conflict); its full build: see the next commit/section.
- **Driver files so far** (`Proof|Spec/github_com/mit_pdos/etcd_grove/examples/etcd/authlease/`): `Defs`, `Dir`
  (authN's at the token and ports 16000/17000), `reqCtx`, `refused` (authkv's), `newUserClient` (authN's),
  `barrier` (authN's + the caller's read update `Q` and the floor `srvApi.kvLogLb E.γs log` with `□ Q (kvStateOf log
  lt)` from `rangeReplyOk`; `isServerReadM E.authOn`, no literal mode). State: see the commit that adds them.
- **Driver plan (what is left, in order):**
  1. `Served.lean`: authN's `serve_member`/`srvdAt`/`Wit` (authN `run.lean`) plus the lease registrations at the member
     (`etcd_lease_auth_served_on`, AuthnServedOn:499: LeaseGrant/LeaseRevoke at `etcdLeaseGrantSpecOn`/`…RevokeSpecOn`;
     `etcd_lease_read_served`, LeaseReadServed:800: TimeToLive/Leases at `etcdLeaseTTLSpecMd`/`…LeasesSpecMd`). Neither
     has a user yet. Their inputs: `grpcUpOn`'s `grpcLeaseUp` (`quotaLeaseServerAt`, `leaseServerAt`, `leaseRegs ⊆ regs`),
     `grpcServerAt`, the interceptors, `srvRevokeBuilt`, `srvRunPool` (as `kv_lease_served` builds them from the stocks,
     etcdstart `ServedLease.lean:386`, the auth-off model), `raftLeaseRead` from `memberUpOn … .revocable`'s `srvLeaseRd`,
     `isServerReqM/ReadM true`, `□ |==> idCred ρ.ids 1`. Likely an etcdstart lemma `ak_served_lease` beside authN's
     `ak_served_kv`/`ak_served_watch` (find them: `grep -rn "theorem ak_served" Proof`), passed to `Serve.spec`'s callback.
  2. `Cell.lean`: the driver's invariant over the client half `etcdKV γk σ` (Freeze §8.3): phases after the set-up
     (`a/x`, `z/lease`, `a/lease`, `a/txn` absent), after root's put (`leaseKeptIn σ rz Lz z/lease`), after u's puts (`…
     Lu a/lease`, `… Lu a/txn`), after u's revocation (`a/lease`, `a/txn` absent); `a/x` absent throughout. Every update
     handed out keeps it: the refused ones (u's `Put(a/x, Lz)`, its txn, `Revoke(Lz)`; v's `Revoke(Lu)`) are refuted at
     their grant (`grantedAt` → `leaseOk` at `setupSt` needs u/v to write `z/lease`/`a/lease`: false; `akAuthFixed_write`);
     re-delivered puts/grants keep the pairs; u's `Revoke(Lu)` moves to the last phase (its step deletes the attached keys).
     Open design point: the phase's ghost state (the updates fire at commit, so they must be able to advance it: a
     monotone phase in the invariant with persistent witnesses for the main thread, not a split ghost var).
  3. `barriers` (loop over the served members: `barrier` at each, `akAuthFixed` and the floor with `Q`), `grantPut`
     (`client_lease_grant_on` + `client_put_on` with `WithLease`, `hl` by `ρ.kv.lm = .revocable`), `noAuth` (checks 1:
     the token-less/invalid-token refusals: `leaseCheckT`/`authedFrom` at no token or `badToken`, D-h), `foreign`
     (checks 3–5: Revoke refuted by its update; TimeToLive/Leases by `lessor_keys_of_read` at barrier 2's floor + the
     per-index `leaseKeysVerdict_refused` of `Scratch/S4Probe.lean`), `absent` (root's `client_range_on` with a read update
     from the cell).
  4. `run`, then `Main` (authN's `Main.lean` with `allocNOnM … .revocable hrun hnx hap (ns := true)`, `memberBootOn … lm`,
     `StartMembersAuth … .revocable`). STOP at `Main.wp_proof` (present Draft §2's closed text vs what linking needs).
- **Pitfalls:** no literal modes in the package (mode gate: a new package line is a raise): `isServerReadM E.authOn` with
  `hon` from `E.authMode = .on γa`. `etc/gen-link.py --bbolt`/`--walfs` and `gen-specs-pkginit --check` differ in a
  worktree without `.lake/packages/perennial` (environmental): do not commit those regenerations. Monitor filters:
  anchor `^Terminated`. `questions.md` is untracked (gitignored): decisions live only in the worktree file.

## Previous START HERE (S4, 2026-11-18, item 9 D-k stop)


- Branch `auth-lease-s4`, worktree `/shared/etcd-grove-rs56`. Pin **6d365ee1a**: `--packages=/shared/tmp/manifest-6d3.json`
  everywhere, `.lake/package-overrides.json` = its copy, `PERENNIAL_DIR=/shared/perennial-6d365ee1a` for `etc/gen-init.py`.
- **Done:** 7b (accepted by etcd-grove-03, 2026-11-18; record in STATUS at the land stop). Item 9 step 1, **D-k**
  (`e7d56912d6`): `(ns : Bool := false)` appended after `hgps` in `srvClusterBoot_alloc`
  (NewServerAlloc), `srvClusterBootOn_alloc` (NewServerAllocOn) and its export `server_cluster_alloc_on` (server
  Results), after `hap` in `allocNOnM` (etcdstart AllocNOn); posts `⌜clusterNoSnap γ.cl ↔ ns = true⌝` (the off
  allocation's `⌜¬ clusterNoSnap γ.cl⌝` replaced: its `ns = false` instance); both allocations call
  `cluster_alloc_ns … ns (fun _ => hbne)`. Callers: Alloc/Alloc3/AllocN derive `¬ clusterNoSnap` from the iff,
  Alloc3On/auth MainAlloc skip the conjunct, `allocNOn` (statement unchanged) by a short Iris proof. Built: the
  29 importer leaves of the change (`/shared/tmp/auth-lease-s4/dk-build.log`, 9509 jobs); `tcb-report --check` 892/4 matches; etcdstart interface regenerated.
  Boot path at `ns = true`: `memberBootOn` has no `¬ clusterNoSnap` (only `memberBoot`, the auth-off bundle, does);
  `StartMember(s)Auth.spec` is generic in the cluster with `clusterNoSnap → 2^48 ≤ catchUp` (NoSnapCatchUp); the
  remaining `¬ clusterNoSnap` premises in the server are restart/snapshot-only (`srvMem_restartStorage`,
  `rnRestartOk`, `run_job_snapC`, `SnapApplyWalk`).
- **Next, in order:** (after etcd-grove-03's go on D-k) the driver: `Spec/…/authlease/{Main,run,barrier,barriers,
  grantPut,noAuth,foreign,absent,reqCtx,refused,newUserClient}.lean` and proofs, on authN's skeleton (`authN/run.lean`,
  `Main.lean`); `Main` allocates with `allocNOnM … .revocable … (ns := true)` so the lessor law's `clusterNoSnap`
  holds; lessor-side refusals via `lessor_keys_of_read` (LessorFollows) + the per-index form of
  `Scratch/S4Probe.lean`'s `leaseKeysVerdict_refused`; client calls via `client_put_on`/`client_txn_on`/
  `client_range_on`/`client_lease_grant_on`/`client_lease_revoke_on` (client/v3 `ResultsOn`) and
  `etcd_lease_read_auth_served_on`. STOP at `Main.wp_proof` (present the closed statement, Draft §2). Then item 10.
  Merge lean first: it moved to 49bd7924e6 after D-k was built (not merged yet).
- **Pitfalls:** `etc/gen-link.py --bbolt`/`--walfs` and `gen-specs-pkginit --check` differ in a worktree without
  `.lake/packages/perennial` (environmental): do not commit those regenerations. Monitor filters: "Terminated" matches
  k8s type names; anchor `^Terminated`. A Perennial pin bump rebuilds everything (~20k jobs, ~3.5 h in a slot).
  `questions.md` is untracked (gitignored): decisions live only in the worktree file.

## Previous START HERE (S4, 2026-11-18, item 7b COMPLETE: lean merged (pin 6d3), full build green; item 9 next)

(7b's section: see commit ad75410f86.)

## Previous START HERE (S4, 2026-11-17, item 7b: steps 7 and 8 DONE; the lean merge is NEXT and is a real integration)

- Branch `auth-lease-s4`, worktree `/shared/etcd-grove-rs56`, head = this commit. Pin still e9e
  (`--packages=/shared/tmp/manifest-e9e.json`); lean (5fb716b5eb, pin c6b) NOT merged.
- **Done:** step 7 `5f8c413b13`: `etcdserver/LessorFollows.lean`, `lessor_keys_of_read : lessor_keys_of_read_stmt`
  (frozen text verbatim; module builds; no `sorryAx`). Forms: questions.md, last entry. Step 8 (Draft §7 row 8), this
  commit: goose project `authlease` (`etc/goose.py`, translated with the e9e translator), `authlease/Base.lean`
  (package fact `True`, as authN's), `authlease/Init.lean` (`etc/gen-init.py`; `--check` clean). PkgTable map entry in
  gen-init: at linking (step 10), as authN's.
- **Next: merge lean (a trial merge was aborted; material in `/shared/tmp/auth-lease-s4/merge/`).** 37 files conflict,
  ~46 hunks, all from lean's trace-check stage (raft's `Cluster.trace`/`reTrace` gates) meeting S4's no-snapshot
  mode (D-k, L-r2/L-r5) in raft: list `conflicts.txt`, diff3 copies under `diff3/` (the 3 Spec files there are
  already resolved: `resolved/`), helper `hunks.py show|set|take FILE IDX`. Rule: keep both sides' premises and
  conjuncts, minus base's `γ.reNoSnap = false →` (S4 removed it; lean's side only carries it as context). Key
  integrations: (1) `InvNodeRule.storBnd`: lean sealed it and gated it on the trace (`match Cluster.trace γ`); S4 added
  `⌜clusterNoSnap γ → k ≤ 1⌝`: put S4's conjunct in the `none` arm; `storBnd_intro_untraced` then needs `clusterNoSnap
  γ → k ≤ 1` (or restate S4's `storBnd_off`/`storBnd_le_one` over it, no twins); `storBnd_cap` by `split`.
  (2) `cluster_alloc_ns`/`cluster_alloc`/`cluster_alloc_traced`: both posts (`(clusterNoSnap γ ↔ ns = true)` and
  `⌜Cluster.trace γ = none⌝`), callers' patterns `%Hns, %HtrC` (NewServerAlloc(On), kv/kvdurable/kvreconf Alloc,
  StartCluster). (3) setupNode/Bootstrap/RestartNode/StartNode proofs and `InvApiBoot`, `InvApiDecAlloc`,
  `InvNodeRun`, `InvRawnode`, `RawNode__Step`, `raft__maybeSend{Append,Snapshot}`, `node__run`: lean's proofs may use
  the removed `reNoSnap = false` (check `grep reNoSnap`). Then `etc/gen-raft-tla.py` (RaftTla copies of raft proofs),
  regenerate `Link`s/interfaces as lean's CLAUDE.md says, `etc/goose.py --perennial /shared/perennial-c6b39d4f8`
  (c6b is a goose change: regenerates translations incl. authlease), `.lake/package-overrides.json` = c6b manifest,
  everything at `--packages=/shared/tmp/manifest-c6b.json` (or 6d3 if that bump landed first). Then the full build
  (`/shared/tmp/build-slot.sh`, `LEAN_NUM_THREADS=4`, retry on cap kills), `etc/tcb-report.py --check`,
  `etc/gen-interface.py` (incl. Spec `uberApplier__Apply`/`uberApplier__dispatch`; the new `LessorFollows` is not in an
  API list), and report 7b's completion.
- **Pitfalls:** in a proof-mode goal `cases h : E.lg` rewrites the Iris context (use `by_cases`). A lemma of a section
  with a package's `[Assumptions]` carries that instance even unused (the law needs mvcc's). `etc/gen-init.py` needs
  the package's `IsPkgInit` instance file first (`Base.lean`). `questions.md` is git-ignored (local). Earlier pitfalls
  below.

## Previous START HERE (S4, 2026-11-17, item 7b F4: wiring COMPLETE, leaves build green; step 7 next)

- Branch `auth-lease-s4`, worktree `/shared/etcd-grove-rs56`, head = this commit. Everything compiles: the ONE leaves
  build from `00b09c1360` (165 targets, `/shared/tmp/auth-lease-s4/7b-f4-leaves2.txt`, log `7b-f4-leaves.log`) exit 0,
  no `sorry`. Pin still e9e (`--packages=/shared/tmp/manifest-e9e.json`); lean not merged yet.
- **Decided:** option (A) forms ACCEPTED by etcd-grove-03; NewServer allocation forms (questions.md, last entry: form
  decided by the agent, for the checkpoint review).
- **Done:** `af275c78fa` `kvEntryOn_extends` is ONE lemma in `KVAuthModel` (server TEMP copy and `v3rpc.ClientModel`'s
  removed). `b769c66663` NewServer and NewServerR: after `writer_facts` (`□ Nx log`), `wSt` split into `wStQ ¼` +
  the tie's quarter, `tie_alloc` (`Lt = log`, `Fr := clusterNoSnap … → decide (lm ≠ none) = false`, NewLessor's
  `lessorWinTie γl []` = `HlWt`), `tie_free` at `lg = false` (`∃ wb, ⌜lg = false → wb = none⌝ ∗ leaseOwnW … wb ∗
  winTok γwt wb`); literals `Wt := srvApi.winTok γwt, stq := ¼`; `hγs` moved below; `Haus` by `envAus_tie`;
  `winTieRes` in `srvKVInvs(On)`; the start row `srvApplyKVW` at `wb`. NewServerR gets `#Hlrdinv` from `lessorInv`
  as NewServer. Client/example callers needed no change (their patterns end in `-`).
- **Next, in order:** (1) step 7, the law (`lessor_keys_of_read_stmt`, frozen text
  `notes/auth-lease-s4-frozen.lean.txt` §5, not yet in the tree; new file, e.g. `etcdserver/LessorFollows.lean`):
  case `E.lg = true` (`¬ Fr`): `tie_obs` (`m := j0`, `F <+: L0`), per `i ≥ j0` `tie_law` (`La`, `Lt` with `□ Nx`),
  then S5 (from `kvInv`/`kvInvOn`'s `ghostVar γk.st ½ (kvStateOf (model L) …)` agreeing with `etcdKV`, and `srvRLogLb A`
  ⊑ the invariant's `L`: `La.length - 1 ≤ σ.rev`, items of `σ.at (La.length - 1)` = `itemsOfLog La`; lemmas to reuse:
  `KVModelDefs.kvStateOf_at(_kvs)`, `v3rpc.ClientModel.etcdState_of_nx`/`srvLog_of_nx`); case `E.lg = false` (lm =
  none): the lm-none model lemma (no committed model log attaches a lease to a key at `lm = none`), then
  `leaseKeptIn` is false (STOP if false or needs trusted text). The off mode (`kvInv`, `kvStQ`) needs the same
  argument or a contradiction (frozen text, "Mode-generic"). `lessorLawMask` gains `lessorRdN` and `winTieN` (a form
  the frozen text allows). (2) step 8; (3) the c6b merge (merge lean, regenerate generated files,
  `.lake/package-overrides.json` → `/shared/tmp/manifest-c6b.json`, `--packages=/shared/tmp/manifest-c6b.json`); full
  build (retry on cap kills); `tcb-report --check`; gen-interface (incl. Spec `uberApplier__Apply`,
  `uberApplier__dispatch`).
- **Pitfalls (this session):** NewServer's proof hung 40 min in lean-check on `iExactEq H; rfl` where `iexact H`
  works (the goal matched up to abbrevs): prefer `iexact`; to find a hang, insert a temporary `done -- TEMPSTOP` and
  bisect. `uberOwn` at `{E with win := wb}` vs `E`: `iExactEq Huo; simp only […]; rfl`. `γt` is already a name in
  NewServer(R) (`mono_nat` at l.1231): the tie's names are `γwt`/`HwTie`. `Htie` is `authHistTie`'s. `pkill -f` on a
  lean-check command line kills your own shell. `etc/importers.py --leaves` lists `Scratch.*`/`notes.*` modules:
  filter them before `lake build`.

## Previous START HERE (S4, 2026-11-17, item 7b F4 (A): apply layer + applyEntryNormal DONE; NewServer(R) next)

- Branch `auth-lease-s4`, worktree `/shared/etcd-grove-rs56`, head = this commit (WIP: `NewServer`, `NewServerR` and
  importers of the changed server rows still do not compile). Base of the coming leaves build: `00b09c1360`.
- **Decided (questions.md, last three entries):** option (A) (etcd-grove-03); the agent's forms "Item 7b F4 (A), forms".
- **Done:** `89951bb50c` apply layer: plain path `E.lg = true → v3 = true → winTgt …` (Spec `uberApplier__Apply`,
  `uberApplier__dispatch`: interfaces to regenerate; `Apply.specRec`); latest path `winTgtL` (DispatchKVL) /
  `(∃ oc, X oc ∧ oc ≠ .rejected .auth) → winTgt` in the methods' `*PreW`; existence lemmas `pass_exists`,
  `backendStep_exists_*` (AuthApplyLatest; the txn read-only fact from `txn.srvOps_gets_nil`, so client
  `srvRunTxn_ro_nil` was NOT moved: no copy exists). All apply files lean-checked `--fast -a`.
  `52fa94a5b5` `EtcdServer__applyEntryNormal` compiles (`--fast -a`, 0 errors): defeq corollaries `Apply_specRec_win`,
  `Apply_kvSpecL_win`, `adminEntryOn_win`, `srvUberOn_kv_win`, `srvUberOn_adm_win` (call at `{E with win := wn}`,
  other resources at `E`); `srvApplyKVW_push` (window of the entry, `Lt` the model log after it), `winTgt_of_log`,
  `backendStep_keep`, `kvOutL_of_pass`; `applyKV_writer`/`applyKV_kvOwnPre` at the window.
- **Next, in order:** (1) MOVE `kvEntryOn_extends'` (TEMP copy at the top of applyEntryNormal) and
  `v3rpc/ClientModel.kvEntryOn_extends` to ONE lemma in `KVAuthModel.lean` (next to `kvEntryOn`), both callers use it
  (no twin). (2) NewServer/NewServerR allocation: NewLessor's output pattern drops `lessorWinTie γl []` (the `-` after
  `Hlown`, NewServer l.737): keep it; after `bootStore_holds` (`Hw0 : wSt γs log c`, l.919) split `wStQ`'s st part
  (`ghostVar_split_half E₀.γs.st (1:Qp).half`) into `wStQ ¼` (kvOwn, `stq := ¼`) and a bare quarter for
  `srvApi.tie_alloc` (with `Hlrdinv`, `HlWt`, `Hlown` after `hNew` l.891, `□ kvNx ρ.rd on log` from `Hrlb0`, `Lt = log`,
  `Fr := clusterNoSnap ρ.rd.raft.raft.cl → E.lg = false`); at `ρ.rd.kv.lg = false` `tie_free` right after (Fr holds).
  AEnv literals (20 in NewServer, 18 in NewServerR): append `Wt := srvApi.winTok γt, stq := (1 : Qp).half.half` (sed on
  `γlt := γlt }`); `Haus` (l.2478) by `srvApi.envAus_tie`; `srvKVInvs` (l.2204) gains `winTieRes`; the final
  `bootKVOf` row (l.2620-2670) is `srvApplyKVW` at the window (leasesLive with `Hlown` at `wn`, `E.Wt wn` = the token).
  Current NewServer errors (lean-check `--fast -a`, 4, all expected): l.2100 `srvEnvOk`'s `(E.win = none ∧ E.stq = ¼)`;
  l.2208/2216 `srvKVInvs`' new `winTieRes` conjunct; l.2622 the `bootKVOf` row (now `srvApplyKVW`).
  (3) Remaining callers (examples, client: `etc/importers.py --uses srvKVInvs --uses srvKVInvsOn --uses srvApplyKVW
  --files Proof/go_etcd_io/etcd/server/v3/etcdserver/InvApplier.lean`). (4) ONE leaves build from `00b09c1360`
  (`/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-e9e.json build $(etc/importers.py --leaves --git
  00b09c1360)`); step 7 (law, incl. the lm = none lemma), step 8; the c6b merge; full build; tcb-report --check;
  gen-interface (the two Spec files above change).
- **Pitfalls:** `{E with win := wn}`-resources: use the `*_win` corollaries (defeq ascription) instead of converting
  hypotheses. `simp only [↓reduceIte]` turns a premise `v3 = true →` into `True →`: write `fun h _ => …`. In python
  edits, an 8-space anchor also matches 10-space lines: anchor at line start (`(?m)^`). Earlier pitfalls below.

## Previous START HERE (S4, 2026-11-17, item 7b F4: STOPPED at a refutation in applyEntryNormal; waiting for etcd-grove-03)

- Branch `auth-lease-s4`, worktree `/shared/etcd-grove-rs56`, head = this commit (WIP: `EtcdServer__applyEntryNormal`,
  `NewServer`, `NewServerR` and importers still do not compile). Base of the coming leaves build: `00b09c1360`.
- **Decided (questions.md):** the F4 wiring forms ACCEPTED; `Fr := (clusterNoSnap … → E.lg = false)` kept, NewServer
  frees the window after `tie_alloc` at `E.lg = false`, step 7 proves the lm-none model lemma (STOP if false/trusted).
- **Done this session:** `ApplyCmpArm.backendStep_kvEntryM` (lean-checked `--fast`): in the auth-off arm every backend
  outcome's log is `kvEntry …` (the off `v3 = true` arm's `winTgt` with `Lt := kvEntry …`, `□ Nx` by `kvAppliedL_nx'`).
- **OPEN (questions.md, last entry):** the window premise `winTgt` is unprovable in the auth-on KV/revocation arms when
  the auth layer refuses, and in the replay (`v3 = false`) arms. Recommended fix (A): gate the premise by `v3` (plain
  path) and by the verdict (latest path). Do nothing on applyEntryNormal's arms until decided.
- **Next once decided:** per (A): apply specs + existence lemma; then the arms (off `v3`: `applyKV_push` with
  `Lt := kvEntry c0 x.chain (kvLeases A) x.log m` before `hA`, winTgt from `backendStep_kvEntryM` with `HkA.2.symm`,
  `Hnl`, `kvTableOf_ne0`; repack `srvApplyKVW`); then the previous START HERE's (2), (3), (6)-(8).
- **Pitfalls:** as in the previous START HERE.

## Previous START HERE (S4, 2026-11-17, item 7b F4: server wiring IN PROGRESS, WIP commits; applyEntryNormal and NewServer(R) left)

- Branch `auth-lease-s4`, worktree `/shared/etcd-grove-rs56`, head = this commit (WIP: `EtcdServer__applyEntryNormal`,
  `NewServer`, `NewServerR` and what imports them do not compile). Base of the coming leaves build: `00b09c1360`.
  Decisions: `questions.md`, last entry (forms, and OPEN: the free-marker fact `Fr` at `E.lg = false`).
- **Done (lean-check `--fast -a` clean on every server file below):** `srvKVInvs`/`srvKVInvsOn`/`srvKVInvsC` last
  conjunct `srvApi.winTieRes E (clusterNoSnap γr.raft.raft.cl → E.lg = false)`; `srvEnvOk` 3rd conjunct `(E.win =
  none ∧ E.stq = ¼)`; `srvApplyKVW E ua x := ∃ w, ⌜E.lg = false → w = none⌝ ∗ applyKV {E with win := w} ua x` in every
  applier row, lemmas `srvApplyKVW_open` (pieces at `E`, window part in the closing wand: use it, never unfold
  inside long proofs), `_of_none`, `_crOwn`, `_writer`, `_authOn`, `_hookRO`; `srvKVInvsM_winTie`. Snapshot path done:
  `applyAll.specSnapM`/`applySnapshot.specSnapM`/`applySnapshot_walk` take `¬ clusterNoSnap γr.raft.raft.cl` (from
  `run_job_snapC`'s `hns`); the walk frees the window (`applyKV_free`), restores at ¼ (`restorePreA_of_au` +
  `au_restore_tie`), `snapWalkPost`/`snap_applyKV` carry `wStQ E.γs E.stq` and `E.Wt none`. Checked: InvApplier,
  KVStore{Api,Laws}, Inv{Read,Start,Build,ApRes,RunRes}, KVApply(On), ServerOn(Defs), UberOn, SnapRO, StartOn,
  ApplyEntryOn, AppliedOn, ApplyKVCore, ApplyNormalOn, ApplyCmpArm, SnapSendBranch, SnapRecv{Facts,On},
  MergedImageOn, RunOn, KVRead, ReadOn, AuthComp(Rows), CompactEnv, ModeSpecs, StopImage, StopShutdown, SnapApply*
  (Defs, AuthM, Walk, Names, IsServer, Opts, OptsLemmas, KV, Post), EtcdServer__{Compact, applySnapshot, apply,
  applyAll, run, start, snapshot}, ApplyAllSnap.
- **Next, in order:** (1) `EtcdServer__applyEntryNormal` (arms: `grep -n winTgt_none`; `HKV` is now `srvApplyKVW`,
  open it with `srvApplyKVW_open` where only the backend pieces are used). Admin arms (`hAd`): call `adminEntryOn` at
  `{E with win := w}` (any `E`), no push. Each `hA` arm: unfold `srvApplyKVW` (`⟨%w0, %Hw0, HKV⟩`); at `E.lg = false`
  (`w0 = none` by `Hw0`) convert to `applyKV E` (`{E with win := none} = E`: `rw [← HEo.2.2.1.1]`) and keep the
  call as is; at `E.lg = true`: `srvApi.applyKV_push hPers hReach E _ HEo.2.2.1.2 w0 ua x Lt hlt` with the tie from
  `Hkvi` (last conjunct), `□ E.Nx Lt` (`Lt` the committed model log after the entry, from the raft lb of `A ++ [m]`;
  `kvNxOff`/`kvNxOn` unfold), then call `hA` at `E' := {E with win := some (s, itemsOfLog Lt)}` (convert each
  `E`-resource in and out by `iExactEq H; rfl`), the premise `winTgt` via `KVOutcomeOn.backendLog_of_step` (KV kinds)
  / `revokeLog_eq_backendLog` (revoke) / `Lt = x.log` (kinds that leave the log); repack `srvApplyKVW` with the new
  window (`⌜E.lg = false → …⌝` vacuous). The `v3 = false` replay arms also call `hA`: same push. Lead for `Lt` in the off
  arm: `kv_applied_step` (l.554) already runs before `Apply` and gives `kvAppliedL … (A ++ [m]) (kvEntry c0 x.chain
  (kvLeases A) x.log m)`, so `Lt := kvEntry …` with `□ E.Nx Lt` by `kvAppliedL_nx'`; `winTgt` then needs, for every
  backend outcome at the live set, `oc.logAfter x.log = kvEntry …` (the per-outcome form of the post-`Apply` equality
  the arm proves from `Hstep`); the on arms the same with `kv_applied_step_on`/`kvAppliedLOn_nx`. (2) NewServer /
  NewServerR: previous START HERE's step (3) (split `bootStore.law`'s `wSt` into `wStQ ¼` ×2, `tie_alloc` after
  `NewLessor` with `Lt = log`, `Wt := winTok γt`, `stq := ¼` in the `AEnv` literals (sed on `γlt := γlt }`), `Haus`
  by `envAus_tie`, the tie into `srvKVInvs`; at `E.lg = false`, `tie_free` right after (Fr from `E.lg = false`), the
  start rows' `srvApplyKVW` at the window). (3) remaining callers (examples, client: `importers.py --uses srvKVInvs
  --uses srvKVInvsOn --uses srvApplyKVW … InvApplier.lean`; their patterns mostly end in `-`). Then (6)-(8) of the
  previous START HERE (leaves build, step 7 with the lm-none lemma if `Fr` stays, step 8, c6b merge).
- **Pitfalls:** `rw [hX]` on the goal rewrites literal `{E with win := w}` pieces in the Iris context (fixed with
  `srvApplyKVW_open`). An `icases` of `srvKVInvsOn` whose last `%X` used to take two pure conjuncts now needs
  `%X0, %X1, -` (SnapRecvOn, ApplyAllSnap, MergedImageOn). `pkill -f rs56-chk.sh` kills your own shell.
  `/shared/tmp/rs56-chk.sh FILE [N]` checks one file and shows a failing import's errors.

## Previous START HERE (S4, 2026-11-17, item 7b F4: step-7 Iris lemmas + apply-thread tie lemmas done; server wiring next)

- Branch `auth-lease-s4`, worktree `/shared/etcd-grove-rs56`, head = this commit. Not built since `00b09c1360`
  (lean-check `--fast` only). Decisions: `questions.md`, last two entries (the tie ACCEPTED by etcd-grove-03; the agent's
  forms "F4 step-7 lemmas and WinTieApply", for review).
- **Done:** `49aab6ebc5`/`add5127999` the tie (`WinTie.lean`); `0d7362641a` `tie_obs` (open `kvsN`+`winTieN`: lbs of the
  records/anchors, `lessorLb j0`, last anchor at the store's log `L0 ⊒ F`; `¬Fr` excludes a free window) and `tie_law`
  (open `winTieN`+`lessorRdN`: for `i ≥ j0`, committed `La ⊒ L0`, `Lt`, `σl` holds every item both put on `id`, `id`
  live); `a5a5ca5595` `WinTieApply.lean` (`winTieRes E Fr` = `∃ γt, ⌜E.Wt = winTok γt⌝ ∗ winTieInv … ∗ lessorRdInv`;
  `envAus_tie` (envAus from the store invariant + tie at `E.stq = ¼`); `kvOwn_push`/`applyKV_push` (entry window, target
  `itemsOfLog Lt`); `kvOwn_free`/`applyKV_free`; `uberOwn_win`/`cmpOwn_win` by `.rfl`) and `KVStoreLaws.restorePreA_of_au`
  (`restoreArgs_holds` now a call of it: use it with `au_restore_tie` on the snapshot path).
- **Next, in order (one change; nothing compiles in between, so lean-check file by file and commit at the end):**
  (1) `InvApplier`: import `WinTieApply`; `srvKVInvs` and `KVApplyOn.srvKVInvsOn` gain a LAST conjunct
  `srvApi.winTieRes E (¬ clusterNoSnap γr.raft.raft.cl)`; `srvEnvOk`'s third conjunct `(E.win = none ∧ E.stq = ¼)`.
  Patterns that break (end in `%X` at the old last position): StopImage:156, InvApplier:729/742, SnapSendBranch:847,
  KVApply:282, applyEntryNormal:375/548, MergedImageOn:80, SnapRecvOn:598, ApplyAllSnap:245 (check which predicate),
  and the `srvKVInvsOn` ones (`grep -A3 "iunfold srvKVInvsOn at"`); `srvEnvOk` users: SnapApplyWalk:641
  (`.2.2.1.2.2` → `.2.2.1.2`), SnapApplyKV:52/102/116 (`hEw`; `snapE_Wt`), `HEo.2.2.1.1` (win) stays.
  (2) `srvApplyKV`/`srvApplyKVOn`: `apply.applyKV E ua x` → `∃ w, apply.applyKV {E with win := w} ua x`.
  (3) NewServer (~l.760 `#Hlrdinv`, ~l.2476 `Haus`) / NewServerR (~l.2165): split `bootStore.law`'s `wSt` into `wStQ ¼`
  ×2; `tie_alloc` after `NewLessor` (`Lt = log` = boot log, `T = itemsOfLog log`); `Wt := winTok γt`, `stq := ¼` in
  the `AEnv` literals (sed on `γlt := γlt }`); `Haus` by `envAus_tie`; build `winTieRes` for srvKVInvs.
  (4) `applyEntryNormal` (6 arms, `grep -n winTgt_none`): `applyKV_push` before `Apply` with `Lt` = the model log after
  the entry (`backendLog lt rq log`; `KVOutcomeOn.backendLog_of_step`, `revokeLog_eq_backendLog` give `winTgt` for
  KV/revoke arms; other kinds leave the log), `□ E.Nx Lt` from the raft witness of `A ++ [m]`.
  (5) Snapshot path (SnapApplyWalk ~l.654): `applyKV_free` (Fr from the toApply payload's `¬ clusterNoSnap`,
  `InvRaftNode.lean:1951`), then `restorePreA_of_au` with `au_restore_tie` in place of `restoreArgs_holds`.
  (6) ONE leaves build from `00b09c1360` (kernel-checks `tie_pick`, `tie_obs`, `tie_law`, the `--fast` files).
  (7) The law (`LessorFollows.lean`, frozen text in `notes/auth-lease-s4-frozen.lean.txt` §5; `lessorLawMask` gains
  `lessorRdN` and `winTieN`): `m := j0` from `tie_obs`; per `i`, `tie_law`; S5 (not yet found as a lemma): from `kvInv`
  (holds `etcdKV`'s other half) and `□ E.Nx L` (`srvRLogLb A`, `L = kvModelM … A`): `L.length - 1 ≤ σ.rev` and the
  items of `σ.at (L.length - 1)` are `itemsOfLog L`; then `leaseKeptIn` at `La`'s and `Lt`'s revisions.
  (8) Step 8, the c6b merge, full build, tcb-report, gen-interface (see the task brief).
- **Pitfalls:** `{E with win := w}`'s pieces do not `iframe` into `{E with win := w'}` goals: `iExactEq H; rfl` (see
  `WinTieApply`). Don't `rw` an Iris hypothesis (`rw … at H` sees only Lean hyps). `cases h : f x` in a proof-mode goal
  rewrites the Iris context: use `rcases Option.eq_none_or_eq_some (f x)`. In `iinv` patterns, `mvccState γ σ` is not
  timeless without `Hp`: bind it without `>`. Earlier pitfalls below.

## Previous START HERE (S4, 2026-11-17, item 7b F4: the tie proved standalone; server wiring next)

- Branch `auth-lease-s4`, worktree `/shared/etcd-grove-rs56`, head = this commit. Not built since `00b09c1360`
  (lean-check only). Decisions: `questions.md`, last entry (K1 forms ACCEPTED; namespace option (b): the tie in its own
  namespace `winTieN`, outside `kvsN`/`mvccN`/`wsN`; `kvStoreInv`, `bootStore.law`, `kvPeek.law`, `srvApi.kvsN` untouched).
- **Done:** `49aab6ebc5` + this commit: `etcdserver/WinTie.lean` (imported by nothing yet; lean-checked, kernel-checked
  except `tie_pick`, `--fast`). Contents: names `WTNames` (`w` token, `t` window records, `a` anchors), `winTieInv Nx Fr
  γl γs γt` (body: `lessorWinTie ws`, `ghostVar γt.w ½ (lastWin ws)`, `ghostVar γs.st ¼ (log,p)`, mono-lists `tw`
  (start, target, model log `Lt`) and `anc` (window idx, lessor idx, store log), persistent facts, pure `tieOk`);
  `winTok γt w` (the apply thread's half, = the server's `E.Wt`); laws: `au_end_tie` (end builder at `wStQ ¼`, records
  the commit's anchor from `winWit`), `au_restore_tie` (restore at `¼`, token at `none`), `tie_push` (per-entry window,
  needs `□Nx log`, `□Nx Lt`, `log <+: Lt`, `T = itemsOfLog Lt`, owner items `= itemsOfLog log`), `tie_free` (free marker,
  needs `Fr`), `tie_alloc` (after `NewLessor`: first window); pure `tie_pick` (step 7's core: an index `i ≥ j0` of the
  law's observation anchor lies in a free window or a window with an anchor `La ⊒ L0 ⊒ F` before `i`, stable to `i`).
- **Next, in order:** (1) step-7 Iris lemmas in WinTie: `tie_obs` (open `kvsN`+`winTieN`: `F <+: log`; the last anchor
  `(tw0.length-1, j0, L0)` with `L0 = log`, `m := j0`, `lessorLb` by `lessorAt_lb`; or `Fr` if the window is free) and
  `tie_law` (open `winTieN`+`lessorRdN`: agree `lessorWinTie` ¼ with `lessorWinBody` ½, `lessorAt` lookups via
  `lessorPinR_agree`+`mono_list_auth_idx_lookup`, then `tie_pick`). (2) Server wiring: `srvKVInvs`/`srvKVInvsOn` gain
  `∃ γt, ⌜E.Wt = winTok γt⌝ ∗ winTieInv E.Nx (¬ clusterNoSnap γr.raft.raft.cl) (mvccLeases E.γ) E.γs γt` (last conjunct;
  fix the patterns that enumerate all conjuncts); `srvEnvOk`'s third conjunct `E.stq = ¼` (and drop `E.Wt = True`);
  NewServer/NewServerR: split `bootStore`'s `wSt` (½) into ¼+¼, `tie_alloc` after `NewLessor` (Lt = boot log),
  `Wt := winTok γt`, `stq := ¼` in the `AEnv` literals (sed on `γlt := γlt }`), `envAus` from the generalized
  `au_begin/au_wread/au_compact/writer_facts/writer_floor` at `{q}` + `au_end_tie`; snapshot path: `tie_free` (Fr from
  the toApply payload's `¬ clusterNoSnap γ.node.cl`, `InvRaftNode.lean:1951`) then `au_restore_tie` (generalize
  `restoreArgs_holds`' proof over the AU, no twin); `srvApplyKV(On)` at `∃ w`; `applyEntryNormal`: `tie_push` with `Lt` =
  the model after the entry. (3) ONE leaves build from `00b09c1360`; step 7 (law: `tie_obs`/`tie_law` + S5 from
  `kvNx`/`etcdKV`), step 8, the c6b merge (see the task brief).
- **Pitfalls:** in WinTie, `lease.win_push`'s `x.map …` does not unify with `some (s,T)` in `iexact`/`iframe`: use the
  wrappers `win_push_some`/`win_push_none`. Projections of literal tuples (`(n,j,L).2.2`) need `simp only` before
  `iframe`/`omega` (also `at h`). `iinv` on `winTieInv` needs `iunfold winTieInv` and `iunfold winTieBody` first. A
  lean-check that reopens WinTie rebuilds its imports (~3 min).

## Previous START HERE (S4, 2026-11-17, item 7b: applierSpecW and K1's apply layer done; F4 next)

- Branch `auth-lease-s4`, worktree `/shared/etcd-grove-rs56`, head = this commit. Not built since `00b09c1360`
  (lean-check `--fast -a` only). Decisions: `questions.md`, last three entries (K1 + applierSpecW APPROVED by
  etcd-grove-03; the agent's forms "applierSpecW and K1", for review).
- **Done:** `96aaf93c0c` applierSpecW (`uberIs`/`baseAuth`/`uberOwn` hold `□ ∀ w, applierSpec {E with win := w}`).
  This commit, K1's apply layer: `srvApi.wStQ γs q` (`wSt` = `wStQ ½`, abbrev), share-generic read-only builders
  (implicit `{q}`), `AEnv.stq : Qp := ½`, `envAus`/`kvOwn(At)`/`mPre*` at `wStQ E.γs E.stq`; server transitional:
  `srvEnvOk`'s third conjunct `(E.win = none ∧ E.Wt = True ∧ E.stq = ½)`. lean-check clean on every file that
  mentions the changed names (list `/shared/tmp/rs56-l3.txt`, plus their imports through Lake).
- **Next, in order:** F4 proper (design: questions.md "Item 7b F4 decision" + "the tie cannot see the store's log"):
  (1) namespace split: store invariant at `kvsN .@ "st"` (`kvStoreInvG`, `kvsN_mvccN` uses: KVStoreCore 22,
  KVStoreApi 6, etcdstart WatchSrv/Served 4, NewServerRFacts 1), tie at `kvsN .@ "win"`; (2) the tie
  (new file, e.g. `etcdserver/WinTie.lean`): names `γw` (ghost var of the current window), `γe` (mono-list of events
  push/commit/obs), invariant `lessorWinTie γl ws ∗ ghostVar γw ½ (lastWin ws) ∗ ghostVar γs.st ¼ (log, p) ∗
  monoListAuthOwn γe 1 evs ∗ facts`; `E.Wt w := ghostVar γw ½ w`; (3) server end builder at `wStQ E.γs ¼` (both
  steps of `au_end` open the tie: the notify step moves the tie's ¼ with the pending, the commit step records the
  commit event) and restore builder (records a free marker), replacing the `kvAusG` ones in NewServer(R)/
  SnapApplyOpts; (4) `srvEnvOk`: `E.stq = ¼`, `E.Wt = ghostVar γw ½` (replace the transitional conjunct), split
  `bootStore.law`'s `wSt` (½) into `wStQ ¼` ×2 in NewServer/NewServerR; (5) `srvApplyKV(On)` at `∃ w`, per-entry
  `win_push` in `applyEntryNormal`, first window in NewServer after `NewLessor`, snapshot `win_push none`;
  (6) ONE leaves build from `00b09c1360`; step 7 (law), step 8, c6b merge (see the task brief).
- **Open point before F4 (1):** `kvStoreInv` (KVStoreApi, the conclusion of `bootStore.law`) is defined with `inv kvsN`
  separately from `kvStoreInvG`; moving the store invariant to `kvsN .@ "st"` changes what `bootStore.law` asserts
  (namespace only; text unchanged), and `etcdstart/Served.lean:112` exports `srvApi.kvsN` as the store's namespace,
  `kvPeek.law` opens `kvsN`. Approved earlier as "text unchanged"; the K1 decision says "texts and meaning". If that
  counts, the alternative is the tie at its own namespace outside `kvsN` (disjoint from `mvccN`, `kvsN`, `wsN`), with
  the law's mask extended by it. Ask etcd-grove-03 which, before coding (1).
- **Pitfalls:** `wStQ` is reducible: `icases` destructs it directly; `iframe` into a `wStQ` goal needs `iunfold wStQ`
  first. To turn `wStQ E.γs E.stq` into `wSt` use `rw [hstq]` inside a subgoal that closes (a goal-level `rw [← hstq]`
  would rewrite every `½`). `{E with win := w}.authOn` does not unify with `E.authOn` in the proof mode:
  `apply.applierSpec_congr` with explicit `c`/`c'`. The loop script `/shared/tmp/rs56-loop.sh LIST stop` stops at the
  first file with an error (fixed: it matched "0 errors").

## Previous START HERE (S4, 2026-11-17, item 7b: F4 (A) decided; STOPPED before coding on the tie/store coupling)

- Branch `auth-lease-s4`, worktree `/shared/etcd-grove-rs56`, head = this commit (no Lean change since `ac1084fa33`,
  which compiles at the defaults; not built since `00b09c1360`, lean-check `--fast` only).
- **Decided (questions.md, "Item 7b F4 decision"):** SnapApplyKV fix accepted; F4 option (A): window kept open between
  entries, loop state `∃ w, applyKV {E with win := w} …`, first window in NewServer after NewLessor, frees only in the
  snapshot branch; tie design (ghost var γw of the current window, `E.Wt w := ghostVar γw ½ w`; mono-list of
  push/commit/obs events at `kvsN .@ "win"`, store invariant moved to `kvsN .@ "st"`).
- **Stop (questions.md, "Item 7b F4: the tie cannot see the store's log"):** step 7's case "window current at the law's
  obs, `F` beyond the push's log" needs the tie to know the store's exact log; no ghost ties the two invariants.
  Recommended K1: the tie owns ¼ of `γs.st` (split from the `wSt` bootStore gives), `AEnv.stq : Qp := ½`, `kvOwn`/
  `envAus` at `wStQ E.γs E.stq`, KVStoreCore builders generalized over the share, server end/restore builders that open
  the tie inside the commit AU. K2 (private `st` name) and K3 (drop the law) in the entry.
- **Next after the decision, in order:** (1) form, any option: `applierSpecW E c a := □ ∀ w, applierSpec {E with win :=
  w} c a` held by `uberIs`/`baseAuth`/`uberOwn` (sites: `grep -rn "unfold apply.uberOwn\|unfold apply.uberIs\|unfold
  apply.baseAuth"`, 28; producers: `NewUberApplier` from `Hbase` at every window, the restoreAlarms chain); lemma
  `applierSpecW_at`; holders then move between windows by `rfl` (`backendOptsOk`, `cmpOwn` do not read `win`).
  (2) the coupling per the decision; (3) F4 proper (namespace split: `kvsN` sites in KVStoreCore 22, KVStoreApi 6,
  etcdstart WatchSrv/Served 4, NewServerRFacts 1; tie definition and laws; `srvApplyKV(On)` at `∃ w`; per-entry
  `win_push` in `applyEntryNormal`; NewServer/NewServerR: tie allocation, first window, `Wt :=` in the 20 `AEnv`
  literals (sed `γlt := γlt }`); snapshot `win_push none`); (4) ONE leaves build from `00b09c1360`; steps 7, 8; c6b merge.
- **Pitfalls:** fresh lean-check of a server file rebuilds its imports through Lake (minutes; examples > 25 min).
  `win_push` returns `s` = the history's last index (no new snapshot). Earlier pitfalls below.

## Previous START HERE (S4, 2026-11-17, item 7b: compiling again at the defaults; STOPPED before F4 on the free-range gap)

- Branch `auth-lease-s4`, worktree `/shared/etcd-grove-rs56`, head = this commit. Decisions: `questions.md` (last three
  entries: etcd-grove-03's review of forms 1-6 + the SnapApplyKV fix; the F4 STOP "the free range between entries").
  Not built since `00b09c1360` (lean-check `--fast` only).
- **Done (this commit):** `srvEnvOk`'s third conjunct is `(E.win = none ∧ E.Wt = fun _ => True)` (etcd-grove-03's fix,
  one conjunct so destructurings keep their arity; F4 replaces the `Wt` half by the tie token); `snap_applyKV` takes it
  as a premise (`SnapApplyPost` reads it off `isServerM`'s fields); NewServer/NewServerR's `leasesLive` builders fixed.
  lean-check `--fast -a` clean: InvApplier, SnapApplyKV/Walk/Post/IsServer/OptsLemmas, EtcdServer__apply,
  EtcdServer__applyEntryNormal, StopShutdown, SnapSendBranch, AppliedOn, InvStart, InvBuild, KVStoreLaws, RestOn, UberOn,
  InvRead, NewServer, NewServerR (see the report), apply/Link, apply/Results, mvccrand writer__revoke, mvccfull
  runner__apply. Not checked (imports rebuild past lean-check's timeout): examples/etcd/auth/WorkCalls, the server
  `Link`/`Results`, restart*: left to the leaves build.
- **Stop (questions.md, "Item 7b F4: the free range"):** at the base `E` (`win = none`) the loop's applier state must
  free the window after each entry (`win_push none`), and `winsOk` says nothing of free ranges, so step 7 cannot place
  an index pushed between entries. Recommended (A): the loop's applier state at `∃ w, applyKV {E with win := w}`; NewServer
  opens the first window after `NewLessor`. The tie's design for the next agent is in the same entry.
- **Next after the decision:** F4 (tie at `kvsN .@ "win"`, store at `kvsN .@ "st"`, `E.Wt := ghostVar γw ½`, per-entry
  push in `applyEntryNormal`, `kvAusG`'s end builder records commits; the `Wt := …` field goes into NewServer's 20 `AEnv`
  literals: sed `γlt := γlt }`), then the ONE leaves build from `00b09c1360`, step 7, step 8, the c6b merge.
- **Pitfalls:** fresh lean-check of a server file rebuilds its imports through Lake (minutes; examples > 25 min). After
  `rw [hwin]` a goal has `lessorUserW … none`, not `lessorUser`: drop `iunfold lease.lessorUser`. `leasesLive`'s last
  conjunct `E.Wt E.win` reduces to `True` at the defaults: `iframe` the `ltHalf`, not `iexact`. Earlier pitfalls below.

## Previous START HERE (S4, 2026-11-17, item 7b: the applier at a window done at the apply layer; server at defaults; F4 next)

- Branch `auth-lease-s4`, worktree `/shared/etcd-grove-rs56`, head = this commit. Decisions: `questions.md` (last three
  entries: etcd-grove-03's decision on the applier forms and F4's token; the agent's forms "applier at a window,
  continued"). Not built since `00b09c1360` (lean-check only, `--fast`); the ONE leaves build comes after F4.
- **Done (this commit, lean-checked):** backend `DeleteRange/Txn/LeaseRevoke/LeaseGrant` at `E.win` (lemmas
  `apply.delWinTgt/delWinDrops/txnWinTgt/txnWinOps` in `WriteLemmas`, `revokeWinTgt/revokeWinDrops` in the Revoke file);
  `envAus`' end builder's target premise only for `pend ≠ []`; auth layer (`putPreW/deletePreW/txnPreW/revokePreW`
  carry `winTgt`); the auth checks at any window (`checkLeasePuts*/checkPutAuth/checkTxn*/CheckTxnAuth.spec` + `specL`s:
  last binder `w`, `lessorView γl U w`); wrappers (Corrupt/Capped/quota/newQuota); `dispatch.spec`, `uberApplier.Apply.spec`,
  `Apply.specRec`, `dispatch.kvSpecL`, `uberApplier.Apply.kvSpecL`, `uberKVC`, `Apply.kvSpecL`: pure premise
  `(E.lg = true → winTgt E.win rq log T) ∧ (E.lg = false → E.win = none)`; server at the defaults: `srvEnvOk` gains
  `E.win = none` (3rd conjunct; destructurings fixed), `applyEntryNormal` passes the premise from `HEo.2.2.1`,
  NewServer/NewServerR's `envAus` end builder from `kvAusG`'s (`Wt = True`), `snapE_win/Wt`.
- **Status of the check (lean-check `--fast`):** all of `apply/` that mentions the changed names checks, incl. the
  auth layer, wrappers, `DispatchKVL`, `uberApplier__dispatch/Apply`, `ApplyRec/KVL/FnKVL`; server: `EtcdServer__Txn`,
  `EtcdServer__applyEntryNormal`, `SnapApplyOpts`, `SnapApplyWalk`, `SnapApplyIsServer` check. **Known broken:**
  `SnapApplyKV.lean:115` rebuilds `leasesLive` at `snapE` and now needs `E.Wt E.win` (the walk binds it as `HlWt` in
  `SnapApplyWalk` after `rw [hwin]`, but does not pass it into `snapWalkPost`): thread `HlWt` through the post, or
  (simpler until F4) add `E.Wt = fun _ => True` to `srvEnvOk` beside `E.win = none` (F4 then replaces it by the tie
  token). `NewServer.lean:2100` fixed (one more `rfl`) but not re-checked. Not yet checked: `NewServerR`, the server
  `Link`/`Results`, `apply/Link`/`Results`, `EtcdServer__apply`, `SnapApplyPost`, the examples (`restart*`,
  `mvccfull`, `auth/WorkCalls`), `StopShutdown`, `SnapSendBranch` (destructurings of `srvEnvOk` fixed by hand).
- **Next, in order:** (1) finish the server check list (`python3 etc/importers.py --files <changed>` filtered by
  the changed names; `/shared/tmp/rs56-loop.sh LIST` runs lean-check over a list). (2) F4 (approved, conditions in
  questions.md): tie invariant at `kvsN .@ "win"`, store invariant at `kvsN .@ "st"`, allocated in NewServer after
  `NewLessor`; the server's base `E` has `win = none` (now in `srvEnvOk`) and `Wt :=` the tie token; per entry
  `applyEntryNormal` pushes the window and calls the applier at `{E with win := some (s, T)}` (applier facts held for
  every window); `kvAusG`'s end update must record the commit in the tie (replace the default-`True` builder in
  NewServer/NewServerR). (3) ONE leaves build from `00b09c1360`; steps 7, 8; c6b merge; full build; tcb; interfaces.
- **Pitfalls:** fresh lean-check of a file rebuilds its imports through Lake (minutes for server files). In proofs with
  a local `%w` (txn op patterns) name the window `wn`/`win`. `ipureintro` merges trailing pure conjuncts: a new pure
  conjunct after a big one needs `⟨⟨…big…⟩, W⟩`. `pkill -f rs56-loop.sh` kills your own shell: use the task id.

## Previous START HERE (S4, 2026-11-17, item 7b: F1-F3 done; the applier at a window IN PROGRESS (WIP commit, downstream broken))

- Branch `auth-lease-s4`, worktree `/shared/etcd-grove-rs56`. Decisions: `questions.md` (last: "F1-F3 forms: reviewed",
  then the agent's forms of this session, "Item 7b applier: forms", for review). Not built since `00b09c1360` (lean-check
  only); the batch's ONE leaves build comes after the server part.
- **Done, lean-checked:** F1, F3 (`3bfb255105`); F2 (`3c0b2b7fe0`: `txn.putAUW/delAUW/txnBeginAUW`, `lease.winWitOk`,
  now `isTxnLessor`'s last conjunct and a premise of `txn.DeleteRange.spec`). This WIP commit: the window premises moved
  into the begin payloads (`putAUW`: `(needsPrev → found) → winMove w I (putItemsOf I o)`; `txnBeginAUW`: `WinOps`), so
  `txn.Put.spec`/`Txn.specSole` lost their upfront `⌜winMove⌝`/`⌜WinOps⌝` (a rejected put/txn has `T = I`, which the
  upfront premise could not meet). **Applier at a window, as AEnv fields** (form, see questions.md): `AEnv.win : Option
  LWin := none` and `AEnv.Wt : Option LWin → IProp := True` (the server's window token, F4); `leasesLive(At)`/`kvOwnAt`
  hold `lessorUserW … E.win ∗ … ∗ E.Wt E.win`; `winTgt w rq log L` (`Chain.lean`: every backend outcome lease-exact at
  `L` leaves the window's target items); `putPre`/`deletePre`/`revokePre` carry `⌜winTgt E.win rq log T⌝`, `txnPre`
  `⌜winTgt … ∧ txnKeysNodup t⌝`; `envAus`' end builder `∀ w`, takes `E.Wt w`, `⌜T = items after⌝`, `winWit`, gives back
  `wSt ∗ E.Wt w`; `revokeClause` and `isApplyLessor`'s Grant clause at `∀ w` (`LessorDerive` passes it);
  `WriteLemmas`: `putPend_cases` (moved), `putWinTgt`, `putWinMove`, `kvOwnAt_of_split` over `(wSt ∗ E.Wt E.win)`,
  `putPre_of_mPre`/`txnPre_of_mPre` take `T0`, `hw : E.lg → winTgt E.win rq log T0`, `hn : ¬E.lg → E.win = none`
  (txn: `hnd`) and `ltHalf E T0` (given back). Checked: `Chain`, `Contracts` (via LessorDerive), `LessorDerive`,
  `WriteLemmas`, `applierV3backend__Put`, txn `Put`/`Txn`/`DeleteRange`, `LessorContract`.
- **Next, in order:** (1) fix the rest of `apply/` (convention: track `wSt ∗ E.Wt E.win` together, as `Put`):
  `applierV3backend__{DeleteRange,Txn,LeaseRevoke,LeaseGrant}` (Txn: `WinOps` in the begin payload from
  `txn.winOps_txn_of_nodup` + `winTgt`; DeleteRange: `winDrops` from `winTgt`; Revoke: `revokeClause` at `E.win`),
  `uberApplier__dispatch` (pass `T`, `hw`, `hn`, nodup from `rqOk`), `Apply.spec`/`dispatch.spec`: new pure premise
  `(E.lg → winTgt E.win rq x.log T) ∧ (¬E.lg → E.win = none)` (Apply's `T`), then `DispatchKVL`, `AuthApplyLatest*`,
  `checkLeasePuts*`, `AuthLemmas` etc. (`python3 etc/importers.py --uses lessorUser …`; patterns binding leasesLive's
  last conjunct). (2) F4 (server): instantiate `E.Wt` with a ghost-var half of a new tie invariant (the store's
  invariant cannot be changed without touching `bootStore.law`/`newServerStoreFreshA` (NewServer.spec premise, the
  etcdstart allocations): proposal: a separate invariant at `kvsN .@ "win"` with the store invariant moved to
  `kvsN .@ "st"` (both inside the law's `kvsN` mask), allocated in NewServer after `NewLessor` with `lessorWinTie`, the
  window var's other half and the event list; the end builder needs the current window because a persistent
  `winWit` could be replayed at a later commit (why `E.Wt`)). Server per-entry push at `{E with win := some (s,T)}`
  (persistent `applierSpec`/`uberIs` facts must then be held `∀ w`). (3) leaves build; steps 7, 8; c6b merge.
- **Pitfalls:** an `IProp` argument inside a term needs `iprop(…)`. In `apply`, `lease.winWit (mvccLeases …)` does not
  resolve: write `Perennial.EtcdGrove.lease.winWit (mvcc.api.mvccLeases E.γ)`. Patterns `⟨Hk, Hu, Hlt⟩` on
  `leasesLive(At)` now bind `ltHalf ∗ E.Wt` to `Hlt` (fine for re-framing, not for `icombine`).

## Previous START HERE (S4, 2026-11-17, item 7b: F1, F3 done; batch continues)

- Branch `auth-lease-s4`, worktree `/shared/etcd-grove-rs56`. Decisions: `questions.md` (last entries: the step-7 gap,
  "F1-F4 decision" by etcd-grove-03, with its conditions). Not yet built (lean-check only); the batch's one leaves build
  comes after the applier/server part.
- **Done (this commit, lean-checked):** F1: `winsOk` pairwise (`InvLessor`; `LessorHist.winsOk_snoc/_open`), `lease.winWit`
  (`InvLessor`, `True` at `none`), `lease.win_wit` (`LessorLemmas`). Form: `txn.isTxnLessor` gains the clause
  `□ ∀ L I w, leaseOwnW … w ={⊤}=∗ leaseOwnW … w ∗ winWit γl w I` (the txn layer has no `lessorRdInv`; premise of
  closed `txn_runTxn`/`server_kv_backend` strengthened, discharged by `isTxnLessor_of_lessorInv` via `win_wit`; consumers'
  patterns get a trailing `-`). F3: `lessor.Revoke.spec`'s begin payload `winWit γl w (items after) -∗ auEnd …`; the proof
  takes the witness after the delete loop; `txn.pendItems_commitLog` (`ApiLemmas`); `srvApi.auBegin_wand`/`auBegin_pre`
  (`MvccShapes`); callers at `none`: `LessorDerive.revokeClause_of_lessorInv`, mvccrand `writer__revoke`, mvccfull
  `runner__apply` (check pending at commit time: see below).
- **Done (F2, lean-checked):** `ApiVocab`: `txn.putAUW/delAUW/txnBeginAUW γ w …` (commit under `lease.winWit … w
  (pendItems σ₀.log pend) -∗`), old names abbrevs at `none`; `lease.winWitOk γl` (`InvLessor`, after `leaseOwnW`), now
  `isTxnLessor`'s last conjunct; `txn.Put/Txn.spec` take the `W` forms at `w`; `txn.DeleteRange.spec` takes
  `lease.winWitOk (mvccLeases γ)` (it has no lessor) and `delAUW`; proofs give the witness before `End`. Appliers
  (`applierV3backend.{Put,DeleteRange,Txn}`) still at `none` (`iintro -` before `commitAU_of_auEnd`).
- **Next, in order (one batch, then ONE leaves build from base `00b09c1360`):**
  1. (done) F2: `ApiVocab`: `txn.putAUW/delAUW/txnBeginAUW γ w …` whose commit is `lease.winWit (mvccLeases γ) w (pendItems σ₀.log
     pend) -∗ txn.commitAU …`; keep `putAU/delAU/txnBeginAU := …W none` (abbrevs: closed `txn_runTxn` names `txnBeginAU`,
     text unchanged). `txn.Put/DeleteRange/Txn.spec` take the `W` forms at their `w`; proofs (`Put.lean:113`,
     `DeleteRange.lean:74`, `Txn.lean:257`) get the witness from `isTxnLessor`'s new clause just before `End`.
  2. Applier at a window (design: "Next" of the previous START HERE): `kvOwnW`/`leasesLiveW`/`mPreAtW` (plain = `none`),
     `revokeClause`/`isApplyLessor` at `w`, `applierV3backend.{Put,DeleteRange,Txn,LeaseRevoke}` with the pure premise; the
     AU builders feed the witness to F4's end builder.
  3. F4: `kvStoreInvG`'s body: `lessorWinTie` + a monotone event list (push `(s,T,log_s,entry)` / commit `(j,log)` with
     `lessorAt` facts); `envAus`'s end builder takes `winWit` + "T = items after" and records the commit; `au_restore`
     records a free marker. Server: `applyEntryNormal` pushes per entry (`win_push (some T)`), snapshot `win_push none`.
  4. lean-check the changed files, then the leaves build; step 7 (the law; `lessorLawMask` gains `lessorRdN`), step 8,
     the c6b merge (`.lake/package-overrides.json` ← `/shared/tmp/manifest-c6b.json`), full build, tcb, interfaces.
- **Pitfalls:** an `IProp` argument written inside a term needs `iprop(…)` (`auBegin γ σ₀ iprop(W -∗ X)`). `wp_apply hR`
  whose window was inferred from a now-wrapped resource needs `(hR none)`. lean-check `-a` on mvccfull's `runner__apply`
  takes minutes (run it in the background).

## Previous START HERE (S4, 2026-11-17, item 7b: STOPPED before step 6's applier work: a gap in step 7's design)

- Branch `auth-lease-s4`, worktree `/shared/etcd-grove-rs56`, head = this commit. Decisions: `questions.md` (last
  two entries: the window design APPROVED by etcd-grove-03; "the approved design leaves step 7 unprovable after a
  commit", the stop, with the proposed fix F1-F4).
- **Done:** steps 1-5, 6a, 6b (commits in the previous START HERE below). No Lean change since `00b09c1360`.
- **Stop:** between the entry's `End` (the store's committed log, hence `kvLogLb` floors, advance) and the next window
  push, `F` may include the entry, so the window's start revision is below `F.length - 1`; nothing records that the
  lessor reached `T` before the commit. Fix proposed (questions.md): pairwise window stability + `win_wit` (lessor),
  the commit update takes a lessor witness (txn `putAU`/`delAU`/`txnBeginAU`, `revokeClause`/`Revoke.spec`), kvsN's
  tie a monotone event list (push / commit) recorded by `envAus`'s end builder.
- **Next after the decision:** one batch: F1 (InvLessor/LessorHist/LessorLemmas), F2-F3 (txn, lease Revoke), the
  applier at `w` (step 6 as designed below) + F4 (envAus, KVStoreCore tie, Chain W-forms), the server's push per entry;
  check with lean-check, then ONE leaves build (InvLessor ⇒ ~5100 modules). Then step 7, 8, the c6b merge.
- **Pitfalls / build:** as in the previous START HERE.

## Previous START HERE (S4, 2026-11-17, item 7b: step 6's rqShape/rqOk part done; the window's delivery to the applier next)

- Branch `auth-lease-s4`, worktree `/shared/etcd-grove-rs56`. Decisions: `questions.md` (last entries: "Item 7b step 6
  decision", "rqShape's conjunct: forms"); ledger 2026-11-16 7b entry ("Step 3" .. "Step 6, the permits").
- **Done:** steps 1-5 (`e1a57743a0`, `0fea6c849f`, `904deb4368`, `77d6bd24c7`); 6a permits (`94933020d5`); 6b (this
  commit): `txn.txnKeysNodup` moved to `txn/TxnRun.lean`; `apply.rqOk`'s txn arm `TxnPreA ∧ putOk ∧ txnKeysNodup`
  (so `rqShape`, `entryShape` and every apply spec taking `rqOk` carry it: `dispatch` has it); `rqShape_txnL`/
  `rqShape_of_txn` take `hn` (from `txnPermitOn`/`txnPermit`). Built: the 51 leaves importing the changed files.
- **Next: deliver the window to the backend applier.** Design (agent, not yet reviewed; refine before coding):
  1. *Who opens.* The server's per-entry apply (`EtcdServer__applyEntryNormal` / `ApplyNormalOn`), which holds kvsN's
     tie quarter (`lessorWinTie`, from `NewLessor` via boot into `kvStoreInvG`'s body, with a pure relation ws ↔ σ.log
     and the raft entry: start index `s` with `items hs[s] = items (stateAfter log)`, `T` = the model's items after the
     entry, the entry's `srvRLogLb`). `win_push (x := some T)` before `Apply`, the window kept after (next entry's push
     replaces it), `win_push (x := none)` in `applySnapshot` (L1: never reached under `clusterNoSnap`, but needed).
  2. *T before the outcome.* T = `leaseItemsOf` of the KV model's state after the entry (a pure function of the
     committed log the server knows). If the model rejects, T = the current items, and `winStep` then freezes every item
     (what the law needs for a rejected entry).
  3. *What each applier layer takes:* `kvOwn`/`mPre`/`leasesLive` at a window (`lessorUserW … w`, `leasesLive`'s `W`
     form; the plain names = `none`), and the pure premise "if the backend runs, `T` is its items after":
     `∀ s T, w = some (s, T) → ∀ oc, backendStep rq log oc → leaseExactL Lv rq log oc → T = leaseItemsOf (stateAfter
     (oc.logAfter log))`. The server discharges it by `KVOutcomeOn.backendLog_of_step` (the model's log is `backendLog`).
     At `w = none` all trivial, so the closed `apply/Results` (`chain_*`, over `kvOwn`/`applierSpec`) keep their text;
     `applierSpec`'s triples at `∀ w` strengthen their premise only (the step-3 pattern; STOP-check with the coordinator
     if `applierSpec` turns out to be a client-supplied premise of a closed result that a client cannot discharge).
  4. *Backend:* `applierV3backend.Txn` gets `WinOps` from `winOps_txn_of_nodup` (nodup from `rqOk` via `dispatch`; or add
     nodup to `txnPre`'s pure part at `w ≠ none`), `Put` from `winMove_to_target`, `DeleteRange` from `winOp_of_nodup`
     (`.delete`), `LeaseRevoke` from `Revoke.spec`'s `winDrops`.
  Then step 7 (the law: `m` = the history's last index when `F` is applied; per index its window via kvsN's tie), step 8,
  the lean merge (c6b), full build, tcb, interfaces.
- **Pitfalls:** a change to `apply/Chain.lean` or `txn/TxnRun.lean` rebuilds ~2100 modules (51 leaves, ~1 h in a slot).
  Proofs with a local `lease` need `Perennial.EtcdGrove.lease.winMove`; locals named `w` in `executeTxn`/`checkTxn`: the
  window is `wn` there. An explicit `none` makes posts `leaseOwnW … none` (convert with `lease.leaseOwnW_eq`). Don't
  `git stash` while a lean-check runs.
- **Build:** `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-e9e.json build $(python3 etc/importers.py
  --git <base> --leaves | grep '^\(Proof\|Spec\|RaftWitness\|PorcupineDag\|Robustness\)\.')`; logs
  `/shared/tmp/auth-lease-s4/7b-*.log`. After the lean merge: `manifest-c6b.json`, and `.lake/package-overrides.json`.

## Previous START HERE (S4, 2026-11-17, item 7b: steps 1-5 and step 6's permit part done; step 6 (applier) next)

- Branch `auth-lease-s4`, worktree `/shared/etcd-grove-rs56`. Decisions: `questions.md` (last entries: step 4 forms,
  "Item 7b step 6 decision" by etcd-grove-03); ledger 2026-11-16 7b entry ("Step 3" .. "Step 6, the permits").
- **Done:** steps 1-2 (lease, `e1a57743a0`); 3 (mvcc, `0fea6c849f`); 4 (server txn, `904deb4368`: `txn.WinOp`/`WinOps`,
  `delSelOf`, `putItemsOf`; the txn specs and `check*` at `∀ w`; the applier and `txn_runTxn` call at `none`);
  5 (`77d6bd24c7`, `txn/WinLemmas.lean`: `winOps_txn_of_nodup`, `winMove_to_target`); 6a (this commit):
  `txn.txnKeysNodup` (`WorkloadDefs`, with `delsPresent_srvOps`) in `txnPermit`/`txnPermitOn`/`txnPermitM`, discharged
  at the v3rpc handler by `v3rpc.txnKeysNodup_of_check` (`CheckShape`, no new client premise); the issue file
  `issues/etcd-txn-check-intervals-sibling.md` has the new consequence. Leaves since `77d6bd24c7` build.
- **Next (step 6 proper):** carry `txnKeysNodup` from the permit into what the applier sees: `reqPropOk` →
  `rqShape` (`InvProposer.txnPermit_reqPropOk` and `ReqOn.txnPermitOn_reqPropOk` call `rqShape_of_txn`/`rqShape_txnL`
  with `Ht.2.2.1`; give `rqShape` the conjunct, `ReqOn.lean:962`), so the apply loop has distinct keys per txn entry.
  Then the applier contracts (`apply/Contracts.lean`: `revokeClause`, `isApplyLessor(Any)`, put/txn contracts),
  `applierV3backend.{Put,DeleteRange,Txn,LeaseRevoke}` at `w` (Txn: `winOps_txn_of_nodup`; Put: `winMove_to_target`;
  DeleteRange: `winOp_of_nodup` on `.delete o` with `B = []`, keys of a sorted state's range distinct,
  `keys_nodup_of_sorted`), then `Chain.lean` (window open per entry with `T` = items after it, keep between entries,
  free in the snapshot branch; kvsN's tie share `lessorWinTie`), step 7 (the law), step 8, the merge (c6b).
- **Pitfalls:** proofs with a local `lease` need `Perennial.EtcdGrove.lease.winMove`; locals named `w` in
  `executeTxn`/`checkTxn`: the window is `wn` there. An explicit `none` makes posts `leaseOwnW … none` (convert with
  `lease.leaseOwnW_eq`). Don't `git stash` while a lean-check runs. A pure fact a permit carries reaches the applier
  only through `rqShape`.
- **Build:** `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-e9e.json build $(python3 etc/importers.py
  --git <base> --leaves | grep '^\(Proof\|Spec\|RaftWitness\|PorcupineDag\|Robustness\)\.')`; logs
  `/shared/tmp/auth-lease-s4/7b-*.log`. After the lean merge: `manifest-c6b.json`, and `.lake/package-overrides.json`.

## Previous START HERE (S4, 2026-11-17, item 7b: steps 1-3 done; step 4 (server txn) next)

- Step 3 (mvcc, `0fea6c849f`): `isLessor`/`isTxnLessor` clauses `∀ w`; `winStep` monotone, `winMove`, `winDrops`;
  mvcc writes and `Txn.*.contract`, `lessor.Revoke.spec` at `w` (details: ledger "Step 3").

## Previous START HERE (S4, 2026-11-17, item 7b: steps 1-2 (lease) done; STOPPED before step 3 (mvcc `isLessor`))


- Branch `auth-lease-s4`, worktree `/shared/etcd-grove-rs56`. Decisions: `questions.md` ("Item 7b step 1 decision",
  the soundness note, "Item 7b step 3"); ledger 2026-11-16 7b entry ("Landed (step 1-2, lease)").
- **Done (this commit):** the window ghost (option (A): `NewLessor`'s allocation extended, post gains
  `lessorWinTie γl []`): `InvLessor` vocabulary (`LWin`, `LWinRec`, `lastWin`, `winStep`, `winStable`, `winEnd`, `winsOk`,
  `itemsLive`, `lessorWinBody` in `lessorRdBody`, `winOwn` in `leaseClosers … w`, `leaseOwnW`; `leaseOwn`, `lessorUser`,
  `leaseOwnOpen`, `lessorUserOpen`, `lookupView(After)` are now `abbrev`s of their `W` forms at `none`); `LessorHist`
  (`winsOk_snoc`, `winsOk_open`, `lastWin_snoc`); `LessorLemmas` (`winBody_push`, `itemsLive_of`, `win_full`, `win_push` =
  win_open (`x = some T`) / win_free (`x = none`); push lemmas take `w`, `winStep`, `itemsLive`, `winOwn`); specs at `∀ w`:
  `Attach`, `Detach` (+ `winStep`), `GetLease`, `Grant`, `Lookup` (pass-through). `Revoke` still at `none`.
  Checked: every library leaf importing a file changed since `232df2b904` builds (log `7b-leaves3.log`);
  `tcb-report --check` matches the baseline (877 axioms, 4 sorries). Interfaces not yet regenerated.
- **Stop:** step 3 needs mvcc's `isLessor` (premise of closed `server_kv_backend` ×3 and, via `isTxnLessor`,
  `txn_runTxn`) at `∀ w`: a stronger premise of closed results. Options in `questions.md` ("Item 7b step 3").
- **Next after the decision:** step 3 (mvcc: `isLessor` clauses `∀ w`, `storeTxnWrite.*`, `Txn.*.contract`,
  `mvccDeleter`, `writeView_*`), then `Revoke.spec` at `w`, then steps 4-8 of the plan below. The free-marker / tie
  design (questions.md "Item 7b step 1", design point; approved) is in the ghost now: `win_push` with the tie's quarter.
- **Pitfalls:** `iunfold` takes one name (`iunfold leaseOwn; iunfold leaseOwnW`). Outside sites that `iunfold
  lease.lessorUser` etc. now also unfold the `W` form (done by a regex). Positional calls of `Lookup.spec`/`Grant.spec`
  need the extra `w` (`none`) after `U`. A change in `InvLessor` rebuilds ~5100 modules (a full build's worth).
- **Build:** `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-e9e.json build $(python3 etc/importers.py
  --git 232df2b904 --leaves | grep '^\(Proof\|Spec\|RaftWitness\|PorcupineDag\|Robustness\)\.')`; logs
  `/shared/tmp/auth-lease-s4/7b-*.log`.

## Previous START HERE (S4, 2026-11-17, item 7b stopped at step 1: resolved by option (A))

## Previous START HERE (S4, 2026-11-16, item 7b: option 2 APPROVED; plan below, no Lean edit yet)

- Branch `auth-lease-s4`, worktree `/shared/etcd-grove-rs56`. Decisions: `questions.md` ("Item 7b", "Item 7b decision"),
  ledger `notes/specs-only/ledger.md` (2026-11-16, 7b entry: add each thawed statement old → new as it lands).
- **Done:** raft, server, drivers (`f1540674ea` .. `782fc63bd3`); Freeze FROZEN (`209e3c68e6`, tag `auth-lease-s4-frozen`);
  items 5 (`ef5f154062`), 6 (`dcaa5c5d18`), 7a (`0455d1a2f7`, accepted); 7b design and decision (this commit).
- **Decision (user via etcd-grove-02):** thread a lessor *window token* IN PLACE through the frozen write chain; NO
  `…specW` siblings. STOP if it reaches a closed theorem's statement, needs an axiom, `sorry` or trusted text, or makes
  a thawed statement weaker for an existing client.
- **Next:** 7b per the plan below (report at its completion); 8. goose `authlease`, gen-init; 9. driver (STOP: D-k's texts;
  STOP: `Main.wp_proof`); 10. linking, gates, land stop (merge lean first).
- **Build:** `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-e9e.json build …`; leaves: `etc/importers.py
  --git <base> --leaves`. lean-check: one server, `--max-open 2`, `--stop` before builds and at the end of a turn.
- **Pitfalls:** `errIsTrue` is not persistent (rebuild it in a `□`). An `iprop` hypothesis is not a Lean one (state an
  entailment lemma). In `wp_apply (… (by …))`, a `by` naming a local can time out (`have` first). Build logs: grep `^error`.

## 7b plan (why: `questions.md`, "Item 7b")

**Core idea.** A snapshot pushed in the middle of an entry must carry its fact when it is pushed. The apply loop opens a
*window* per entry, `w = (start, T)`, with `T` the item map of the model after the entry. The lessor's invariant keeps
every snapshot `j ≥ start` *stable*: `∀ k, hs[start](k) = T(k) → hs[j](k) = T(k)`. Only `Attach`/`Detach` change
items, so only they need the window, with the premise `winStep w I I'`: every item an op changes goes to its target,
`∀ k, I k ≠ I' k → I' k = T k`. At `w = none` the premise is `True`.

Steps (bottom up; build each layer's leaves before the next):
1. **Lessor ghost** (`Proof/.../lease/InvLessor.lean`, `LessorHist.lean`, `LessorLemmas.lean`, `NewLessor`):
   - `LessorRdNames` gains a name (sed `γr.2.2.2.2` → `γr.2.2.2.2.1` in `lease/`; ~10 sites).
   - `lessorRdBody` gains the windows mono-list (auth ½ invariant, ½ owner), stability per window, and `itemsLive`
     (every item's lease in the snapshot's lease map).
   - `leaseOwnW γl L I w` (`w : Option LWin`) holds the owner's half. Define `leaseOwn γl L I := leaseOwnW γl L I none`
     (so `leaseOwn`'s clients do not change).
   - Push lemmas `hist_append(_set)`/`grant_hist`/recover take the window obligation.
   - New lemmas: `win_open` (owner: `none` → `some (hs.length-1, T)`, opening `lessorRdN`) and `win_close` (→ `none`,
     returning the persistent `□ ∀ j σ, start ≤ j ≤ end → lessorAt j σ → stable`).
2. **Lessor specs**: `lessor.Attach/Detach.spec` take `leaseOwnW … w` + `winStep`. `Revoke.spec` takes `w` for its
   deletes, which go through `mvccDeleter` + `Txn.DeleteRange.contract`. Grant, Recover and Lookup stay at `none` (no
   item change), unless the apply loop needs `w` across them, in which case `w` passes through unchanged.
3. **mvcc** (`Spec/.../storage/mvcc/`): `storeTxnWrite__{put,delete,deleteRange,Put,DeleteRange}`,
   `metricsTxnWrite__{Put,DeleteRange}`, the `watchableStoreTxnWrite` wrappers (find them), `Api.lean`'s
   `Txn.Put/DeleteRange.contract` and `mvccDeleter`, `writeView__{Put,DeleteRange}` + `Api/WriteViewApi.lean`'s
   `writeView_*_api`, `ApiLaws.lean` if it mentions them. Premise in the op's terms: `winStep w (pendItems log pend)
   (pendItems log (pend ++ ops))`. restore/New/NewStore stay at `leaseOwn` (`none`).
4. **server txn** (`Spec/.../etcdserver/txn/`): `put, Put, deleteRange, DeleteRange, txn, Txn, executeTxn` (+ the `check*`
   specs only if they carry `lessorUser`). `lessorUser` gets a `W` form (`lessorUserW`, `lessorUser := … none`). Premise
   at the request level: the request's whole change list moves each item at most once, toward `T`.
5. **Pure lemma** (new, server txn or apply): within one entry each key's lease item changes at most once along the
   prefixes of its change list (`txnShape`, `siblingSafeL`, `checkIntervals`, `put`'s same-lease early return), so
   `winStep` holds at each op for `T` = the items after the entry.
6. **applier** (`Proof/.../etcdserver/apply/`): `Contracts.lean` (`revokeClause`, `isApplyLessor(Any)`, the put/txn
   contracts), `applierV3backend__{Put,DeleteRange,Txn,LeaseRevoke}`, `AuthApplyLatest{Put,Txn}`, `WriteLemmas`,
   `checkLeasePuts(Keys)`. Then `Chain.lean`: per entry, `win_open` with the model's `T`, the op, `win_close`; record
   the window ↔ model tie (start/end revisions, `srvRLogLb` of the entry) persistently, in a mono-list owned by the
   lessor's window or by `kvsN`.
7. **The law** `lessor_keys_of_read` (new `LessorFollows.lean`, re-exported from server `Results`), at the frozen text.
   `lessorLawMask` gains `↑lease.lessorRdN` (approved form). Proof: `m` = the history's last index once `F` is applied.
   For `i ≥ m`, find `i`'s window; stability, `itemsLive` and `leaseKeptIn` at the window's two revisions (both
   `≥ F.length-1`, both `≤ σ.rev` by S5) give `lsHolds`. The S6 off-mode check is in the law's docstring.
8. Links (`etc/gen-link.py --server`, mvcc, lease), the examples (mvccfull/mvccrand: they stay at `none`), the
   interfaces (`etc/gen-interface.py etc/api/mvcc.txt`), the ledger rows, `cmpfrozen.py`, then report.

**Thawed statements (approved; record each old → new in the ledger as it lands):** `lease.lessor.Attach.spec`,
`Detach.spec`, `Revoke.spec`; mvcc `storeTxnWrite.{put,delete,deleteRange,Put,DeleteRange}.spec`,
`metricsTxnWrite.{Put,DeleteRange}.spec`, `watchableStoreTxnWrite.{Put,DeleteRange}.spec`, `Txn.Put.contract`,
`Txn.DeleteRange.contract`, `mvccDeleter`, `writeView.{Put,DeleteRange}.spec`/`writeView_*_api`; txn
`put/Put/deleteRange/DeleteRange/txn/Txn/executeTxn.spec`; apply `revokeClause`, `isApplyLessor`, `isApplyLessorAny`,
the applier put/delete/txn contracts, `applierV3backend.{Put,DeleteRange,Txn,LeaseRevoke}.spec`. Check first:
`etc/tcb-report.py` exported results and the `Results` statements must not mention these (closed theorems: STOP).

# History

## Previous START HERE (S4, 2026-11-16, item 7a done; 7b next)

- 7b's design lead then: only a writer holding `lessorMu` and the owner's `leaseClosers` appends to the lessor history
  (`InvLessor.lean:922-1036`); the last snapshot's item map is the owner's `I`, which mvcc ties to `pendItems σ.log
  changes` (`WriteViewApi.lean:207-275`); the tie as a mono-list in `kvsN`. Superseded by the 7b finding above.

## Previous START HERE (S4, 2026-11-16, items 5-6 done; item 7 next)

- Branch `auth-lease-s4`, worktree `/shared/etcd-grove-rs56`. Decisions: `questions.md` (gitignored; last entries,
  "Item 5", "Item 6": the forms decided, for the checkpoint report).
- **Done:** raft L-r0..L-r6, server, drivers (`f1540674ea` .. `782fc63bd3`); merge of lean 523c2a5495 (`2835564e9d`);
  **Freeze FROZEN** (`209e3c68e6`, tag `auth-lease-s4-frozen`; texts `notes/auth-lease-s4-frozen.lean.txt`; a change
  beyond them is a thaw: STOP); **item 5** (`ef5f154062`): Freeze §1 + K1; **item 6** (this commit): §2 (Md lessor/retry/
  stub specs, `lessorRemoteAtC`, `LessorPlain.lean` for plain callers), §3 C1 (`opGrantT` lease rows), C3/D-i
  (`clientTokAt` + Lease; `newClient` proves it), D-h (registrations, `client_lease_grant_on`/`_revoke_on` in
  `ResultsOn.lean`), H1 chain (`authedFrom` + `authedFrom_ctx` in `AuthWhy`, `leaseCheckFrom_of_authedFrom` in
  `LeaseCheck`, `requireAuthInfo.specC`, server `LeaseGrant`/`LeaseRevoke.spec`, v3rpc contracts + handler specs).
  Frozen texts compared equal to the tree's (script in the item-6 entry of `questions.md`: all but `opGrantT`/
  `clientGrant`, equal in meaning). Built: every library leaf importing files changed since `ef5f154062`.
- **Next, in order (Draft §7):**
  7. read handlers (§4: `EtcdServer.LeaseTimeToLive/LeaseLeases.specN` (T1, F4), v3rpc `leaseTTLOut`/`leaseLeasesOut`,
     `etcdLeaseTTLSpecMd`/`etcdLeaseLeasesSpecMd`, `etcd_lease_read_served`; `requireAuthInfo.specC` already carries
     `authedFrom`) and the per-member law (§5, §10 S1/S4, `leaseKeptIn`, `lsHolds`, `lessorLawMask`,
     `lessor_keys_of_read`; the tie per §5.4 / R4-5: the big one, est. 4-6 days).
  8. goose `authlease`, gen-init. 9. driver (STOP: D-k's exact texts; STOP: `Main.wp_proof` proved). 10. linking, gates,
     then the land stop (merge lean first: it is 61053b1f3c or later).
- **Build:** `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-e9e.json build …`; affected leaves:
  `$(python3 etc/importers.py --git <base> --leaves | grep '^\(Proof\|Spec\|RaftWitness\|PorcupineDag\|Robustness\)\.')`
  (Scratch/notes targets are unknown to lake). Logs `/shared/tmp/auth-lease-s4/i{5,6}-*.log`.
- **Pitfalls:** an `iprop` hypothesis is not a Lean one (`unfold … at H` fails: state an entailment lemma, as
  `kvOpAuOn_leaseGrant`). `opGrantT`'s match does not reduce under `iexact`. `attemptPre_md` did not `iapply` in
  `LessorPlain` (unfold `attemptPre` by hand). In a `wp_apply (wp_X … (by …))` argument, a `by` naming a local can fail
  or time out: `have` first. Don't Monitor the build log for `error` (axiom lists name `errors` packages): wait on exit.
  Build logs are huge (~1M lines of `#print axioms`): grep `^error`.

## Previous START HERE (S4, 2026-11-16, item 5 done; item 6 next)

- Branch `auth-lease-s4`, worktree `/shared/etcd-grove-rs56`. Decisions: `questions.md` (gitignored; last entries).
- **Done:** raft L-r0..L-r6, server, drivers (`f1540674ea` .. `782fc63bd3`); merge of lean 523c2a5495 (`2835564e9d`);
  **Freeze FROZEN** (`209e3c68e6`, tag `auth-lease-s4-frozen`; texts `notes/auth-lease-s4-frozen.lean.txt`, hashes in
  the Freeze header; a change beyond them is a thaw: STOP); **item 5** (this commit): Freeze §1 + K1 under the old names
  (texts checked equal to the frozen ones), `client_put_on` over `gs` (at today's `clientOpAuOn`; item 6 widens it);
  forms in `questions.md` ("Item 5"). Built: every library leaf importing the changed files (`etc/importers.py --git
  c8e05b5db9 --leaves`, minus `Scratch`/`notes`): passes. Not yet run: tcb/interfaces/bounds (at the land stop).
- **Next, in order (Draft §7):**
  6. F3 lease contract (client): §2 (`lessorRemoteAtC` in `InvLease.lean`, the four `lessor.*`/`retryLeaseClient.*`
     specs at `GrpcSpecMd` + `□ ▷ attemptPre`; the `leaseClient.*` stub specs need the same Md form (a form: kVClient.Put's;
     `etcdConn_InvokeMd`, `reqPre_box`)), §3 (C1 `opGrantT` lease rows, C3/D-i `clientTokAt` + `New`'s post, D-h
     registrations), the v3rpc H1 chain (§7 Round 3/4 tables; `requireAuthInfo.specC` + `authedFrom` (`AuthWhy.lean`,
     instance) + `leaseCheckFrom_of_authedFrom` (`LeaseCheck.lean`); `EtcdServer.LeaseGrant` uses `requireAuthInfo.spec`
     on the span ctx `ctx1`: needs an `authedFrom_ctx` (as `authedOutB_ctx`, `LeaseReqOn.lean:279`)).
  7. read handlers (§4, §10 T1) and the per-member law (§5, §10 S1, `lessorLawMask`; the tie per §5.4 / R4-5).
  8. goose `authlease`, gen-init. 9. driver (STOP: D-k's exact texts; STOP: `Main.wp_proof` proved). 10. linking, gates,
     then the land stop (merge lean first: it is 61053b1f3c or later).
- **Build:** `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-e9e.json build …`; affected leaves:
  `$(python3 etc/importers.py --git <base> --leaves | grep '^\(Proof\|Spec\|RaftWitness\|PorcupineDag\|Robustness\)\.')`
  (Scratch/notes targets are unknown to lake). Logs `/shared/tmp/auth-lease-s4/i5-*.log`.
- **Pitfalls:** in a `wp_apply (wp_X … (by …))` argument, a `by` naming a local can fail or time out: `have` first.
  `receiptBound` is a `Nat`. Don't Monitor the build log for `error` (axiom lists name `errors` packages): wait on exit.
  `v3rpc.LeaseServer.ty` must be written `go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer.ty` outside its namespace.
  Build logs are huge (~1M lines of `#print axioms`): grep `^error`.


## Previous START HERE (S4, 2026-11-16, Freeze FROZEN; items 5-10 next)

- Branch `auth-lease-s4`, worktree `/shared/etcd-grove-rs56`. Decisions: `questions.md` (gitignored; last entries).
- **Done:** raft L-r0..L-r6, server, drivers (`f1540674ea` .. `782fc63bd3`); merge of lean 523c2a5495 (`2835564e9d`,
  all checks at baseline: tcb 877/4, 65 collections, interfaces, bounds 390, mode 448); Freeze rev 3 + rounds 2-4
  (`fcc8b0985e`, `c30c95e91e`); **Freeze FROZEN** (`209e3c68e6`, tag `auth-lease-s4-frozen`): the frozen texts are
  `notes/auth-lease-s4-frozen.lean.txt` with per-text hashes in the Freeze header. A change beyond them is a thaw: STOP.
- **Next, in order (Draft §7):**
  5. leased KV at auth on (client): Freeze §1 + §9 K1 (`etcdPutSpecOn`/`M`, `etcdTxnSpecOn`/`M` filters, `txnUpdAtOn`'s write
     branch, `client_put_on` over options `gs`; server side `putPermitM_of_dep`, `ServerKVOn.lean:369-397`). Files naming them:
    - Proof/github_com/mit_pdos/etcd_grove/examples/etcd/auth/Run.lean
    - Proof/github_com/mit_pdos/etcd_grove/examples/etcd/auth/WorkEnv.lean
    - Proof/github_com/mit_pdos/etcd_grove/examples/etcd/auth/ClientOn.lean
    - Proof/github_com/mit_pdos/etcd_grove/examples/etcd/auth/WorkCalls.lean
    - Proof/github_com/mit_pdos/etcd_grove/examples/etcd/authN/run.lean
    - Proof/github_com/mit_pdos/etcd_grove/examples/etcd/auth3/run.lean
    - Proof/go_etcd_io/etcd/client/v3/ResultsOn.lean
    - Proof/go_etcd_io/etcd/client/v3/Results.lean
    - Proof/go_etcd_io/etcd/client/v3/AuthnServedOn.lean
    - Proof/go_etcd_io/etcd/client/v3/LeaseGrantServed.lean
    - Proof/go_etcd_io/etcd/client/v3/KVServiceOn.lean
    - Spec/github_com/mit_pdos/etcd_grove/examples/etcd/auth/SetUp.lean
  6. F3 lease contract (client): §2, §3 (C1/C3/D-h/D-i), the v3rpc H1 chain (§7 Round 3/4 tables: `LeaseServer.{LeaseGrant,
     LeaseRevoke}.spec`, `lessorGrantOkGM`/`lessorRevokeOkM`, `EtcdServer.{LeaseGrant,LeaseRevoke}.spec`, `requireAuthInfo.specC`,
     `authedFrom` + instance + bridge in `LeaseCheck.lean`).
  7. read handlers (§4, §10 T1) and the per-member law (§5, §10 S1, `lessorLawMask`; the tie per §5.4 / R4-5).
  8. goose `authlease`, gen-init. 9. driver (STOP: D-k's exact texts; STOP: `Main.wp_proof` proved). 10. linking, gates,
     then the land stop (merge lean first: it is 61053b1f3c or later).
- **Build:** `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-e9e.json build …`; checks with
  `LAKE_OPTS=--packages=/shared/tmp/manifest-e9e.json`; `etc/lean-check.py --max-open 2`, `--stop` before builds and at
  the end. `etc/importers.py --uses NAME FILE` to find what a changed statement breaks.
- **Pitfalls:** in a `wp_apply (wp_X … (by …))` argument, a `by` naming a local can fail or time out: `have` first.
  `receiptBound` is a `Nat`. Don't Monitor the build log for `error` (axiom lists name `errors` packages): wait on exit.
  `v3rpc.LeaseServer.ty` must be written `go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer.ty` outside its namespace.


## Previous START HERE (S4, 2026-11-16, L1 option 1 drivers done: checkpoint)

- Branch `auth-lease-s4`, worktree `/shared/etcd-grove-rs56`. Decisions: `questions.md` (last entries).
- **Done:** raft L-r0..L-r6 (`f1540674ea`, `0d81d23b6f`), server (`d54c9155f6`), drivers (`a86afd08dc` + this commit):
  `kvJ`/`kvrJ`/`kdJ` with the cap; `cluster_alloc`'s `¬ clusterNoSnap` → `srvClusterBoot_alloc` → `memberBoot`/
  `memberRestartFacts`/`memberRestartBoot`; `kvCluster` gains it (kv's `KV__run`); kvreconf/kvdurable `isReplica`
  `%Hnsn`; `NewServer.spec` premise now `clusterNoSnap γ.cl → 2^48 ≤ SnapshotCatchUpEntries` (so no new
  `receiptBound` in specs: bounds at baseline), auth drivers `→ 2^48 ≤ catchUp`. Freeze §5: `Scratch/S4Freeze.lean`
  (copy `/shared/tmp/auth-lease-s4/S4Freeze.lean`) over `clusterNoSnap γr.raft.raft.cl`, checks with 0 errors.
- **Checked** (`full5.log`): full build passes; `tcb-report --check` matches the baseline (870 axioms, 4 sorries);
  all 63 collections pass; bounds 377 = baseline; mode 448 = baseline; interfaces regenerated (9 files: raft
  `InvNodeRule`, etcdstart `Alloc3`, `AllocN`, `Defs`, `Restart`, `StartMemberAuth`, `StartMembersAuth` (Proof and Spec)).
- **Next:** Freeze review rounds r2–r3, then items 5–10 (Draft §7); authlease's allocation sets the flag `true`
  (`cluster_alloc_ns`; `memberBootOn` carries no mode fact, by design).
- **Build:** `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-e9e.json build …`.
- **Pitfalls:** in a `wp_apply (wp_X … (by …))` argument, a `by` block naming a local can fail ("unknown free
  variable") or time out: prove it in a `have` first. `receiptBound` is a `Nat` (cast in `Int` goals: `omega`).

## Previous START HERE (S4, 2026-11-16, L1 option 1: raft + L-r5 + server committed; STOPPED at the checkpoint)

- **Branch** `auth-lease-s4` (worktree `/shared/etcd-grove-rs56`). Plan: Freeze `notes/auth-lease-s4-freeze.md` §8.4;
  GO and form decisions: `questions.md` (last entries, etcd-grove-02).
- **Done:** raft part 1 (`f1540674ea`: NsCap/storCapF, maybeSendAppend, L-r0..L-r4, L-r6, snapshotCert without the
  flag, `readySnap`'s mode conjunct); L-r5 (`0d81d23b6f`: `Bootstrap` sets `ns` via `ownRaftPhys_set_ns` from
  `⌜reNoSnap = false⌝ ∨ storCapF`, `setupNode` carries it in `InitialState`'s post, `StartNode` derives it,
  premise gone; `memStorInv_alloc`'s `sorry` takes `clusterNoSnap γ → c ≤ 1`); server (this commit):
  `compactRaftLog.spec` premise `clusterNoSnap → snapi ≤ scu`; `isServerApplyAll`'s scu row
  `clusterNoSnap → receiptBound ≤ scu` (start keeps it through the default-catch-up join; the five built hubs carry
  it on `Hscu`; `NewServer.spec` premise `clusterNoSnap γ.cl → receiptBound ≤ cfg.SnapshotCatchUpEntries'`);
  `clusterNoSnap → ai ≤ w` in `snapshotIfNeededAndCompactRaftLog.specBatch`, `applyAll.specBatch`, `applyResR`
  (run's loop; start: first start via `rnRestartOk_mode`/`isRaftNode_mode`, `srvRunRestartR`'s
  `clusterNoSnap → A₀ = []`); the snapshot job takes `¬ clusterNoSnap` from `rnApSnap` (from `readySnap`);
  restart path: `rnBootPre .restart`, `NodeStartSpecR`, `NewServer.specR`, `rnRestartOk`'s restart disjunct take
  `¬ clusterNoSnap`. Server `Link`, `Results`, `NodeApiLink`, `read.Link` build.
- **Not yet:** drivers/examples (callers of `NewServer.spec`/`specR`, `cluster_alloc*`, `StartNode`/`RestartNode`
  users outside raft, the kv examples' storage `B`), `tcb-report --check` (needs the full build), interfaces of
  other packages (`etc/api/etcdstart.txt` etc.), Freeze §5 `memberNoSnapInstall` → `⌜clusterNoSnap …⌝`.
- **Next, in order:** drivers (`etcdstart` `newServerMode`/`Restart`, cluster3, auth/auth3, k8s apimodel: flag
  `false` except authlease; discharge the scu premise from `Hrb48` and `NoSnapCatchUp = 2^48`); the kv examples
  (`KvStorage`, `KvrStorage`, `KdStorage`: their `memStorJ` copies, `storBnd` patterns gain one `-`); full build,
  `etc/tcb-report.py --check` + collections, `gen-interface --check` on every list; then §5 and items 5-10.
- **Build:** `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-e9e.json build <targets>` (logs
  `/shared/tmp/auth-lease-s4/build-*.log`); `LAKE_OPTS=--packages=... etc/lean-check.py --max-open 2` only when
  imports are built, `--stop` before builds and at the end.
- **Pitfalls:** `applyResR`'s positional patterns (`stop_split`: `Hwt` is `rnWalTokA`, the `∃ w` is the next one);
  Go's default-catch-up `wp_join` leaves the else branch to close by hand; in `local macro`s with `hygiene false`,
  Iris hyps are not Lean hyps; `ApiImpl.readySnap`/`readySnap` stay defeq (`¬ … = true`).

## Previous START HERE (feasibility, superseded)


- **Branch** `auth-lease-s4` (worktree `/shared/etcd-grove-rs56`). S0–S3c on lean. Draft `notes/auth-lease-s4-draft.md`
  (statement approved). Decisions: `questions.md` (untracked), "auth-lease S4", "S4 Freeze r1 decisions", "S4 Freeze rev 2: L1 stop".
- **Done:** items 0, 2, 3 (`5baacbd07a`, `647aadf78b`, `7b126d3e4e`, `2bddb5967a`); item 4 Freeze rev 1 + r1 (`c4f188d250`),
  L1 stop (`ef4c34650e`), rev 2's texts (`5d142952af`; `Scratch/S4Freeze.lean`, copy `/shared/tmp/auth-lease-s4/S4Freeze.lean`);
  **L1 option 1 approved by the user**; its feasibility check: Freeze **§8.4** (this commit, no tree edits).
- **§8.4 in one line:** feasible, snapshot path untouched (flag `false` = today's invariant; proof bodies of the
  snapshot examples gain only a trivial `flag = false` conjunct at `Compact`/`ApplySnapshot`); estimate **11–14 days**
  (centre ~12.5, over the ~12 stop line); raft API laws L-r0..L-r6 listed there.
- **Next, in order (on the go):**
  1. raft (§8.4 table order): `NsCap`/`storCapF`; `maybeSendAppend`'s two branches; `ownRaftPhysC_sn` split; boot
     `set_ns` (revive from `ce370ad2a8^`); L-r0..L-r6; `etc/gen-interface.py etc/api/raft.txt`;
  2. server: `compactRaftLog` premise, the `ai ≤ w` clause (apply-loop specs), the `scu` row, `NewServer`, names;
  3. drivers/examples: flag `false` everywhere, authlease `true`; `etc/tcb-report.py --check` + collections;
  4. Freeze §5: `memberNoSnapInstall` → `⌜clusterNoSnap γr.raft.raft.cl⌝`; review rounds r2–r3
     (`/shared/tmp/auth-lease-s4/freeze-review-r{2,3}.md`); then items 5–10 (Draft §7).
- **Token:** `authlease-3354335` (ports 16000/17000).
- **Pitfalls:**
  - Build: `flock /shared/tmp/etcd-grove-build.lock systemd-run --scope -q -p MemoryMax=64G lake
    --packages=/shared/tmp/manifest-e9e.json build …`. Run `etc/gates.sh` only under
    `flock /shared/tmp/etcd-grove-full-build.lock`.
  - Check: `LAKE_OPTS=--packages=/shared/tmp/manifest-e9e.json etc/lean-check.py -a Scratch/S4Freeze.lean`.
  - `leaseTTLRow` needs `[go_etcd_io.etcd.server.v3.etcdserver.Assumptions]` in the section.
  - Auth-off lease users: `rw [hoff]` before `iintro`. Mode gate: no literal `true` in the new package (L3).
  - Ports 20000–21999 belong to another session.

Plan: `notes/auth-lease-scope.md` (approved; §0, §2, §5, §7). Decisions Q1–Q9: `questions.md`,
section "auth-lease". Worktree `/shared/etcd-grove-rs56`, branch `auth-lease` (off lean `89ef103d5b`,
with `auth-lease-scope` merged).

## Done

- **S0 (probe), 2026-11-14.** Unlinked, untracked: `Scratch/AuthLeaseProbe.lean` (the apply layer's lease
  check at the latest state) and `Scratch/AuthLeaseProbeModel.lean` (the mode-`on` model on the triple
  state). Both check with no `sorry`. Findings: CP0 report (below, "Pitfalls").

- **S1 (empty-user fix), 2026-11-14** (go from etcd-grove-81): `leaseCheckFrom` over `principalBound`,
  `v3rpc.leaseCheckT` over the new `v3rpc.principalBoundT` (`infoBoundTM` deleted); lemmas
  `principalBoundOn_of_ctxBound`, `principalBound_ctx` (`LeaseCheck.lean`); ledger and decisions.md entries;
  full build passes; interfaces unchanged (`gen-interface --check` on every `etc/api` list); waiting for the
  coordinator's go to run `etc/land.sh`.
- **S2 Draft** (design text): `notes/auth-lease-s2-draft.md`, reviewed in rounds (`/shared/tmp/auth-lease/`).

- S1 landed: lean `28b89b9dd6` (2026-11-14).
- **S2 (apply layer at the latest state with a lessor), proved, 2026-11-15** (Freeze approved by
  etcd-grove-81 with the five design choices): `AuthLatest` (lease vocabulary, `isAuthStoreL`'s snapshot
  clause), `AuthApplyLatestPut` (`checkLeasePuts{,Keys}.specL`, `checkPutAuth.specL`, `Put.specL`),
  `AuthApplyLatestTxn` (`txnPutsW`, `txnOutLL`, the txn checks), `AuthApplyLatestRevoke` (new:
  `revokePreW`, `LeaseRevoke.specL`), `AuthApplyLatest` (`authOutLL`, `kvPostFL` + lease class),
  `DispatchKVL` (`authKVKind`, `kvOutL`/`kvShapedL` with leases, `applierKVL`'s revocation triple,
  `dispatch.kvSpecL` widened, the revocation branch), `ApplyKVL`/`ApplyFnKVL` widened, `UberKVLBase`,
  server: `KVOutcomeOn` (`txnPutsW_plain`, `authOutL_of_kvOutL` over `plainCover`), `ApplyNormalOn`,
  `UberOn`, `UberKit` (`LeaseRevoke.specL`), `EtcdServer__applyEntryNormal`, `Results`
  (`apply_lease_revoke_latest`). Full build green; lean `dd068e790f` merged.

- S2 landed: lean `c3da59fa29` (2026-11-15).

## Next, in order

1. S3, revised (etcd-grove-81, 2026-11-15, option (a) of `/shared/tmp/auth-lease/s3-scope-gap.md`; 26–40 days after
   S3a review r1's F1 (ii), F2 (a), F3),
   in three Freeze packages:
   - **S3a** (now): the model and the apply thread: the triple state with the lease table, the client's half kept in
     `kvInvOn`, the auth-on table for `srvRest`, `authKVKind` in the three places, admission of grants, revocations and
     leased puts at the revocable mode. Design: `notes/auth-lease-s3a-draft.md` (revision 4 = the S3a Freeze package,
     three review rounds `/shared/tmp/auth-lease/s3a-review-r{1,2,3}.md`; N1 (ii′): `leaseExactL` in the class
     track's `kvPostF`); **frozen at revision 5** (etcd-grove-81, 2026-11-15, after round 4; tag
     `auth-lease-s3a-frozen`). **Probe done** (2026-11-15): `kvOwnAt` and `kvOwn ⊣⊢ ∃ L, kvOwnAt E log L` proved
     (`Scratch/S3aProbe.lean`, untracked); `applierV3backend.Put`'s proof has the live set `L` in hand and splits
     on `o.leaseID = 0 ∨ o.leaseID ∈ L` (`applierV3backend__Put.lean:97-170`), rebuilding `kvOwn` at the same `L`
     (`kvOwn_of_split`), so its `kvPostF` conjunct is local; the key-length bound is closed by §5. **Prove: started 2026-11-15, STOPPED at a finding**
     (see "S3a Prove: where it is" below). Order (Draft §8): (1) the model (`KVAuthModel.lean`: `OnState`, `kvEntryOn`/`kvRaftOfOn` on it,
     `kvGrantedL`/`leaseGrantedM`/`leaseOk` from `Scratch/AuthLeaseProbeModel.lean`, `plainEntryOn lm`/`plainReqL`/
     `txnPlainL`, `entryDetOn`/`entryShapeOn lm`, `keysNonEmpty`, `keysLeasesLive`, `KVAuthBridge.leaseOk_iff`);
     (2) `kvInvOn` + alloc, `appliedTableM`, `srvKVInvsOn`'s rows (`lm = E.lm`, `pre = []`), `appliedTableM_eq_model`;
     (3) `kvOwnAt`/`leaseExactL`/`kvPostF`'s conjunct through backend/quota/capped/corrupt/auth, `kvPostFL`, the four
     layer triples; the apply thread's model (`outcomeOn`, `kvAppliedOn`, the S2 `plainCover` lemmas restated);
     (4) the snapshot path (§5, its frozen `hnl` text); (5) `applyEntryNormal.wp_proofOn`/`apply.wp_proofOn`, the
     examples' proofs. `KVAuthModel` rebuilds ~1500 modules: full builds under the flock.
   - **S3b**: the request side (grant, revoke, leased put with auth on). **Draft** (2026-11-15):
     `notes/auth-lease-s3b-draft.md` (statements old → new, §6; decisions D1–D5, §7); probe `Scratch/S3bProbe.lean`
     (untracked; copy `/shared/tmp/auth-lease-s3b/S3bProbe.lean`, checked clean: the widened `authTie`, applied ⇒
     `kvGrantedL`, an applied put's lease live); reviews `/shared/tmp/auth-lease-s3b/review-r*.md`. No frozen text edited. **Rev 3 = the S3b Freeze package**
     (round 2: no first-tier finding); STOPPED for etcd-grove-81's decisions D1–D7 (questions.md). After the Freeze:
     the Draft's §8 order of work (est. 5–8 days).
   - **S3c**: the couplings and `NewServer`; the `lease.bootCfg` hub change and the `NewLessor` docstring (hard stops).
     **Plus (S3b decision D6, etcd-grove-81, 2026-11-15; +2–3 days):** the gRPC lease handlers' contracts at the mode
     (v3rpc `lessorGrantOkG`/`lessorRevokeOk` at `isServerReqM E.authOn` with the client's lease deposit, `KVDep.lease`/
     `LeaseDep` as S3b Draft §5 sketches; `lessor*_of_server`, `ServerLeaseGrant`/`ServerLeaseRevoke`, v3rpc `Results`'
     `lessor*_server`) and etcdstart's lease registrations at auth on (`etcdLeaseServedAt` at `etcdModelOfServer E γr
     E.authOn`), beside the couplings `etcdLeaseServedAt`'s revocable branch needs. Until then those callers stay at
     auth off (they hold `isServerReq` and pass the off permits).
   - The auth-on snapshot path carries the leases (F2 (a)); the latest track gains a lease-exact outcome (F1 (ii)).
2. S4 with the client's leased put (`WithLease`, `Put`/`Txn` with a lease) and linearizable client specs of
   `Lease.Grant`/`Revoke` (F3).

## S3a Prove: where it is (2026-11-15, after rev 6)

Rev 6 (§14) FROZEN with the stronger guard (etcd-grove-81); its frozen-text edits are made (`EtcdServer.{Put,
DeleteRange}.spec`, `txnAppliedOk`, v3rpc `putApplied`/`deleteApplied`/`txnAppliedAns`, client `KVService` rows,
`readQ_of_ansM`, `srvKVCoreM_fire` + `srvKVFacts_fire(0)`, `kvLogOkTo`). The tree does NOT build yet.

**Strategy: a transitional port first.** `srvKVInvsOn` keeps a TRANSITIONAL `γr.kv.lg = false` (beside the frozen
`lm = E.lm ∧ pre = []`); the apply and snapshot proofs take `lm = none` from it (`KVNames.lm_of_lg_false
Hrows.2.2.1`, marked "TRANSITIONAL until the §5 step") and keep their `plainCover` reasoning. Steps 3 (§3a
`leaseExactL`/`kvOwnAt`/Chain's `kvPostF`), 4 (§5, drop the transitional row) and 5 (revocable-mode apply arms) come
after the tree builds.

Checked clean with `etc/lean-check.py` (in order): KVAuthModel, KVApplyOn, KVModelM, KVReadOn, KVAuthShape, ProposeOn,
ServerOnDefs, ImageOn, ServerOn, NewServerAllocOn, AuthTie, AuthTieRead, ReqOn, ReadOn, auth/Hist, KVOutcomeOn,
ApplyEntryOn, ApplyTieOn, ApplyNormalOn, SnapRecvOn, MergedImageOn, SnapAuthRecover, AuthCompRows,
Spec/EtcdServer__applyAll, ApplyAllSnap, ModeSpecs, EtcdServer__Range, EtcdServer__apply, EtcdServer__applyEntryNormal,
StartOn, RunOn, NewServer, EtcdServer__applySnapshot (SnapApplyPost), SnapSendBranch, StopShutdown, EtcdServer__run,
ClientModel, EtcdServer__Put/DeleteRange/Txn. Edited, not yet checked: auth/MainAlloc, etcdstart/Alloc3On (alloc premises),
server Results (`server_member_alloc_on` premises), KVLogOk, client WatchFire/Results/KVService, v3rpc ServerKV, InvRead.

**Where it is (2026-11-15, session 2):** the full build is GREEN at `build9` (`/shared/tmp/auth-lease-s3a/build9.log`,
flock + 64G, commit after `auth-lease S3a §3a`); `etc/tcb-report.py --check` at 870 axioms, 4 sorries (run at `build8`,
before §3a; §3a adds no axiom). Done this session:
1. **The read rows' guard** (handoff item 1, decided by etcd-grove-81): `⌜on = true → γr.kv.lm = .none → kvLeasesOn γr.kv
   srvAuthSt0 L = []⌝` inside the `∃ L` of `rangeAnsOkM`/`txnReadAnsM` (`ServerKV.lean`), proved in `ServerKVOn` by
   `ReadOn.depQ_leases_none` (from `srvKVCoreM_leases_none`: `kv_log_plain_on` + `kvLeasesOn_none`; `iapply wp_fupd` before
   the `wp_apply` so the post can be updated). `readQ_of_ansM` (client Results) takes the guard;
   `rangeErrReply_of_errAt` became a fupd lemma over `srvKVCoreM E.authOn` (the error row `rangeErrAt` keeps its text).
   §14's table has the two rows.
2. **Client chain and examples** destructure the table (`ServerKVGet`, `ServerKVTxn`, `ClientPutGet`, `kubernetes/Defs`,
   k8s `etcd3/Compact`, `partition/WatchWrites`, `txnlin/Calls`, `auth/WorkCalls`). Pitfall: `simp only [hs, …]` on an
   Iris goal rewrites the context too: specialize `Himp $$ %hs` BEFORE the simp.
3. **§3a**: `apply.leaseExactL`, `leaseExactL_rejected`, `leaseExactL_other`, `kvOwnAt`, `kvOwn_iff_at`, `kvOwn_of_at(P)`,
   `kvOwn_atP`, `kvOwn_rejected`, `kvOwnAt_ltHalf` (Chain); `kvOwnAt_of_split`, `wSt_ne_false` (WriteLemmas). `kvPostF` and
   `kvPostFL` carry `∃ L, ⌜leaseExactL L rq log oc⌝ ∗ kvOwnAt E (oc.logAfter log) L`; the backend's Put (a dead lease's
   commit refuted by two writer halves), Txn (`txn.Txn.spec`'s `PathsLeaseOk`/rejection), DeleteRange (trivial) prove it;
   quota/capped/corrupt/auth pass it or reject (`kvOwn_rejected`); the class-track consumers (`apply/Results`,
   `uberApplier__dispatch`) forget it (`kvOwn_of_atP`). The latest track: `dispatch.kvSpecL` gains `⌜v3 = true → E.lg =
   true → leaseExactL T rq log o⌝` (from `kvOwnAt_ltHalf` at the caller's `ltHalf E T`), `uberApplier.Apply.kvSpecL`,
   `uberKVC`, `apply.Apply.kvSpecL` gain `⌜∀ o b, out = .dispatched o b → v3 = true → E.lg = true → leaseExactL T rq x.log
   o⌝`; `auth_pass_kvPostFL_nil` takes `dispatchKind rq = .leaseRevoke`. The server (`applyEntryNormal`) drops the new
   conjunct for now (`%HXo, -, #Hdel`): §6 consumes it.
4. **§4 started**: `appliedTableM`, `appliedTableM_false/true`, `appliedTableM_eq_model` in `KVModelM.lean` (checked with
   lean-check, not yet in a full build; it rebuilds ~1270 modules). **Finding:** `srvRest` (`InvRest.lean`) is imported
   by `KVAuthModel`, so it cannot read `kvLeasesOn`. Proposed form (to do): split `srvRest` into a table-generic
   `srvRestT E γr T A` in `InvRest` (`srvRest E γr A := srvRestT E γr (appliedTable γr A) A`, so the off proofs are
   untouched) and `srvRestM on E γr A := if on then srvRestT E γr (appliedTableM true γr A) A else srvRest E γr A` in a
   module after `KVModelM`; `srvRestRp`/`imageLeasesAt` and the auth-on users take `srvRestM E.authOn` (Draft §4's
   "`srvRest` and `srvRestAt`'s callers use `appliedTableM E.authOn`", in a Lean shape that fits the import order).

5. **§4's split done** (approved by etcd-grove-81 as a form, §14 row): `srvRestT`, `srvRest_eq_T` (`rfl`),
   `srvRestT_lg_false` (InvRest); `srvRestM on` (`srvRest` off, `srvRestT … (appliedTableM true γr A)` on),
   `srvRestM_false` (`rfl`), `srvRestM_lg_false`, `srvRestRpM on`, `srvRestRpM_false`, `srvRestRpM_lg_false` (ApplyRDefs);
   `imageLeasesAtT`, `imageLeasesAt_eq_T` (ImageLeases). Full build `build10` at `f0b7821df7`.

**Session 3 (2026-11-15):** the statement switch is DONE (commit after `82b6add2a9`, full build `build12`, `/shared/tmp/auth-lease-s3a/build12.log`):
- Defs: `srvRestM`/`srvRestRpM` moved to `KVModelM` (the snapshot files do not import `ApplyRDefs`); `srvRestRM on`
  (ApplyRDefs); `imageLeasesAtM on` (SnapApplyDefs); M laws in KVModelM (`srvRestT_eq_at`, `srvRestM_eq_at/_open/_close/
  _snoc`, `appliedTableM_cc`, `srvRestM_nil`, `leaseItems_of_noLease`) and ApplyRDefs (`srvRestRM_*`, `srvRestRpM_eq_at/
  _ro/_open/_close/_model`); `srvKVInvsM_rows` (ServerOnDefs).
- Statements at the mode: the five specs (applyEntryNormal, applyEntries, apply, applyAll specBatch/specSnapM,
  applySnapshot specSnapM incl. `hlease : imageLeasesAtM E.authOn` and the frozen rev-5 `hnl`), ModeSpecs.specOn, the
  run/start rows (RunOn, StartOn, AuthCompRows), `srvSnapAppliedG on`, `SnapImageFactsOn.nolease/.hlease` (rev-5 §5).
  The start rows convert at `isServerBuilt_of_gapOn` by `srvRestM_nil` (empty prefix), not transitional.
- `EtcdServer.apply.wp_proofOn` is ported to the M laws for real (no transitional step).
- **§5 started:** `keysLeasesLive_kvRaftOfOn` (KVAuthModel; needs only `LogNoLease log0`: `backendLog` enforces the
  live set, so no admission premise), with `liveSt` and its laws through `applyChange(s)`, `srvOps`, `backendLog`,
  the chain, `dispatchLog`, `kvEntry`, `kvEntryOn`; `kvInvOn_log0`, `kvInvOn_keysLive` (what the callers of
  `specSnapM` need for the new `hnl`). `keysNonEmpty`'s preservation NOT done (needs `kvShapeAll`'s put-key shape).
- TRANSITIONAL sites now (each marked "TRANSITIONAL until the §5 step"): `isServerC_restM` (AuthCompRows) used by
  applyAll's merged send; the `srvRestM_lg_false`/`srvRestRpM_lg_false` conversions in ApplyAllSnap (on branch:
  `snapRecv_imageOnR`, merged send), EtcdServer__applyEntryNormal (both on branches: `irevert HRS HΦ; simp only [hR]`),
  SnapApplyPost (`HrestM`), EtcdServer__run/StopShutdown/NewServerR (the run and stop rows at `srvRestRM K.isOn`, off by `srvRestRM_false`: not transitional), EtcdServer__applySnapshot (lg = false branch: `Hnil` derives `LogNoLease` of the auth-on
  image from `kvInvOn_log0` + `kvRaftOfOn_restorable` at lease mode none; `hleaseI` to the off table), SnapRecvOn and
  ApplyAllSnap (`SnapImageFactsOn` built from the lease-free image); plus the older ones (`grep -rn TRANSITIONAL Proof`).

**Session 4 (2026-11-15):** handoff items (a), (b) and most of (c) DONE (commits `26acfbb48f`, `1239efff42`; full
build `build13` at `1239efff42`, `/shared/tmp/auth-lease-s3a/build13.log`; see the session report):
- (a) `keysNonEmpty` preserved: `neSt`, `opKeysNE`/`opsKeysNE`, `reqKeysNE`, `entryKeysNE` and their laws through
  `applyChange(s)`, `srvOp(s)`, `backendLog`, the chain, `dispatchLog`, `kvEntry`, `kvEntryOn`, `kvRaftOfOn`;
  `reqKeysNE_of_shape` (`kvShapeAll`: a put's key is a point key of the cache's shape), `entryKeysNE_of_plain`,
  `keysNonEmpty_kvRaftOfOn` (KVAuthModel). Not yet used (§6's `kvShapedL` at a leased put takes it).
- (b) the snapshot consumers at the keys-live form: `applySnapshot_walk`'s `hnl` is "every leased key's lease is in
  `Recover`'s `Lr`" (pending items = the image's lease items, each short by `Hkey`), `snapWalkPost`'s `leaseOwn Lr`
  at the image's lease items, `snap_applyKV` at them (`leasesKnown_of_items`, SnapApplyKVLemmas), `snap_srvRest`
  at `srvRestM on` (`srvRestM_close`), `srvSnapApplied_of_walk` at `appliedTableM E.authOn` (its TRANSITIONAL
  `HrestM` gone). `EtcdServer.applySnapshot.wp_proof`'s leased branch (`E.lg = true`) now covers both auth modes:
  the mode's table (`ImageLeasesOn.lean`: `kvEntryOn_table_eq_or`, `kvRaftOfOn_table_{mem,nodup,mono}`,
  `appliedTableM_{nodup,ids_granted,mono_mem,mono_sub,rev_mem,granted_live}`, `kv_grantLog_nodup_on`), the image's
  records by `imageLeasesAtT_recs` (ImageLeases, table-generic), `hnl` from the frozen rev-5 text. The `E.lg = false`
  branch is not transitional (lease mode `none` from `E.lg = false`); its comment relabelled.
- (c) the auth-on image carries the leases (Draft §5's ImageOn/MergedImageOn/SnapSendBranch/snapRecv rows):
  `bkRestAtNAL T` (ImageOn) in `imageRestAtOn` at `kvLeasesOn γk st₀ L`; `mergedImgM`'s table `appliedTableM M.isOn`;
  `bkRestAtM_of_obs`, `mergedCreate_window`, `stop_obs` at `appliedTableM E.authOn`/`srvRestM E.authOn`;
  `merged_imageOn` builds the leased certificate (`kvLeasesOn_none` when `E.lg = false`); `snapRecv_imageOn`,
  `snapRecv_imageOnR` take `srvRestM true`/`srvRestRpM true`, no `hlg`, and give `SnapImageFactsOn` from the image's
  records (`bkRestAtNAL_other`, `restModel_bk_of_NAL`, `image_alarmNAL`, `image_membBucketsNAL`,
  `clusterImageOk_of_NAL`, `imageLeasesAtT_of_NAL`, SnapRecvOn; `nolease` from `keysLeasesLive_kvRaftOfOn`).
  TRANSITIONAL conversions removed: applyAll's merged send (`isServerC_restM` deleted), ApplyAllSnap (on receive and
  on merged send; the lessor-mode block `hEm`/`HElg`/`Hlrev` deleted: unused), SnapRecvOn, MergedImageOn,
  SnapApplyPost (`srvKVInvsM_lg` deleted).
- Left of (c), all bound to §6: the row `γr.kv.lg = false` in `srvKVInvsOn` (KVApplyOn) and its three users,
  `kv_entry_pre_on` (ApplyEntryOn:151, over `plainCover`) and `applyEntryNormal.wp_proofOn`'s two branches
  (v3 = false replay, 1293; v3 = true, 1519). Dropping the row before §6 breaks those proofs: the on branches must
  then cover the revocable mode.

Next (session 5), in order:
1. §6, pure side (KVOutcomeOn/ApplyNormalOn/ApplyEntryOn): `kvShapedL_of_log` at `plainReqL lm` with `keysNonEmpty`
   (a leased put's/txn's lease keys `reqShape k []` from `keysNonEmpty_kvRaftOfOn`); `authOutL_of_kvOutL`/
   `outcomeOn_of_kvOutL` at `plainReqL lm` with the lease verdict (`KVAuthBridge.leaseOk_iff`) and `leaseExactL T`
   at `T = (appliedTableM true γr A).ids` (`appliedTableM_eq_model`, `pre = []`); `kv_entry_pre_on` at the mode
   (`plainEntryOn γk.lm`, no `plainCover`); `kvOn_after_kv`, `authTie_of_kvOutL` likewise.
2. §6, `applyEntryNormal.wp_proofOn` v3 = true: the KV arm consumes the dropped `leaseExactL` conjunct (`%HXo, -,
   #Hdel` → keep it); new grant arm (the off arm's `srvEver_applyPre`, `kv_entry_grantFresh`, `grantReqA_of_res`,
   at the mode's table) and revocation arm (S2's `LeaseRevoke.specL`, `revokeOwn`, `ltHalf`, `revokeRestA`; the
   KV side new: the lease's keys' deletions committed, Draft §6 r2 N4); the rest at `srvRestM true` (no
   `srvRestM_lg_false`).
3. The replay branch (v3 = false): `srvRestRpM true` at the mode's table; at `v3 = false` `kvEntryOn` keeps the
   table (`dispatchTable` with `v3 = false`).
4. Drop `γr.kv.lg = false` from `srvKVInvsOn` (KVApplyOn:401) and from its provers (`NewServerAllocOn`,
   `srvClusterBootOn_alloc`); fix the destructurings of its pure row (`Hrows.2.2.1` etc. shift: grep `srvKVInvsOn` in
   ReadOn, ApplyNormalOn, KVApplyOn, ServerOnDefs (`srvKVInvsM_rows`), AuthCompRows (`isServerC_lm`), ModeSpecs,
   ApplyAllSnap (`Hcmlg`), EtcdServer__run/apply, WatchSrv, MainServe).
5. The land-stop checks (below, "Build").


**Session 5 (2026-11-15): STOPPED at a finding (ledger 2026-11-15, "the latest track's certificate premise for a
leased put or transaction").** The KV branch of Draft §6 cannot be proved for an admitted leased put or leased
transaction: the latest triples' premise `certPreVW … (kvOutL …)` becomes, through `certPreW_inner`, the class track's
`certPre` over every `backendStep` outcome, and `backendStep` admits an applied put of a lease not live (and an applied
transaction without `PathsLeaseOk`), whose log `kvNxOn` cannot certify. Options in the ledger entry ((1) the certificate
at the live set `T`, recommended as its own reviewed change; (3) narrow S3a to no leased put/transaction). Waiting for
etcd-grove-81. Done this session (pure, option-independent, checked with `etc/lean-check.py -a`, not yet in a full
build): `leaseOk_of_leasePassedL`, `not_leaseOk_of_leaseRefusedL` (the bridge; no shape needed), `kvGrantedL_of_kvOutL`
(every authKV kind), `backendTable_kv`, `chainTable_kv`, `backendLog_of_step` (a KV request's backend outcome is
`backendLog` given `plainCover ∨ leaseExactL lt.ids`), `outcomeOn_of_kvOutLL` (at `plainReqL lm`), `revokeLog_eq_backendLog`
(`liveSt` + `0 ∉ ids`), `outcomeOn_of_kvOutL_revoke` (KVOutcomeOn); `leaseShapedL_of_keysNE`, `kvShapedL_of_logL` (no
`plainCover`; ApplyNormalOn). Not blocked by the finding, next whatever the decision: the grant arm and the revocation
arm of `applyEntryNormal.wp_proofOn` (a revocation's certificate is the model's: `outcomeOn_of_kvOutL_revoke`; it needs
`liveSt` of the model's state, `liveSt_kvRaftOfOn`, and `0 ∉` the table's ids, from `appliedTableM_ids_granted`-style
facts), then the replay branch. The row `γr.kv.lg = false` stays until the KV arm covers the revocable mode.

**Session 5, continued (2026-11-15): decided by etcd-grove-81, (3) now, then (1) as stage S3a2.** Done:
- Rev 7 (Draft §15, ledger decision): `plainReqL lm := plainReq` (`plainReqL_iff`); destructurings of the old
  disjunction fixed (KVAuthModel, KVOutcomeOn, SnapRecvOn, ImageLeasesOn, SnapAuthRecover). Commit `…rev 7`.
- `kv_entry_pre_on` at the mode (no transitional step; grants/revocations are no KV kind).
- `applyEntryNormal.wp_proofOn` at `srvRestM true` throughout (no `srvRestM_lg_false`): new `RestOn.lean`
  (`appliedTableM_true_snoc/_eq/_nonLease/_nodata`, `srvRestM_keep`, `srvRestM_nodata/_admin/_applyP/_applyP0`).
  The replay branch (v3 = false) is DONE at the lease mode: plain, grant and revocation entries all by
  `Apply.spec` (`plainOrCmpG_of_entryOn`, `revokeOwn_take`), at `srvRestRpM true`. Commit `fdd1d88b44`; checked
  with `etc/lean-check.py -a` (0 errors).
- What is LEFT of the transitional row: the two `exfalso` bullets in the v3 = true data branch of `wp_proofOn`
  (marked "TRANSITIONAL until the grant arm" / "… revocation arm"), and the row itself in `srvKVInvsOn`
  (KVApplyOn) with its docstring. `grep -rn TRANSITIONAL Proof` lists exactly these.

Full build GREEN at `fdd1d88b44` (`/shared/tmp/auth-lease-s3a/build14.log`, flock + 64G).

**Next (session 6), in order:**
1. The grant arm (v3 = true), modelled on the cluster-request branch (`hA`, `Apply.spec`, auth passes a grant
   through: not `authChecks`): `applyStep_grant`, `kvEntry_grant`; the table after is `kvTable` (the model's write
   branch: a grant is no `authKVKind`, no admin), so generalize the `tail_on` macro to take the table `lt'` (it
   hardcodes `kvLeasesOn γr.kv srvAuthSt0 A`; `kvApplied_nextOn` already takes any `lt'`); certificate: the log
   kept (a `kv_certPre_keep` for a grant: `apply.chainStep_grant_logAfter`); `srvEver_applyPre` with a new
   `kv_entry_grantFresh_on` (port of `kv_entry_grantFresh` over `kvInvOn`'s `kvGrantIds`); `srvGrantIf_permPG`;
   `grantReqA_of_res`; `srvRestM_applyG` (port of `srvRest_applyG`'s `lg = true` branch at the auth-on table,
   `appliedTableM_true_snoc` + the write branch giving `dispatchTable`); the result's not-NOSPACE at the auth chain
   (`applyResultIs_notNoSpace_grant` is at `alarmChain false …`: port); `authTie_nonKV`; `grantArM_of_resW`.
2. The revocation arm (v3 = true), modelled on the KV branch (`hK`, `kvSpecL`: `authKVKind .leaseRevoke`):
   certificate from `outcomeOn_of_kvOutL_revoke` (needs `liveSt` of the model state: with rev 7 the model's log has
   no leased key, `LogNoLease`, so `liveSt` is immediate; and `0 ∉` the table's ids: a `kvRaftOfOn` port of
   `kvTableOf_ne0`); `kvShapedL_of_logL` + `keysNonEmpty_kvRaftOfOn`; `revokeOwn_take`; the post's
   `revokeIdsA`/`revokeRestA` at the model's table after (refused at the latest state: kept; applied:
   `backendTable`'s filter; port `revokeA_table`/`srvRest_applyR` to the auth-on table); `revokeArM` from
   `revokeAnsRA` (`InvRequest.lean:2031`); not-NOSPACE (`applyResultIs_notNoSpace_revoke` at the auth chain);
   `authTie` of a revocation (check `authTie`'s kind guard).
3. Drop `γr.kv.lg = false` from `srvKVInvsOn` (KVApplyOn) and its provers (`NewServerAllocOn`,
   `srvClusterBootOn_alloc`); shift the destructurings (`Hrows.2.2.1` → `Hrows.2.1` etc.: grep `srvKVInvsOn` in
   ReadOn, ApplyNormalOn, KVApplyOn, ServerOnDefs `srvKVInvsM_rows`, AuthCompRows `isServerC_lm`, ModeSpecs,
   ApplyAllSnap `Hcmlg`, EtcdServer__run/apply/applyEntryNormal (`obtain ⟨-, -, hlmE, -⟩ := Hrows`, `Hrows'.2.2.1`),
   WatchSrv, MainServe).
4. The land-stop checks (merge lean, full build under flock + 64G, tcb 870/4, gen-interface with only Alloc3On.txt,
   bounds/mode, no closed statement changed, `grep -rn TRANSITIONAL` empty, STATUS/handoff/status-history). STOP
   before `etc/land.sh`.

**Session 6 (2026-11-15): S3a's proof DONE, at the land stop.** Commits `9c2f582bd1` (the grant and revocation
arms), `b2550e6a1d` (the transitional row dropped):
1. The grant arm (v3 = true): `apply.Apply.spec` (the auth layer passes a grant through), the log kept, the table
   the model's step (`kvEntryOn_grant`: the third branch of `kvEntryOn`, `dispatchTable` at the auth-on chain);
   `srvRestT_applyG` (`srvRest_applyG` at any table), `kv_entry_grantFresh_on`, `kv_certPre_grantOn`,
   `applyResultIs_notNoSpace_grantOn` (`dispatchStep_start_grantB`). All in `RestOn.lean`.
2. The revocation arm (v3 = true): the latest-state triple `kvSpecL` (the auth layer checks a revocation);
   `revokeOn_after` (refused: the model's table kept; applied: `backendTable`); the certificate
   `kv_certPreVW_revoke_on` over `outcomeOn_of_kvOutL_revoke` (`liveSt` from `kvInvOn_log0`, `0 ∉` the table by
   `kvRaftOfOn_ne0`); `kvShapedL_revoke` from `keysNonEmpty_kvRaftOfOn`; `srvRestT_applyR` with the refusal;
   `applyResultIs_notNoSpace_revokeOn` (the auth error told apart). The table after needs the empty raft prefix
   (`srvKVInvsOn`'s `pre = []`) to be the model's state the outcome met.
3. `γr.kv.lg = false` dropped from `srvKVInvsOn`; `acModesOk` on: `cmp = false` only (`srvKVInvsC`); NewServer no
   longer proves it. `grep -rn TRANSITIONAL` is empty. The local macro `tail_on` takes the table after the entry.
4. Land-stop checks (2026-11-15): lean not moved (`c3da59fa29` merged); full build GREEN under flock + 64G
   (`/shared/tmp/auth-lease-s3a/build15.log`, 17537 jobs); `tcb-report --check` 870 axioms, 4 sorries; every
   `etc/api` list's `gen-interface --check` passes, no interface differs from lean (the Alloc3On change is a
   proof body only); bounds ok (351); mode gate: S3a's findings classified (`model`: the auth-on table's rows;
   `unmoved`: `specSnapM`'s frozen `hnl`), baselines raised (etcdserver lit-mode 156→252, match-mode 76→78,
   client/v3 lit-mode 18→22; commit `4f34346b9e`); no closed theorem statement changed (the diff in
   `Proof/github_com` is proof bodies). STOPPED before `etc/land.sh`.

**Stage S3a2 (after S3a lands; its own Scope and Freeze; 3–6 agent-days; S3b's leased put waits on it).** Leased
puts and leased transactions in the auth-on apply thread (ledger 2026-11-15, option (1)). Freeze items:
- `certPreT E c rq log T` in place of the class track's `certPre` for KV requests: the certificate of the outcomes
  that are lease-exact at the live set `T` (`apply.leaseExactL T`), with the class track's `leasesLive` at `T`
  (`kvOwnAt E log T`, split at the top layer from the two `ltHalf`s);
- the backend's `Put`/`Txn` take the certificate only when the lease is live (today `applierV3backend__Put.lean:88-95`
  takes it before the lease check);
- the latest track's `X` gains `leaseExactL T` (`certPreW_inner`, `Apply.kvSpecL`, `uberKVC`,
  `uberApplier.Apply.kvSpecL`, `dispatch.kvSpecL`: the exported `apply_*_kv_latest` change);
- `plainReqL` widened back to Draft §1's text; §6's KV arm over `outcomeOn_of_kvOutLL` (session 5's lemmas:
  `backendLog_of_step`, `kvGrantedL_of_kvOutL`, `kvShapedL_of_logL`).

**S3a2 (2026-11-15, session 7): Draft and Probe.** Draft `notes/auth-lease-s3a2-draft.md` (rev 1, commit `fd412d310d`).
Probe `Scratch/S3a2Probe.lean` (untracked, checked with `etc/lean-check.py -a`, no `sorry`): `certPreT`, `mPreAt`,
`putPre`/`txnPre` bundling `∃ T, certPreT … T ∗ mPreAt … T`, the backend `Put` with the witness taken in the live
branch (`Put_wp_T`), the backend `Txn` over a strengthened `txn.Txn.specSole` wand (`Txn_wp_T`; finding: the wand
must be told `PathsLeaseOk L`, a frozen `Spec/` text), `certPreW_innerT`, `certPreW_tie`. Review rounds:
`/shared/tmp/auth-lease-s3a2/review-r*.md` (r1–r5; r3 found `authTie` false at a leased request → Draft §4a, option (b)
probed in `Scratch/S3a2ProbeTie.lean`; r5 no first-tier finding). Draft rev 6 = the Freeze package (commit
`cb5bf97093`), STOPPED for etcd-grove-81 (`questions.md`). Probes copied to `/shared/tmp/auth-lease-s3a2/`. Next after
the Freeze: Draft §7's order (step 1 `Chain.lean`). No Lean outside `Scratch/` edited yet.

**S3a2 Prove (2026-11-15, session 8): FROZEN at Draft rev 6 (etcd-grove-81; tag `auth-lease-s3a2-frozen`), proved.**
Commits after `42827e4060` (the Freeze record): `4453757bc6` (apply layer and server lemmas), `a1dff7fc97` (the KV arm),
then the build fixes. Done, by Draft §7's steps:
1. `Chain.lean`: `leasesLiveAt`, `certPreT` (+ `_of_certPre`, `_mono`, `_auth`, `_quota`, `_capped`), `mPreAt`,
   `mPre_iff_at`, `leasesLive_iff_at`; `putPre`/`txnPre` bundle `∃ T, certPreT … T ∗ mPreAt … T`. `mPre`, `leasesLive`,
   `kvOwnAt` keep their bodies (form: equivalent, the laws relate them). WriteLemmas: `mPreRestAt`, `mPreAt_split_chain`,
   `mPreAt_of_rest`, `mPreRest_of_at`, `mPreRestAt_lend`, `mPreAt_ltHalf`, `putPre_of_mPre`, `txnPre_of_mPre`. The backend
   `Put` (witness in the live branch) and `Txn` (from the probe), quota/capped/corrupt/auth, class `dispatch`.
2. `txn.Txn.specSole`'s wand told `PathsLeaseOk`; `txn/Txn.lean` passes `⟨Hign, Hlok⟩`; `txn_runTxn` keeps its text
   (`wand_weaken_told`); `TxnSpecs.lean`, `clients-txn.md` §8 noted.
3. Latest: `putPreW`/`txnPreW` bundle `∃ T` with `leaseExactL T`; `certPreW_innerT`, `certPreW_tie`; `kvOutLT` and the four
   triples (`dispatch.kvSpecL`, `uberApplier.Apply.kvSpecL`, `uberKVC`, `Apply.kvSpecL`); the dispatch's put/txn cases split
   `mPre` at its live set and tie it to `T` (`mPreAt_ltHalf`).
4. Server: `authTie st lb rq out` at `kvGrantedL` (option (b)); `plainReqL` back to rev 5's text (rev 7's
   `plainReqL_iff` gone); `kvCover` (KVModelDefs: `plainCover` without the lease conditions) carries the Draft's
   `leasedKV`: the lemmas that read only those facts are restated over it in place; `kv_certPreW_on`/`kv_entry_pre_on`
   at `kvOutLT` (the model's table); the KV arm of `wp_proofOn` over plain and leased requests (`kvOn_after_kv` at
   `plainReqL lm` with the dispatch post's `leaseExactL`; `hne` from `keysNonEmpty_kvRaftOfOn`); the replay branch over
   `plainOrCmpG ∨ kvCover`; the four exported results restated (Draft §4's table).
Forms: `questions.md`, "S3a2 Prove". §5 (literal modes): only `srvRestM_nodata`/`srvRestM_admin` and the table-keeping
lemmas (`appliedTableM_nonLease`, `appliedTableM_nodata`) moved to either mode; etcdserver lit-mode 252 → 251 (the KV arm's
certificate at the server's live set added three); the aim of 200 is NOT reached (Left, below).
Land-stop checks (2026-11-15): lean `b7e3cf342a` not moved (merged); full build GREEN under flock + 64G
(`/shared/tmp/auth-lease-s3a2/build4.log`, 17537 jobs); `tcb-report --check`, `gen-interface --check`, bounds (351),
mode (baseline ratcheted 252 → 251): see the session report; no file under `Proof/github_com` or `interface/` changed, the
one `Spec/` change is the approved txn wand; `grep TRANSITIONAL` empty. STOPPED before `etc/land.sh`.
Next: S3b (the proposers of a leased put with auth on; `grantedAt` → `kvGrantedL` via `kvGrantedL_of_tie`-style use of
`authTie`'s converse).

## S3b Prove (2026-11-15, session 9): FROZEN at Draft rev 3 (etcd-grove-81; tag `auth-lease-s3b-frozen`)

Decisions D1–D7 (`questions.md`, "S3b Freeze"; ledger 2026-11-15, S3b entries). Done (commits after `76a28d8669`):
1. `ReqOn`: `authTie st lb lt rq out` (guard `authKVKind`, the lease-exact disjunct), `resultIsWOn`/`entryWitOn` (+ `lt`),
   `resultΨOn` (`∃ … lt`), `modelOutM true`; `grantedAt_of_dispatched`, `grantedAt_of_applied` (at `authKVKind`),
   `modelOutM_true_table`, `chainStep_applied_backend`, `leaseLive_of_tie` (D3), `txnLeaseLive_of_tie` (D7),
   `pathLeaseOk_of_plain`/`txnPathsLeaseOk_of_plain`; `grantedRes_applied`/`putQhOn_res`/`txnQhOn_res` return the model's
   table; `putPermitOn`/`txnPermitOn`/`txnPermitM` widened; `rqShape_put`/`rqShape_txnL`/`rqShape_grant`/`rqShape_revoke`;
   `reqPropOkM_true_writeL`.
2. `ProposeOn`: `grantedAt` at `kvGrantedL` (D2), `grantedAt_iff` restated, `grantedAt_kvGranted`, `grantedAt_plain`,
   `grantedAt_grant`, `writeGrantG_granted`; `reqPropOkOn`'s write form at `writePropOk lm` (`plainReqL ∨ grantPropOk ∨
   revokePropOk`), `rqShape lm`, `grantIdOwn`; `kv_prop_au_on`'s write branch (`commitOkOn_L`, `kvGrantIds_snoc`, a grant
   never refused).
3. New `LeaseReqOn.lean`: `leaseGrantPermitM`/`leaseRevokePermitM` (+ `_false`/`_true`/`_mono`), `grantQhOn`/`revokeQhOn`,
   `leaseGrantPermit_reqPropOk`/`leaseRevokePermit_reqPropOk`, `leaseGrantResM`/`leaseRevokeResM` (+ laws),
   `leaseGrantedRespAt`, `leaseGrantedResp_iff_at`, `leaseGrantResM_true_id`, `authedOutB_ctx`. `InvProposer`:
   `irrLeaseGrant`, `irrLeaseRevoke`.
4. `ApplyNormalOn`: `authTie_of_kvOutL` (+ `lt`, `hex`), `leaseExact_revoke`, `authTie_nonAuthKV`; the apply arms of
   `applyEntryNormal.wp_proofOn` (KV arm's `hex` from `HXL`, the revocation arm by `authTie_of_kvOutL`, the others
   vacuous); `processInternalRaftRequestOnce` destructures the table.
5. Specs: `Put.spec` (D3), `LeaseGrant.spec`, `LeaseRevoke.spec` (both at `isServerReqM E.authOn`, the permit, `authedOutB`,
   the result), `txnAppliedOk` (D7), `srvGrantsLeases`/`srvRevokesLeases` (auth-off conjunct dropped); proofs: `Put`, `Txn`,
   `DeleteRange`, `LeaseGrant`, `LeaseRevoke` (a mode split after `requireAuthInfo`, whose error is returned with auth on).
6. Callers: `revokeExpiredLeases` (off permit), v3rpc `ServerLeaseGrant`/`ServerLeaseRevoke` (off instance by
   `isServerReq_authOn`), `ServerKVOn` (`putPermitM_of_dep`/`txnPermitM_of_dep` left disjuncts; the extra conjuncts dropped),
   etcdstart `ServedLease`, `WorkAuth` (`grantedAt_kvGranted`). SpecPlan's `LeaseGrant`/`LeaseRevoke`/`Put` checked: an
   opaque-vocabulary statement S3b moves toward (the client's update fired at the commit); no defect found.
7. Land-stop checks (2026-11-15): lean `7d9d727fba` merged (two merges: restart3 A1 and restart3-c); full build GREEN
   under flock + 64G (`/shared/tmp/auth-lease-s3b/build4.log`, 17545 jobs); `tcb-report --check` 870 axioms, 4 sorries;
   `gen-interface --check` passes on every `etc/api` list (no `interface/` file changed); bounds ok (351); mode gate:
   the four new mode-indexed rows classified `model`, three LeaseReqOn lemmas `unmoved`, baselines raised (etcdserver
   lit-mode 251→278, match-mode 78→82: the specs' `hdrBoundM`/`pubAfterM` flags, the permits' and results' bridges,
   ReqOn's three new auth-on lemmas), for etcd-grove-81; no closed theorem statement changed (the diff under
   `Proof/github_com` is two proof bodies: `WorkAuth.lean:330`, `ServedLease.lean:263, 321`). STOPPED before
   `etc/land.sh`.

## S3c Draft (2026-11-15, session 10)

Draft `notes/auth-lease-s3c-draft.md` (rev 1, commit `64326e6fff`); probe `Scratch/S3cProbe.lean` (untracked; copy
`/shared/tmp/auth-lease-s3c/S3cProbe.lean`, clean: the guard C1, run's expiry arm, the new `bootCfg` and its laws,
`NewServer`/`NewServerR`'s guard). Reviews `/shared/tmp/auth-lease-s3c/review-r*.md`. Rev 2–4 applied rounds 1–3 (each had first-tier findings: C2→C2′, the quota wrapper's metadata spec, C5′ pair, `srvAuthAt_of_viewsM`, the registration lemma from `grpcServerAt` in client/v3, the two trusted docstrings' wording); rev 4 = commit `a5f0e9223b`; round 4 (§1–§6 clean; three first-tier in §7: `grpcUpOn`'s Lease conjunct, the exported mode corollaries, the quota server's revoke) applied as rev 5 = `9ce15e1837`. **Next: review round 5 on rev 5** (a fresh `spec-reviewer`, brief as round 4's), then the Freeze package. Session 10 stopped on context. Decisions asked: C1 (the guard
carries `on → leasesNoExpiry`; `run` has `runCfg`, not `bootCfg`), the hub change (`bootCfg`'s row, Scope text), C2
(`srvInvAt` drops `on`), C3 (`acLessor` deleted), C4 (auth-on lease registrations as an `Md` set), C5 (`…M` contracts
beside the off ones), the `NewLessor` docstring wording (§6). No Lean outside `Scratch/` edited.

## S3c Prove (2026-11-15, session 11): FROZEN at Draft rev 6 (tag `auth-lease-s3c-frozen`)

Round 5 (`/shared/tmp/auth-lease-s3c/review-r5.md`) found no first-tier problem; etcd-grove-81's conditional decisions are in
force (`questions.md`, "S3c Freeze"); ledger entry 2026-11-15 "auth on implies no lease granted". Done (commits
`334a059cef`, `e08989808d`, `28abd867e1`, after lean `2dbf6503cc` merged):
1. **Couplings (§1–§5):** C1 guard `srvGrantGuard := ⌜lg = true ∧ (on = true → leasesNoExpiry)⌝`, `srvGrantGuard_expired`
   restated, `srvGrantGuard_expired_off` new, `_false` deleted; `lease.bootCfg`'s row `on = true → m = .revocable →
   leasesNoExpiry` (hub), `bootCfg_mono` without `hon`, `bootCfg_auth` → `bootCfg_noExpiry`, `bootCfg_of_run`'s `hon`;
   `lease.srvInvAt` without `srvLessorNil` (C2′: `on` unused), `_lessorNil` laws deleted; `srvLessorNil`, `srvLessorNilM`,
   `lookupNil_of_guard`, `apply.lookupNil`, `acLessor` (C3 a) and their conjuncts deleted (apply specs, `srvUberOn`,
   `srv_uberKVL(_on)`, server `Results`' `server_uber_kvl(_on)`, `Start`/`start`/`applyAll.spec`, `isServerRunC`,
   `run_job_body`, `isServerBuilt_offC`); `revokeExpiredLeases.spec` takes `E.authOn = false`; `run`'s expiry arm from
   `srvGrantGuard_expired_off`; `NewServer`'s guard by `bootCfg_noExpiry`; the mode-allow line `::srvLessorNilM::` gone.
2. **C6:** `srvClusterBootOn_alloc` (+ `server_cluster_alloc_on`) takes `lm`/`gp`/`gps`/`hgps` (defaults), post `γk.lm = lm ∧
   γk.ids.pfx = gp ∧ γk.gps = gps`; `MainAlloc`/`Alloc3On` derive `lg = false`.
3. **§6 trusted docstrings** exactly as decided (`NewLessor.lean`, `LessorBackend.lean`); other docstrings restated.
4. **D6, server and v3rpc layer:** new `v3rpc/LeaseOn.lean` (`leaseGrantResT`/`leaseRevokeResT`, `lessorGrantOkGM`/`lessorGrantOkM`/
   `lessorRevokeOkM`/`raftLessorM`, `_false` bridges, `leaseGrantResT_true`/`leaseRevokeResT_true`, `lessorGrantOkGM_mono`);
   `lessorGrantOkLive_of_server`/`lessorRevokeOk_of_server` at `isServerReqM E.authOn` and the `…M` contract, with `_off`
   corollaries (form: the off discharges' texts kept under new names, used by `lessorGrantOkL_of_server` and v3rpc `Results`'
   unchanged `lessorGrantOkLive_server`/`lessorRevokeOk_server`); new exported `lessorGrantOkLiveM_server`, `lessorRevokeOkM_server`;
   `LeaseServer.LeaseGrant.spec`/`.LeaseRevoke.spec` at `on`, `ρ`, `Q`, the permit, the result (revoke narrowed to
   `lessorRevokeOkM`); `quotaLeaseServer.LeaseGrant.spec` metadata-indexed (`grpcHandlerOwnOkMd`, error clause);
   `quotaLease_grantHandlerOkMd_of` (plain `_of` its corollary), `quotaLease_revokeHandlerOkMd`; `srvAuthAt_of_viewsM` in
   **`ReadOn.lean`** (form: `AuthGuard.lean`, the Draft's place, is imported by `ReqOn`/`ReadOn`, a cycle); client off callers
   (`LeaseGrantServed.lean:142`, client `Results` `:3806`, `:3861`) at `on := false` with `ρ := ⟨γr.kv.st, γr⟩` (any wait name).

**Checks (2026-11-15):** full build GREEN (`/shared/tmp/auth-lease-s3c/build3.log`, flock + 64G, 17546 jobs);
`tcb-report --check` 870 axioms, 4 sorries (matches lean's baseline); bounds ok (351); mode gate: every finding classified
(the C5′ `pair` line, the client's auth-off callers as `bridge`), `gen-interface --check` passes on every `etc/api` list; baselines to raise for etcd-grove-81: v3rpc lit-mode 21→33
(the `…M` contracts' `_false`/`_true` bridges and the discharges' `hdrBoundM true` flags), client/v3 lit-mode 22→23; etcdserver
lit-mode 278→276, match-mode 82→81 (decreases); closed examples: proof bodies only (`auth/startServer`, `auth3/startMember`,
`auth/MainAlloc`, `etcdstart/{Alloc3On,Start,StartStop}`).

**Session 12 (2026-11-15): S3c's Prove finished** (lean `fa4909047e` merged, clean; commit `c15150ec34` and the
land-stop commit):
1. client/v3: `etcdLeaseGrantSpecOn`/`etcdLeaseRevokeSpecOn` and the handler lemmas `etcdLeaseGrantHandlerOkMd`/
   `etcdLeaseRevokeHandlerOkMd` in `LeaseGrantServed.lean` (form: not `KVServiceOn.lean`, which does not import the
   lease modules; the handler lemmas mode-generic, at `E.authOn`, no `hγa`: no literal mode); `etcdLeaseMethodsOn` and
   `etcd_lease_auth_served_on` in `AuthnServedOn.lean` (the Draft §7.3 statement; the lessor contracts at
   `S := etcdKVSlot s E γr`, the run slot `etcdGrpcSlot`); `etcd_leaseGrantMethodOkMd`/`etcd_leaseRevokeMethodOkMd` (client
   `Results.lean`, the plain revoke one now their corollary).
2. `Spec/…/etcdserverpb/_Lease_LeaseRevoke_Handler.lean` at the metadata form (`GrpcSpecMd`, `grpcHandlerOkMd`, `Ψe`;
   proof `wp_unaryHandlerMd`), as `LeaseGrant`'s and `Range`'s: the auth-on revoke spec reads the run's metadata (form:
   a stronger internal spec, its one caller adapted).
3. etcdstart: `grpcUpOn` gains `grpcLeaseUp s C.A regs`; `grpcUpM_true` keeps it (`leaseServerAt_revR`); the closed
   examples' destructurings (`auth/Run.lean`, `auth3/run.lean`, proof bodies).
4. r5 S5 applied (decided by etcd-grove-81): `leasesNoExpiry`'s docstring names `NewServer` and `NewServerR`.
5. Land-stop checks: see the report / STATUS entry.

**Left (after S3c):** S4 (client library, read handlers at auth on, `memberBootOn`'s `lg = false`, the closed
theorem); the cleanup stage (the C5′ pair, the literal modes).

## Pitfalls

- `kvStOn` is `@[reducible]` but `rw` does not see through it: write `kvStateOf (kvModelOn …) (kvLeasesOn …)`
  in goals that are rewritten.
- In an Iris proof, `cases hon : E.authOn` rewrites the goal but not the Iris context (an `iexact` of a hypothesis at
  `E.authOn` then fails at `false`): split with `by_cases hon : E.authOn = true` and rewrite where needed.
- `srvRestM false E γr A` is `srvRest E γr A` by `rfl` but `iexact` does not unify them (a `match` on the mode):
  `rw [srvRestM_false]` first.
- With `apply.DispatchKVL` imported, `and_false` can be ambiguous in `simp only` (`BI.and_false`): use
  `_root_.and_false`.

- The latest-state refusal must be stated in `refusedL`'s form (`leaseRefusedL`), not `¬ leasePassedL`:
  `latestOk` is vacuous at `hs = []` and in mode `any`.
- `isAuthStoreL`'s admin clause gives only the latest verdict; the lease class (`leaseKeysClass`'s
  admin disjunct) needs a recorded state: the probe adds `□ ∀ hs, L hs -∗ L hs ∗ auth.latestSnap M hs`
  (real store: `latestResC_snap`).
- The model's refusal guard `isKVKind` excludes `.leaseRevoke`: the triple-state model's guard must
  add it (`authKVKind`), or a refused revocation is applied.
- `txn.putsW`, `lease.keysOf`, `kvGrantedPerm` (Scope Draft names) do not exist; the probe defines
  `putsW` (mutual `opPuts`/`opsPuts`) and states key sets over `I.lookup ⟨k⟩ = some id`.

## Build

Targeted: `systemd-run --scope -q -p MemoryMax=64G lake --packages=/shared/tmp/manifest-ddc.json build
<modules>`; check: `LAKE_OPTS=--packages=/shared/tmp/manifest-ddc.json etc/lean-check.py FILE`. Full builds
under `flock /shared/tmp/etcd-grove-build.lock`. `TMPDIR=/shared/tmp`.

## Left (follow-ups)

- **The auth-on lease table's literal modes** (mode-gate raise accepted by etcd-grove-81, 2026-11-15): S3a raised the
  mode baselines (etcdserver lit-mode 156→252, match-mode 76→78, client/v3 lit-mode 18→22) with `appliedTableM true`,
  `srvRestM true`, `srvRestRM true`, `srvRestRpM true`, `kvModelM`/`kvStM` at literals; S3a2 should try to reduce the
  literal-`true` uses (state the auth-on arms' lemmas at `srvRestT` and the slot's `C.isOn`).

- **The literal-mode count is growing** (decided by etcd-grove-81, 2026-11-15: S3b's raise accepted, etcdserver lit-mode
  251→278, match-mode 78→82, the lease permits' and results' flags and bridges and three auth-on lemmas): reducing the
  literal-mode uses (below) is due before the count grows further.
- **S3a2 §5 not reached** (lit-mode 251, aim 200): the remaining literal uses are the auth-on arms of
  `applyEntryNormal.wp_proofOn`/`apply.wp_proofOn` (classified `unmoved`/`model`), `RestOn`'s lemmas true only of the
  auth-on table (`appliedTableM_true_*`, `srvRestM_keep`, `srvRestM_applyP0`/`_applyP`, which read the model's table) and
  `ReqOn`/`ReadOn`'s `…M true` rows; moving them means stating `RestOn`'s lemmas over `srvRestT` at any table with the
  entry's step as a premise (Draft §5's plan), a refactor of its own.
- **The empty-prefix fact ties the auth-on server to fresh starts** (S3a rev 5, `srvKVInvsOn`'s `γr.raft.pre = []`):
  an auth-on restart (future work) has to revisit it (the model's table folds over the applied entries, `srvRest`'s
  over the raft prefix and them).
- A revocable auth-on cluster's snapshots: carried by S3a §5 (the image's table, `keysLeasesLive`).
