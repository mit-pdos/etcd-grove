# revoke-open: discharging `srvRevokeOpen_open`, the gated `sorry` of lease expiry

Phase: **Draft, pass 1** (step A written 2026-11-06: "Draft pass 1" below; the Scope approved as
recommended, Q1 (a2), Q2 K = 4, Q3–Q8, Q10, Q11, by etcd-grove-82 under the user's delegation,
2026-11-06). Scope: drafted read-only on branch `revoke-open` = lean `aa4449beb6`; nothing edited or
built). It replaces the parked candidate in `notes/lease-expiry-plan.md`, "Scope candidate:
discharging `srvRevokeOpen_open`" (2026-11-05), which this Scope re-checks against today's lean
(after S2–S4, lease-mono3 and R2c) in §9. A hard stop: the user's Scope.

What it does: proves `EtcdServer.revokeExpiredLeases` (`server.go:860-905`, run's expiry arm) and
passes the proof in place of `srvRevokeOpen_open` (`EtcdServer__run.lean:283`) in
`leaseexpiry/MainLinked.lean:54`. The trust base goes from 3 `sorry`s to 2. Perennial: P1 (thread
tokens by level, `84d538063`) is already lean's pin; no Perennial change is needed.

## Scope (2026-11-06)

### 0. The Go code (unchanged from the parked design's reading)

`revokeExpiredLeases` `GoAttach`es an *outer* goroutine: `lg := s.Logger()` (`lgMu` read lock),
`s.ensureLeadership()` (an axiom: `lgMu`, `read.mux`, a thread token), then per lease a send on the
semaphore `c` (capacity `maxPendingRevokes = 16`, or `<-s.stopping`: return) and a `GoAttach` of an
*inner* goroutine: `s.authStore.WithRoot(s.ctx)` (`enabledMu` read lock: `E.RD`), `s.LeaseRevoke`
(`leadTimeMu`, `E.RD`, no thread token), `leaseExpired.Inc()` or `lg.Warn(...)`, `<-c`. `GoAttach`
holds `wgMu`'s read lock across `wg.Add(1)` and the `go` statement, and calls `s.Logger()` in its
stopped branch. No bug: nothing panics for non-nil leases; a skipped inner `GoAttach` leaves `c`
full but the outer's `select` exits on `stopping`. Nothing for `issues/`.

Rounds overlap without bound (each tick starts one; an inner goroutine may block as far as the
proof sees), so every reader slot the expiry goroutines use must come from a pool backed by thread
tokens (`threadPool.isThreadPoolL`, at least `threadBound GF − 1` copies), borrowed with a level
token: the goroutines of `s.wg` hold their token's levels from 1 only (level 0 is in the wait group).

### 1. Where `threadBound` is fixed (the open point)

- **Perennial** guarantees only `1 < threadBound GF` (`Threads.lean:83`, `ThreadGS.threadBound_gt`).
  A thread token is one token per level `l < threadBound GF`; `threadToksFrom l = emp` for
  `l ≥ threadBound` (`threadToksFrom_of_le`, `Threads.lean:362`), so a design using level `l` needs
  `l < threadBound GF` wherever it splits `levelTok l` off.
- **The trust boundary** `goose_adequacy_start` (`Proof/runtime/Start.lean:103`) takes `T` as a
  parameter: the WP proof gets `threadBound GF = T`, and the execution must satisfy
  `RealThreadsBelow T n` (`Perennial/GooseLang/BoundedLang.lean:246`: every prefix of the `n`-step
  run has fewer than `T` threads), which is monotone in `T`.
- **The choice `T = n + 2`** is made once per adequacy lemma, from `realThreadsBelow_of_one`
  (`Proof/runtime/Threads.lean:60`): `etcd_adequate` (`etcdstart/Adequacy.lean:201,208`),
  `etcd_adequate_alloc` (`:154,163`), `etcd_adequate_members`/`etcd_adequate_alloc_members`
  (`AdequacyMembers.lean:60,87`, through the former), `k8s_etcd3_adequate` (direct,
  `k8s/etcd3/Adequacy.lean:146`), and the non-server `init_adequate` (`Adequacy.lean:115`),
  `init_adequate_start` (`AdequacyStart.lean:52`), `durable_init_adequate` (`DurableExt.lean:98`).
  Their `Hprog` premise is stated at `threadBound GF = n + 2`.
- **The closed theorems' premise on it** is the execution length, `Hn : n + 2 ≤ 2 ^ 28`, and each
  proof derives its `Main.spec`'s `threadBound GF ≤ 2 ^ 28` by `(by rw [HT]; omega)` (23 sites). No
  closed theorem mentions `threadBound`. The server specs below the `Main`s take only upper bounds
  (`≤ 2 ^ 28` in `isServer`, `≤ 2 ^ 30 − 1`, `≤ 2 ^ 31`, `≤ backend.rdPoolN`, pool sizes
  `threadBound ≤ n + 1`); no proof relates `threadBound` to `receiptBound` or to `n`.
- **The closed theorems through the etcd lemmas** (statement `Hn : n + 2 ≤ 2 ^ 28`):
  `etcd_cache_adequate`, `etcd_compacted_adequate`, `etcd_compactwatch_adequate`,
  `etcd_lease_adequate`, `etcd_leasecatchup_adequate`, `etcd_leaseexpiry_adequate`,
  `etcd_leasegrant_adequate`, `etcd_partition_adequate`, `etcd_partition_watch_adequate`,
  `etcd_putget_adequate`, `etcd_putget3_adequate`, `etcd_txnlin_adequate`, `etcd_watch_adequate`,
  `k8s_compactor_adequate`, `k8s_compactor_partition_adequate` (15), and `k8s_etcd3_adequate`
  (direct); with their `Results.lean` restatements (`*_safe`).
- **The over-count lemma** (`ThreadTokensTest.lean:64`: `threadToks n ∗ threadFuel t ∗
  levelToks 0 m ⊢ ⌜n + t + m < threadBound GF⌝`) and `threadToks_lt`/`levelToks_lt` are used only
  toward upper bounds (`k < T ≤ 2 ^ 31`); a larger `T` weakens what they give, never falsifies a
  proof's use. No bounds premise (`receiptBound ≤ 2 ^ 48`, `receiptBound ≤ N + 1`,
  `threadBound ≤ actualMaxReaders`, `≤ rdPoolN`, the pools' `threadBound ≤ n + 1`) breaks for a `T`
  that is still `≤ 2 ^ 28`.

### Q1. Where the lower bound on `threadBound` comes from

The design (Q2) needs `K ≤ threadBound GF` with `K = 4` inside `revokeExpiredLeases`'s proof only.

- **(a1) `T = n + K` in the etcd adequacy lemmas.** Every one of the 16 closed theorems' `Hn`
  becomes `n + K ≤ 2 ^ 28` (a weakening, however small, of every top-level result and of its
  `Results` restatement), and their docstrings. Hard stop on 16 top-level statements for nothing the
  others use. Rejected.
- **(a2) `T = max (n + 2) K` in the four etcd adequacy lemmas** (`etcd_adequate`,
  `etcd_adequate_alloc`, `etcd_adequate_members`, `etcd_adequate_alloc_members`): `Hprog`'s
  `threadBound GF = n + 2` becomes `threadBound GF = max (n + 2) K`; the proofs pass
  `RealThreadsBelow (max (n + 2) K) n` from a new pure lemma beside `realThreadsBelow_of_one`
  (`Proof/runtime/Threads.lean`, monotonicity in `T`; optionally offered to Perennial as
  `RealThreadsBelow.mono`, not needed). **No closed theorem's statement changes**: `max (n + 2) 4 ≤
  2 ^ 28` follows from `n + 2 ≤ 2 ^ 28`, and the 23 `(by rw [HT]; omega)` go through unchanged
  (`omega` rewrites `max`, `Lean/Elab/Tactic/Omega/Frontend.lean:216,288`). What changes: the four
  lemmas' statements (etcdstart's API: `interface/.../etcdstart/Adequacy.txt`,
  `AdequacyMembers.txt`; a request to etcd-grove-82, whose hub step 7 made them), their
  docstrings and the closed theorems' docstrings ("the thread bound `n + 2`"). The non-server lemmas
  (`init_adequate`, `init_adequate_start`, `durable_init_adequate`) and `k8s_etcd3_adequate` stay at
  `n + 2` (or move for uniformity: free, not needed). It is bounds-plan rule 1 (the adequacy theorem
  fixes the constants once). Trust: none. Build: `etcdstart/Adequacy.lean` has 54 importers (7.3k
  lines), `AdequacyMembers.lean` 28, `Proof/runtime/Threads.lean` 57.
  - **Confined, not global**: the bound must reach only the expiry proof. It rides on the revocable
    run configuration, which only leaseexpiry builds: `lease.runCfg`'s revocable arm
    (`LeaseRun.lean:78`) becomes `m = .revocable → srvRevokeLevels ∧ srvRevokeOpen`, where
    `srvRevokeLevels : Prop := 4 ≤ threadBound GF` is named in the owner (`LeaseRun`, beside the
    level layout's docstring; a named Prop, so no spec between the adequacy and the owner spells
    `threadBound`); `lease.runCfg_revocable` takes it; `run` hands it to `revokeExpiredLeases.spec`
    (a premise, Q8). leaseexpiry's `Main.spec` takes `srvRevokeLevels` (or `4 ≤ threadBound GF`) and
    its closed theorem's proof gives it from `HT`. cluster3 excludes the revocable mode
    (`lm ≠ .revocable`), so lease-mono3 is untouched.
  - **Global** (rejected): the bound in `isServer`/`NewServer.spec*` would reach every hub start
    spec (`StartServer`, `StartMember`, `newServerMode`, cluster3's), every example `Main.spec`
    (15) and their callers: `Spec/.../NewServer.lean` alone has 478 importers. It is forced only if
    a shared pool sits at a level `≥ 2` (Q3).
- **(b) Fewer levels, so that no bound is needed.** Not possible: the outer goroutine holds levels
  `≥ 1` only, and at `GoAttach` it holds a `wgMu` slot while giving a level to `wg.Add`'s pending
  token, so it needs two levels `≥ 1`; at `ensureLeadership` it holds `lgMu`, `read.mux` and the
  axiom's token: three (level 3, so `K = 4`; `K = 3` if the axiom took no token, Q5). Even a pending
  backed by a pool loan instead of a level token leaves `GoAttach`'s stopped branch holding `wgMu`
  and `lgMu` at once. So (b) lowers `K` (from the parked 8 to 4) but cannot remove the bound; it is
  Q2, and it is what makes the confined form possible.
- **(c1) `T` as a parameter of the etcd lemmas** (`(T) (hT : n + 2 ≤ T)`, `Hprog` at `threadBound
  GF = T`): closed statements unchanged, but each of the 19 closed proofs passes its `T`, and the
  constant is chosen per example instead of once. More churn than (a2) for no gain.
- **(c2) Raise Perennial's `threadBound_gt`**: a Perennial change shaped by one proof, which breaks
  every Perennial user's `T = n + 2` (CLAUDE.md, "Changes to Perennial"). Rejected.
- **(c3) A class `ThreadBoundGe GF k`** (the twin of `ThreadBoundLe`, `ProgramLogic/Bounds.lean:40`):
  cosmetic; a general Perennial addition if wanted later, not needed here.
- **(c4) Derive `K ≤ threadBound` from held tokens** (`threadToks n ⊢ n < T`) inside `Main`'s
  proof: no point of the proof holds 3 whole tokens at once. Rejected.

**Recommendation: (a2), confined, `K = 4`.** Statements touched: the four etcd adequacy lemmas
(exported, etcdstart), `lease.runCfg`'s revocable arm and `lease.runCfg_revocable`, leaseexpiry's
`Main.spec` (+1 premise, frozen at `lease-expiry-frozen`), `revokeExpiredLeases.spec` (+1 premise).
No closed theorem's statement.

### Q2. The level layout

- **(i) The parked layout**: one pool per lock, one level each, levels 0–7 (`wgMu` 3, `lgMu` 2,
  `read.mux` 4, `leadTimeMu` 5, `E.RD` 6, `ensureLeadership` 7). It needs `K = 8`, and its `lgMu`
  pool at level 2 is the transport's shared `raftPool`, which forces the bound global (Q3).
- **(ii) Compressed and confined (recommended):**

  | level | what | who |
  |---|---|---|
  | 0 | a started goroutine's slot in `s.wg` | every `GoAttach` goroutine |
  | 1 | `wg.Add`'s pending token; the `lgMu` pool (the transport's `raftPool`, shared); the inner pool `I` = `leadTimeMu` ∗ `E.RD` | every `GoAttach` caller; rafthttp's peers; `GoAttach`'s stopped branch; the outer's `Logger()`/`ensureLeadership`; the inner goroutine |
  | 2 | the outer pool `B` = `wgMu` ∗ `read.mux` | `run`'s call (the outer `GoAttach`), the outer goroutine |
  | 3 | `ensureLeadership`'s token | the outer goroutine |

  Levels 0 and 1 exist at every `threadBound > 1`, so every shared protocol (`s.wg`, `raftPool`,
  `GoAttach`) needs no new premise; levels 2–3 are split off only inside `revokeExpiredLeases`'s
  proof (`threadTokFrom_succ`, `2, 3 < threadBound` from `srvRevokeLevels`). Pools are built at any
  level without a premise (`initL`: `threadBound ≤ n + 1` only).
- **(iii) `K = 3`**: as (ii), `ensureLeadership` taking no token (Q5 (b)). No closed-theorem
  difference; it changes the axiom's faithfulness argument for nothing.

**Recommendation: (ii).** Two new pools instead of five (bundled by role: what a goroutine holds
together is one pool item), `K = 4`.

### Q3. `lgMu`: the shared pool's level, and `GoAttach`'s logger slot

The `lgMu` stock left after `httpProcSlots` (2^29) and `raftPool` (2^28) is about 2^28 − 70
(`NewServer.lean:572-589`), short of a pool's 2^28 − 1: the expiry goroutines must share
`raftPool` (`rafthttp/Net.lean:262`, `R = srvLgReader s`, built at `NewServer.lean:589`; consumers
`startPeer` and `Transport.Start.spec`, all proved; rafthttp has no `etc/api` list).

- **(i) `raftPool` leveled at 1, and `GoAttach.spec` drops `srvLgReader s` (recommended).**
  `raftPool R := ∃ γ, isThreadPoolL raftPoolN 1 γ R`; `raftPool_borrow`/`raftLoan_giveBack` keep
  their statements (`threadTok` in and out, `raftLoan` keeping the levels not lent); new
  `raftPool_borrowL`/`giveBackL` for a holder of `levelTok 1`. `GoAttach`'s stopped branch borrows
  `lgMu` with the caller's `levelTok 1`, which is idle there (no `Add`); its handle comes in
  `srvGoAttachOk` (body + `raftPool (srvLgReader s)`, from `NewServer`'s `#HrPool` through
  `srvRevokeBuilt`, Q7). Callers holding a counted `srvLgReader` frame it (the derived
  `wp_GoAttach_tok`, Q4). No frozen, exported or trusted text; about 70–90 lines; `Net.lean` has
  1222 importers.
- **(ii) `raftPool` at level 2, `GoAttach` keeping `srvLgReader`** (the parked design): the
  outer goroutine cannot hold `lgMu` at level 1 while `Add` takes level 1, so the pool must be at a
  level `≥ 2`; then rafthttp's borrowers need `2 < threadBound`, from `NewServer`: the global form
  of Q1. Rejected.
- **(iii) Shrink `httpProcSlots`**: strengthens the trusted `Serve_spec` (`Boundary.lean:571`).
  Rejected (as the probe did).

**Recommendation: (i).** A correction of the parked design, whose probe noted the gap ("route
(i)'s level needs the same") without resolving it.

### Q4. `GoAttach.spec` and the leveled `s.wg` (after H2)

Today (`Spec/.../EtcdServer__GoAttach.lean`, H2 2026-11-05): pre `srvGoResAt s γ ∗ srvLgReader s ∗
P ∗ {{P ∗ goRunning γ}} f() {{goRunning γ}}`, post `srvGoResAt s γ ∗ srvLgReader s`; `f` runs with
no thread token (the caller's is in `goAttachInv`, `InvGoAttach.lean:104`).

```lean
abbrev EtcdServer.GoAttach.spec : Prop :=
  ∀ (s : Loc) (γ : GoNames) (f : GoFunc) (P : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvWgReaderAt s γ ∗ levelTok 1 ∗ P ∗
      {{ P ∗ goRunning γ ∗ threadTokFrom 1 }} (App (Val #f) (Val #()))
        {{ RET #(); goRunning γ ∗ threadTokFrom 1 }} }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"GoAttach")) (Val #f))
  {{ RET #(); srvWgReaderAt s γ ∗ levelTok 1 }}
```

- `goAttachInv`: `threadToks k` becomes `levelToks 0 d ∗ levelToks 1 q` with the counter
  `sint.nat ctr = d + q` (started + pending), H2's receipts' authority over the `d` started
  (`ownTokAuthDfrac γ.run dq d`, `goWaited` as today). `Add` deposits `levelTok 1` as pending; the
  `go` statement (`wp_fork_tok_upd`) puts the fresh token's level 0 in a slot, returns the pending
  `levelTok 1` to the caller and gives `f` the fresh `threadTokFrom 1`; `Done` hands back a level 0.
  `sync.tokJoinL` cannot be reused (its `ownAdder` is exclusive; `GoAttach`'s adders are concurrent
  `wgMu` readers): the same argument, re-proved in `goAttachInv`.
- `srvGoAttachOk` (`InvGoAttach.lean:116`): `⌜threadBound GF ≤ 2 ^ 31⌝` → `⌜2 * threadBound GF ≤
  2 ^ 31⌝` (from `isServer`'s `≤ 2 ^ 28`), + `raftPool (srvLgReader s)` (Q3).
- **(i) One spec, a derived lemma (recommended).** `wp_GoAttach_tok` (`InvGoAttach.lean`), stated
  as today's triple text, from the new spec: split `threadTok = levelTok 0 ∗ levelTok 1 ∗
  threadTokFrom 2` (`threadTokFrom_succ`, only `1 < threadBound`), frame `srvLgReader s`, frame
  `threadTokFrom 1` through `f`. The six callers (`Start`, `applyEntryNormal` ×3, `sendMergedSnap`,
  v3rpc's `monitorLeader`) apply it; their proofs and statements are unchanged. Not a second spec:
  one `GoAttach.spec`, one lemma about it.
- **(ii) Keep today's spec and add a leveled one**: a second spec of one function, the escalation
  trigger. Rejected.

API change: `GoAttach.spec` (no `interface/` for etcdserver; a diff to review). About 300–350
lines with `goAttachInv`; `InvGoAttach.lean` has 961 importers (188k lines), the spec 405.

### Q5. `ensureLeadership`'s axiom

Today (`Spec/.../EtcdServer__ensureLeadership.lean:44-49`): `srvLgReader s ∗ srvReadReader s γr ∗
threadTok ∗ ⌜threadBound GF ≤ 2 ^ 30 − 1⌝`, all but the bound returned. The outer goroutine has no
whole token.

- **(a) `threadTok` → `levelTok l`, `l` caller-chosen (recommended, as parked).** The faithfulness
  argument (tickMu's readers are at most the live goroutines, fewer than 2^30 − 1) never used the
  token's identity. `LeaseRenew` passes `l = 0` from its whole token (no premise); the outer passes
  `l = 3`. A restated axiom: the `axiom` skill before the Freeze.
- **(b) No token at all** (`K = 3`): also faithful, but its review must argue from adequacy's
  thread bound alone; no gain at the closed level.
- **(c) Keep `threadTok`**: the outer cannot meet it. Not an option.

### Q6. `E.RD`'s supply (re-checked: unchanged)

`backend.authRdN` is still `2 ^ 7` (`RdPool.lean:45`); `authRdSupply` hands the server
`authRdN − 1 = 127`, of which `NewServer` takes 67 (`NewServer.lean:930-941`); `rdStockN_val =
805306239`. The pool `I` needs `2 ^ 28 − 1` copies.

- **(a) `authRdN = 2 ^ 28 + 2 ^ 7` (recommended, as the probe).** True of Go (the backend's
  `readTx` reader partition stays `2 ^ 30 − 1`). Changes: the body of `backend.authRdN` and the
  statement of `rdStockN_val` (→ `536870783`), both backend API (`interface/.../backend/RdPool.txt:50`,
  regenerate), `mvcc.nReaders_val` (`InvStore.lean:5040`), `hAN` (`NewServer.lean:931`); the
  `decide`s at `AuthSrv.lean:324,461` still pass. The trusted premise `authSchemaSrv` keeps its
  text but trades a larger count (`authRdN` slots for `authRdN` tickets): the `axiom` skill. About
  40–60 lines; `RdPool.lean` has 2109 importers (398k lines, the whole server and every example): the
  most expensive rebuild of the stage, to batch with the others (§7).
- **(b) A mode split in `authStoreKit`** (auth off posts the copies `authStoreKit_off` discards):
  reverses the user's N2. Rejected.

### Q7. The pools and where they are built

- `B` = `srvWgReaderAt s γg ∗ srvReadReader s γr`, level 2, `2 ^ 28 − 1` items: carved in `start`
  from the stocks `srvStartReaders` posts (`InvStart.lean:323-330`: `actualMaxReaders` of `read.mux`,
  `actualMaxReaders − 2` of `wgMu`); `Start.spec`'s text is unchanged, the counts in
  `srvStartReaders`'s body shrink (an exported definition; its consumers, `etcdstart/Start.lean:74`
  and `auth/startServer.lean:189`, take far fewer).
- `I` = `srvLeadTimeReader s ∗ E.RD`, level 1, `2 ^ 28 − 1` items: in `NewServer`, from
  `leadTimeMu`'s rest (discarded today, `NewServer.lean:1418`) and `E.RD`'s raised supply (Q6).
- `raftPool (srvLgReader s)`: today's, leveled (Q3).
- They reach `start` and `run` in one sealed conjunct `srvRevokeBuilt s E` of the construction
  premise (`isServerBuilt*`/`srvBuiltG` bodies; `NewServer.specG`'s text unchanged), and the
  revocation's persistent bundle `srvRevokeCtx s E ρq γr γg` (sealed, `LeaseRun.lean`): the three
  pools, `isServerReq s E ρq`, `isServerRead s E γr`, `□ (|==> idCred ρq.ids 1)`, the server
  context's `context.isContext`, `srvWithRootOk s E` (Q10).
- Alternative: five single-lock pools (the parked design): more pools, more levels, nothing gained.

**Recommendation: the two bundles.**

### Q8. `run`'s thread token and the restated spec

`start` forks `run` with plain `wp_fork` (`EtcdServer__start.lean:560`); `run` holds no token.

- **(a) Fork `run` with `wp_fork_tok_body` (recommended, as parked)**: `run.spec` (R2c's one spec,
  frozen at `r2c-frozen`) takes `threadTok` and returns it (post `True` → `threadTok`); `run` keeps it
  across rounds. No sound alternative: the outer `GoAttach` deposits a level-1 token and borrows
  `B` at level 2, both from `run`.
- The restated `revokeExpiredLeases.spec` (frozen at `lease-expiry-frozen`):

```lean
abbrev EtcdServer.revokeExpiredLeases.spec : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF)
    (ρ : ReqNames) (v : SrvFields) (γr : ReadNames) (γg : GoNames)
    (γcx : context.ContextNames) (rv : RunFields) (SP : IProp GF) (ls : GoSlice) (ρq : ReqNames),
  srvRevokesLeases E ρq → srvRevokeLevels →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvFieldsAt s γ ci TM E ρ v ∗ srvRunFieldsAt s γr γg γcx rv SP ∗
      lease.expiredLeases (srvGrantGuard E.lg E.authMode.isOn) ls ∗
      srvRevokeCtx s E ρq γr γg ∗ threadTok }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"revokeExpiredLeases")) (Val #ls))
  {{ RET #(); threadTok }}
```

  Unlike the parked text: no `srvLgReader` (the logger comes from `raftPool`), and the level premise
  from `lease.runCfg`'s revocable arm (Q1). `ρq` is the request side's names `Start` hands out
  (`{ρ with wait := γw}`); whether `ρq` must be exactly that is a Draft check. Its proof is an
  ordinary `wp_proof` over callee specs (no pure hypothesis outside the spec), linked only in
  leaseexpiry's `MainLinked` (as the P1 decision kept it out of the server's `Link.lean`), through
  `srvRevokeOpen_proved : srvRevokeOpen`.
- At `run`'s call site (`EtcdServer__run.lean:1330-1336`): `srvRevokesLeases` from `runCfg_lm` and
  `hCoff`; `srvRevokeLevels` and the spec from `lease.runCfg_revoke`; `threadTok` and `#Hrvk` new
  conjuncts of `isServerRun`/`isServerRunC` (exported).

### Q9. The goroutines' accounting (for the Draft's invariant text)

- `run` (whole token): gives `levelTok 1` to the outer `GoAttach` (back at the fork), borrows `B`
  with `levelTok 2` for the `wgMu` slot, gives it back.
- outer (`threadTokFrom 1`, receipt `goRunning`): `Logger()` with `raftPool` at 1; `ensureLeadership`
  with `raftPool` at 1, `B` at 2 (`read.mux`), `levelTok 3`; returns `raftPool`; keeps `B` for the
  loop (`wgMu`) and gives `levelTok 1` to each inner `GoAttach`; returns `B` before exiting, so it
  exits with `threadTokFrom 1` and its receipt.
- inner (`threadTokFrom 1`): borrows `I` at 1 for `WithRoot` and `LeaseRevoke`, returns it, `<-c`,
  `Done`.
- `c`: a bag of `True` (sends and receives carry nothing; the bound is the tokens').
- Bound: every live goroutine is one fuel token; each pool has fewer than `T` loans; `s.wg`'s
  counter is below `2T`.

### Q10. Callees (re-checked: unchanged from the parked design)

- `authStore.WithRoot` is still names-only (`Code/go_etcd_io/etcd/server/v3/auth.toml`'s
  `translate` does not list it): add it, prove `WithRoot.specOff` over `IsAuthEnabled.spec`, add
  `isAuthRoot st RD M` to the auth store construction's post beside `isReqAuth` (an auth API
  change), `srvWithRootOk` wraps it. Fallback, if goose's reach (`metadata`, `tokenSimple`) cannot be
  translated: a contract axiom (trust growth, hard stop).
- `leaseExpired.Inc()`: its initializer is still opaque (`Init.lean:105,356`). Preferred: translate
  it and prove it from `prometheus.NewCounter.wp_proof` (`etcdserver.toml`, `etc/gen-init.py`
  `SPECIAL`); fallback a `leaseExpired_init` axiom (+1 axiom, hard stop).
- `zap.Logger.Warn`, `zap.Uint64/String/Error`, `MemberID`, `Logger`, `fmt.Sprintf` exist.

### Q11. Go first

The stage changes no top-level program's traffic and no model (leaseexpiry's `Main`, its driver and
its claim are unchanged), so the spec-first plan's Go-first rule does not require a Go side. One test
is still worth having for Test (described, **not run now**: the machine stays quiet):
`examples/etcd/leaseexpiry/revoke_stats_test.go`, one in-process member, 40 leases of TTL 1 granted
together (more than `maxPendingRevokes = 16`, so a round blocks on `c`), checking that every lease is
revoked (`Leases()` empty), that `etcd_server_lease_expired_total` grows by 40 (the success arm),
that a lease re-delivered after `expiredLeaseRetryInterval` while its revoke is in flight reaches the
warn arm (`failed to revoke lease`, `ErrLeaseNotFound`), and that `Stop()` during a round returns
without panic (the skipped inner `GoAttach`, the outer's `stopping` exit). It reaches each new
outcome the proof covers.

### Frozen and top-level statements touched

- `EtcdServer.revokeExpiredLeases.spec` (`lease-expiry-frozen`): restated (Q8).
- leaseexpiry's `Main.spec` (`lease-expiry-frozen`): + `srvRevokeLevels`; `Main.wp_proof`'s `hrev`
  and `MainLinked` follow. `etcd_leaseexpiry_adequate`/`_safe`: statements unchanged.
- `run.spec` (`r2c-frozen`): `threadTok` in pre and post.
- The etcd adequacy lemmas `etcd_adequate`, `etcd_adequate_alloc`, `etcd_adequate_members`,
  `etcd_adequate_alloc_members` (etcdstart API, interfaces committed; hub step 7's: a request to
  etcd-grove-82): `Hprog` at `max (n + 2) 4`. No closed theorem's statement changes.
- Exported definitions and specs: `GoAttach.spec`, `srvGoAttachOk` (bound, `raftPool`),
  `isServerRun`/`isServerRunC` (+ `threadTok`, `srvRevokeCtx`), `isServerBuilt*`/`srvBuiltG`
  (+ `srvRevokeBuilt`), `srvStartReaders`'s counts, `lease.runCfg` and `lease.runCfg_revocable`, the
  auth store's post (+ `isAuthRoot`), backend's `authRdN`/`rdStockN_val`, `mvcc.nReaders_val`.
- Unchanged: `srvRevokeOpen`'s text, `NewServer.specG`'s and `Start.spec`'s text, `isServerReq`,
  `LeaseRevoke.spec`, every closed theorem.

### Trust items

- Restated axiom: `EtcdServer.ensureLeadership.wp_proof`, `threadTok` → `levelTok l` (Q5): the
  `axiom` skill.
- A trusted premise's count: `authSchemaSrv` trades `2 ^ 28 + 2 ^ 7` slots for as many tickets
  (Q6): the `axiom` skill.
- Possible growth (only if the preferred routes fail): `leaseExpired_init`, a `WithRoot` contract
  axiom.
- Goose configuration: `auth.toml` (`WithRoot`), `etcdserver.toml` and `gen-init.py` (`leaseExpired`).
- No new model assumption, no Perennial change (P1 is lean's pin, `84d538063`). Removed: the
  `sorry` `srvRevokeOpen_open` (3 → 2; `etc/tcb-report.py --check --update`, collection
  `leaseexpiry`).
- Bounds: `spec-thread` +0 to +1 (leaseexpiry's `Main.spec` if it spells `4 ≤ threadBound GF`
  rather than `srvRevokeLevels`); `bounds-allow.txt` entries for the pool sites.

### §7. Work, order and build cost

1. Adequacy (a2): the four lemmas, the `RealThreadsBelow` lemma, docstrings. ~30 lines, 54 modules.
2. Leveled `s.wg`, `GoAttach.spec`, `wp_GoAttach_tok`, `srvGoAttachOk`. ~300–350 lines; 961 modules.
3. `raftPool` at level 1, `borrowL`/`giveBackL`. ~70–90 lines; 1222 modules.
4. `ensureLeadership` → `levelTok l` (axiom skill first), `LeaseRenew`. ~30 lines; 402 modules.
5. `authRdN` raise. ~40–60 lines; 2109 modules.
6. Callees: `WithRoot` (config, regeneration, proof, `isAuthRoot`), `leaseExpired`. ~250 lines.
7. Pools and plumbing: `B`, `I`, `srvRevokeBuilt`, `srvRevokeCtx`, `srvRevokeLevels` in
   `lease.runCfg`, `run`'s fork and spec, `isServerRun*`. ~400 lines; `InvStart` 946, `LeaseRun` 950.
8. The spec, its proof (~400 lines), `run`'s call site, `srvRevokeOpen_proved`, leaseexpiry's
   `Main.spec`/`MainLinked`; delete the `sorry`.

About 1,500–1,900 lines. The statement changes of 2–5 and 7 all rebuild most of the server; the
Draft lands them as one batch (statements first, proofs `sorry`), so that the 2109-module rebuild is
paid once, then proves 2–8 against built statements.

### §9. The parked design against today's lean

- **Still right:** no Go bug; pools are unavoidable; `c` as a bag of `True`; `s.wg` leveled with
  `p = 1` and the `2T` bound (`⌜2 * threadBound GF ≤ 2 ^ 31⌝`); `ensureLeadership` → `levelTok l`
  (its other caller `LeaseRenew`, `l = 0`); `E.RD` via `authRdN = 2 ^ 28 + 2 ^ 7` (numbers unchanged:
  `2 ^ 7`, 67 taken, `rdStockN_val = 805306239`); `run` forked with a token, `run.spec`'s post
  `threadTok`; `srvRevokeCtx`/`srvRevokeBuilt`; `WithRoot` and `leaseExpired` as proposed.
- **Moved:**
  - `GoAttach.spec` now carries H2's receipt (`goRunning γ`, `srvGoResAt`): the generalized spec
    keeps it, and `goAttachInv`'s receipts count the started goroutines only (Q4).
  - `GoAttach.spec` drops `srvLgReader` (the stopped branch borrows from `raftPool`), and `raftPool`
    is at level 1, not 2: otherwise the bound goes global (Q3).
  - Levels 0–3, two bundled pools, `K = 4`, instead of 0–7 and five pools (Q2).
  - The level bound is a premise on the revocable run configuration and on leaseexpiry's
    `Main.spec`, so `Main.spec` is no longer "unchanged" (Q1); the four etcd adequacy lemmas take
    `T = max (n + 2) 4`.
  - The restated spec drops `srvLgReader` and gains `srvRevokeLevels` (Q8).
  - `run.spec` is now R2c's one spec (`r2c-frozen`); the parked `run.specStop` is gone.
  - The trust base is 3 `sorry`s today, so the stage takes it to 2 (the parked text said 4 → 3).

### Recommendations, in one list

Q1 (a2) confined, `K = 4`; Q2 (ii); Q3 (i); Q4 (i); Q5 (a); Q6 (a); Q7 the two bundles; Q8 (a)
with the text above; Q10 the preferred routes; Q11 no Go-first requirement, the stats test in Test.
Hard stops for the user: this Scope; the frozen statements and the adequacy lemmas above; the
restated `ensureLeadership` axiom and `authSchemaSrv`'s count (each after the `axiom` skill); the
Goose configuration changes.

## Draft pass 1 (2026-11-06)

Pass 1, step A (`notes/spec-first-plan.md`, "A large Draft: pass 1 small, pass 2 wide"): every
statement the stage changes or adds that more than one package names, old → new, in exact Lean text,
written before any build. Step B applies them (proofs that break become `sorry -- DRAFT revoke-open`).
Where a statement differs from the Scope's text, the item says why (**Δ**). §F lists the changes
found necessary in step A that the Scope did not list (the batching rule: applied as DRAFT, brought
to the user once); one of them touches a `Results.lean` statement, which the brief forbids without a
decision: **§F.1 needs an answer before step B**.

Notation: `actualMaxReaders` is `sync.rwmutex.actualMaxReaders` (`2 ^ 30 - 1`).

### A. The hub statements: the four etcd adequacy lemmas (etcdstart API; a request to etcd-grove-82)

**A.0 New lemma** (`Proof/runtime/Threads.lean`, beside `realThreadsBelow_of_one`):

```lean
/-- `RealThreadsBelow` is monotone in the bound (revoke-open Q1 (a2): the etcd adequacy lemmas'
`T = max (n + 2) 4`). -/
theorem realThreadsBelow_mono {T T' n : Nat} {ρ : List Expr × CfgState} (hT : T ≤ T')
    (h : RealThreadsBelow T n ρ) : RealThreadsBelow T' n ρ
```

**A.1–A.4** `etcd_adequate`, `etcd_adequate_alloc` (`etcdstart/Adequacy.lean`),
`etcd_adequate_members`, `etcd_adequate_alloc_members` (`etcdstart/AdequacyMembers.lean`): in each,
the one line of `Hprog`'s binder

```lean
    (Hprog : ∀ hG : HeapGS .hasLC GF, receiptBound GF = n + 1 → threadBound GF = n + 2 →
```

becomes

```lean
    (Hprog : ∀ hG : HeapGS .hasLC GF, receiptBound GF = n + 1 → threadBound GF = max (n + 2) 4 →
```

Everything else in the four statements is unchanged. Proofs: `etcd_adequate`/`etcd_adequate_alloc`
pass `(max (n + 2) 4)` for `T` to `goose_adequacy_start` and `(realThreadsBelow_mono
(Nat.le_max_left _ _) (realThreadsBelow_of_one Hthreads))` for `Hlive`; the two `_members` lemmas are
unchanged. Docstrings: each says "(revoke-open, 2026-11-06) at the thread bound `max (n + 2) 4`: the
revocation's goroutines use levels 0–3 of a thread token (`srvRevokeLevels`)". Unchanged:
`init_adequate`, `init_adequate_start`, `durable_init_adequate`, `k8s_etcd3_adequate` (`n + 2`).

The closed theorems over them (the 15 of §1) keep their statements (`Hn : n + 2 ≤ 2 ^ 28`): their
`(by rw [HT]; omega)` sites see `max (n + 2) 4`, which `omega` handles. Only docstrings that say "the
thread bound `n + 2`" change.

### B. `run.spec` (frozen at `r2c-frozen`)

In `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__run.lean`, old:

```lean
      isServerRunC C s γ ci TM E ρ γr Er γn γg γcx γd v b ai₀ at₀ c₀ x₀ (srvStopReq s E ρ dd)
        (srvDoneInv ρ.rd.raft.raft ρ γn.id dd c) }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"run")) (Val #()))
  {{ RET #(); True }}
```

new:

```lean
      isServerRunC C s γ ci TM E ρ γr Er γn γg γcx γd v b ai₀ at₀ c₀ x₀ (srvStopReq s E ρ dd)
        (srvDoneInv ρ.rd.raft.raft ρ γn.id dd c) ∗ threadTok }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"run")) (Val #()))
  {{ RET #(); threadTok }}
```

Docstring: "+ `run` holds a thread token, which it returns (revoke-open Q8 (a): `start` forks it with
`wp_fork_tok_body`; its expiry arm gives level 1 to the outer `GoAttach` and borrows the outer pool
with level 2)". **Δ** Q8 put `threadTok` in `isServerRun`/`isServerRunC`; here it is in `run.spec`'s
own pre, beside the post that returns it (a spec takes its `threadTok` itself, CLAUDE.md "Bounds"),
and `isServerRun*` gain only `#Hrvk`.

### C. `isServerRun*`, `isServerBuilt*`/`srvBuiltG`, `srvStartReaders` (exported definitions)

**C.0 New module** `Proof/go_etcd_io/etcd/server/v3/etcdserver/RevokeCtx.lean` (public imports
`InvRunRes` and `AuthGuard`). **Δ** The Scope put `srvRevokeLevels` and `srvRevokeCtx` in
`LeaseRun.lean`; but `LeaseRun` imports `EtcdServer__revokeExpiredLeases`'s spec, whose pre names
them, so they live in a module below the spec, which the spec imports. For the same reason
`srvRevokesLeases` moves here from `LeaseRevoke.lean` (text unchanged: `LeaseRevoke.lean` reaches
`LeaseRun`, which imports the spec). Its text:

```lean
/-- **The level bound the revocation's goroutines need** (revoke-open Q1 (a2), Q2 (ii)): levels 0–3
of a thread token exist (level 0 a started goroutine's slot in `s.wg`; 1 `wg.Add`'s pending token,
`raftPool`, the inner pool; 2 the outer pool; 3 `ensureLeadership`'s). Only the revocable run
configuration carries it (`lease.runCfg`), so no other spec names the bound. -/
def srvRevokeLevels : Prop := 4 ≤ threadBound GF

/-- The copies in each of the revocation's pools: one fewer than the server's thread bound's limit
(`threadBound GF ≤ backend.rdPoolN`, `isServerBuilt`'s `%Hbound`), what `threadPool.initL` needs. -/
@[word_unfold] def srvRevokePoolN : Nat := backend.rdPoolN - 1

def srvRevokeOuterN : Namespace := nroot .@ "srvRevokeOuter"
def srvRevokeInnerN : Namespace := nroot .@ "srvRevokeInner"

/-- **The outer pool `B`** (revoke-open Q7; level 2): what the outer goroutine holds for its loop,
a reader slot of `wgMu` at `GoAttach`'s names `γg` (its `GoAttach`es) and one of the read loop's lock
(`ensureLeadership`'s `LinearizableReadNotify`). Carved by `start` from `srvStarted`'s stocks. -/
def srvRevokeOuterPool (s : Loc) (γr : ReadNames) (γg : GoNames) : IProp GF :=
  iprop(∃ γ : GName, threadPool.isThreadPoolL srvRevokeOuterN 2 γ
    iprop(srvWgReaderAt s γg ∗ srvReadReader s γr))

/-- **The inner pool `I`** (revoke-open Q7; level 1): what an inner goroutine holds for its
`WithRoot` and `LeaseRevoke`, a reader slot of `leadTimeMu` and the auth store's reader resource.
Built by `NewServer` from `leadTimeMu`'s rest and `E.RD`'s supply (Q6). -/
def srvRevokeInnerPool (s : Loc) (E : apply.AEnv GF) : IProp GF :=
  iprop(∃ γ : GName, threadPool.isThreadPoolL srvRevokeInnerN 1 γ
    iprop(srvLeadTimeReader s ∗ E.RD))

/-- **What `NewServer` builds for the revocation** (sealed; persistent): the inner pool, the
transport's pool of `lgMu` readers (`raftPool`, leveled at 1, Q3) and the auth store's concrete
pointer (`WithRoot`'s receiver). -/
@[no_expose] def srvRevokeBuilt (s : Loc) (E : apply.AEnv GF) : IProp GF :=
  iprop(srvRevokeInnerPool s E ∗ raftPool (srvLgReader s) ∗
    (∃ stl : Loc, srvAuthStoreAddr s ↦□ auth.authIface stl))

/-- **The revocation's persistent bundle** (sealed): `srvRevokeBuilt`, the outer pool at `start`'s
names, with auth off the request side's and the reader's views (from which `srvAuthAt`,
`srvAuthAt_of_views`) and the mode `off` (`WithRoot`'s premise, the `IsAuthEnabled` verdict), the
request names' credential, and the server context's contract (`s.ctx`, `WithRoot`'s argument and
`LeaseRevoke`'s). -/
@[no_expose] def srvRevokeCtx (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (γg : GoNames) : IProp GF :=
  iprop(srvRevokeBuilt s E ∗ srvRevokeOuterPool s γr γg ∗
    ⌜E.authOn = false → E.authMode = auth.AuthMode.off⌝ ∗
    □ (⌜E.authOn = false⌝ → isServerReq s E ρ ∗ isServerRead s E γr) ∗
    □ (|==> idCred ρ.ids 1) ∗
    (∃ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
      srvCtxAddr s ↦□ GoInterface.ok ctx ∗ context.isContext ctx cd))
```

with `Persistent` instances for both sealed predicates (laws of the module). **Δ** No `srvWithRootOk`
and no `isAuthRoot` (Q10): `isServerReq ∗ isServerRead` give `srvAuthAt`, whose `apply.isAuthStore`
already carries `IsAuthEnabled`'s contract at `E.RD` (`Contracts.lean:27`), and `WithRoot`'s spec
(§I.3) takes that contract as a premise; so the auth store's construction post is unchanged (§G).
The guards on the off-mode views: `isServerRun*` carry `#Hrvk` in both auth modes; with auth on the
revocation never runs (`srvRevokesLeases`). (`isServerReqM` cannot be used: `ReqOn` reaches `LeaseRun`.)

**C.1** `isServerRun` (`InvRun.lean`), `isServerRunOn` (`RunOn.lean`), `isServerRunC`
(`AuthCompRows.lean`): after the conjunct

```lean
    "#Hrf" ∷ srvRunFieldsAt s γr γg γcx v SP ∗
```

insert

```lean
    -- (revoke-open, 2026-11-06) the revocation's bundle (`run`'s expiry arm, revocable mode)
    "#Hrvk" ∷ srvRevokeCtx s E ρ γr γg ∗
```

(in `isServerRunOn`, after its `#Hrf`). Nothing else changes in the three.

**C.2** `isServerBuilt` (`InvStart.lean`), `isServerBuiltOn` (`StartOn.lean`), `isServerBuiltC`
(`AuthCompRows.lean`), `srvBuiltG` (`ServerOn.lean`): after the conjunct

```lean
    "%Hbound" ∷ ⌜threadBound GF ≤ backend.rdPoolN⌝ ∗
```

insert

```lean
    -- (revoke-open, 2026-11-06) what `NewServer` built for the revocation
    "#Hrvkb" ∷ srvRevokeBuilt s E ∗
```

`NewServer.specG`'s text is unchanged (its post names `srvBuiltG`).

**C.3** `srvStartReaders` (`InvStart.lean`), old:

```lean
def srvStartReaders (s : Loc) (γr : ReadNames) : IProp GF :=
  iprop(([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
      srvReadReader s γr) ∗
    ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders - 2) (), srvWgReader s))
```

new:

```lean
def srvStartReaders (s : Loc) (γr : ReadNames) : IProp GF :=
  iprop(([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders - srvRevokePoolN) (),
      srvReadReader s γr) ∗
    ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders - 2 - srvRevokePoolN) (),
      srvWgReader s))
```

and the same two counts in `srvStarted`'s `"Hrds"` and `"Hwgs"` (`InvStart.lean`; `start.spec`'s
post, text unchanged): `Int.toNat sync.rwmutex.actualMaxReaders` → `Int.toNat
sync.rwmutex.actualMaxReaders - srvRevokePoolN`, `Int.toNat sync.rwmutex.actualMaxReaders - 2` →
`Int.toNat sync.rwmutex.actualMaxReaders - 2 - srvRevokePoolN` (805306368 and 805306366). **Δ**
`srvStarted` was not in the Scope's list; and the read slots reach further than the Scope said: §F.1.

### D. `GoAttach.spec`, `srvGoAttachOk`, `goAttachInv`, `wp_GoAttach_tok`

**D.1** `EtcdServer.GoAttach.spec` (`Spec/.../EtcdServer__GoAttach.lean`), old:

```lean
abbrev EtcdServer.GoAttach.spec : Prop :=
  ∀ (s : Loc) (γ : GoNames) (f : GoFunc) (P : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvGoResAt s γ ∗ srvLgReader s ∗ P ∗
      {{ P ∗ goRunning γ }} (App (Val #f) (Val #())) {{ RET #(); goRunning γ }} }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"GoAttach")) (Val #f))
  {{ RET #(); srvGoResAt s γ ∗ srvLgReader s }}
```

new:

```lean
abbrev EtcdServer.GoAttach.spec : Prop :=
  ∀ (s : Loc) (γ : GoNames) (f : GoFunc) (P : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvWgReaderAt s γ ∗ levelTok 1 ∗ P ∗
      {{ P ∗ goRunning γ ∗ threadTokFrom 1 }} (App (Val #f) (Val #()))
        {{ RET #(); goRunning γ ∗ threadTokFrom 1 }} }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"GoAttach")) (Val #f))
  {{ RET #(); srvWgReaderAt s γ ∗ levelTok 1 }}
```

Docstring: the caller's level-1 token is `wg.Add`'s pending deposit, back at the `go` statement (or,
stopped, the `lgMu` borrow from `raftPool` for `Logger()`); `f` runs on the fresh token's levels from
1 (level 0 is in the wait group until its `Done`).

**D.2** `srvGoAttachOk` (`InvGoAttach.lean`), old last two lines:

```lean
    (∃ l : Loc, srvLgAddr s ↦□ l ∗ ⌜l ≠ null⌝) ∗
    ⌜threadBound GF ≤ 2 ^ 31⌝)
```

new:

```lean
    (∃ l : Loc, srvLgAddr s ↦□ l ∗ ⌜l ≠ null⌝) ∗ raftPool (srvLgReader s) ∗
    ⌜2 * threadBound GF ≤ 2 ^ 31⌝)
```

`InvGoAttach.lean` gains `public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Net`
(`Net` does not reach `InvApplier`, so no cycle; `InvRunRes` already reaches `Net`).

**D.3** `goAttachInv` (`InvGoAttach.lean`; the invariant body), old:

```lean
def goAttachInv (γ : GoNames) : IProp GF :=
  iprop(∃ (b : Bool) (ctr : w32) (k : Nat) (dq : DFrac), ghostVar γ.b (1 : Qp).half b ∗
    sync.ownWaitGroup γ.wg ctr ∗ threadToks k ∗ ownTokAuthDfrac γ.run dq k ∗
    ⌜0 ≤ sint.Z ctr ∧ sint.nat ctr = k⌝ ∗
    ⌜dq = DFrac.own 1 ∨ (dq = DFrac.own (1 : Qp).half ∧ k = 0 ∧ b = false)⌝ ∗
    (⌜b = false⌝ ∗ token γ.close ∗ (⌜dq = DFrac.own 1⌝ ∨ token γ.wt) ∨
      ⌜b = true⌝ ∗ sync.ownWaitGroupWaiters γ.wg 0 ∗ token γ.wt))
```

new (`d` goroutines started, each with its level-0 token deposited and its receipt counted; `q`
`Add`s pending, each with its caller's level-1 token; the counter their sum, below `2 * threadBound`):

```lean
def goAttachInv (γ : GoNames) : IProp GF :=
  iprop(∃ (b : Bool) (ctr : w32) (d q : Nat) (dq : DFrac), ghostVar γ.b (1 : Qp).half b ∗
    sync.ownWaitGroup γ.wg ctr ∗ levelToks 0 d ∗ levelToks 1 q ∗ ownTokAuthDfrac γ.run dq d ∗
    ⌜0 ≤ sint.Z ctr ∧ sint.nat ctr = d + q⌝ ∗
    ⌜dq = DFrac.own 1 ∨ (dq = DFrac.own (1 : Qp).half ∧ d = 0 ∧ q = 0 ∧ b = false)⌝ ∗
    (⌜b = false⌝ ∗ token γ.close ∗ (⌜dq = DFrac.own 1⌝ ∨ token γ.wt) ∨
      ⌜b = true⌝ ∗ sync.ownWaitGroupWaiters γ.wg 0 ∗ token γ.wt))
```

Ownership: allocated by `start` (as today); opened by `GoAttach` (its `Add` deposits `levelTok 1`,
`q + 1`; at the `go` statement, `wp_fork_tok_upd`, the fresh token's level 0 is deposited, `d + 1`,
the receipt minted, and the pending level-1 token returned, `q - 1`, the goroutine keeping
`threadTokFrom 1`), by the goroutine's `Done` (takes a level 0 back with its receipt, `d - 1`) and by
`run`'s shutdown `Wait` (as H2). `ownAdder` exclusivity is why `sync.tokJoinL` is not reused (Q4).

**D.4** New lemma `wp_GoAttach_tok`, in a new module
`Proof/go_etcd_io/etcd/server/v3/etcdserver/GoAttachTok.lean` (imports the spec). **Δ** The Scope put it
in `InvGoAttach.lean`, which the spec imports; a lemma about the spec sits above it. Its statement
is today's spec text:

```lean
/-- **`GoAttach` with a whole thread token** (revoke-open Q4 (i)): today's triple, from
`GoAttach.spec` (the token split `levelTok 0 ∗ levelTok 1 ∗ threadTokFrom 2`, level 1 lent, the rest
and `srvLgReader s` framed, `threadTokFrom 1` framed through `f`). The six callers of `GoAttach`
before the stage apply it. -/
theorem wp_GoAttach_tok (hGA : EtcdServer.GoAttach.spec (GF := GF) (hG := hG))
    (s : Loc) (γ : GoNames) (f : GoFunc) (P : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        srvGoResAt s γ ∗ srvLgReader s ∗ P ∗
        {{ P ∗ goRunning γ }} (App (Val #f) (Val #())) {{ RET #(); goRunning γ }} }}
      (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"GoAttach")) (Val #f))
    {{ RET #(); srvGoResAt s γ ∗ srvLgReader s }}
```

**D.5** `raftPool` at level 1 (`api/rafthttp/Net.lean`; no `etc/api`; Q3 (i)). Old:

```lean
def raftPool (R : IProp GF) : IProp GF := iprop(∃ γ : GName, threadPool.isThreadPool raftPoolN γ R)
def raftLoan (R : IProp GF) : IProp GF :=
  iprop(∃ γ : GName, threadPool.isThreadPool raftPoolN γ R ∗ threadPool.ownThreadLoan γ)
```

new:

```lean
def raftPool (R : IProp GF) : IProp GF :=
  iprop(∃ γ : GName, threadPool.isThreadPoolL raftPoolN 1 γ R)
/-- An `R` lent out for a whole thread token: the loan and the token's other levels. -/
def raftLoan (R : IProp GF) : IProp GF :=
  iprop(∃ γ : GName, threadPool.isThreadPoolL raftPoolN 1 γ R ∗ threadPool.ownThreadLoan γ ∗
    levelTok 0 ∗ threadTokFrom 2)
/-- An `R` lent out for a level-1 token. -/
def raftLoanL (R : IProp GF) : IProp GF :=
  iprop(∃ γ : GName, threadPool.isThreadPoolL raftPoolN 1 γ R ∗ threadPool.ownThreadLoan γ)

theorem raftPool_borrowL (R : IProp GF) (E : CoPset) (HN : ↑raftPoolN ⊆ E) :
    £ 1 ∗ raftPool R ∗ levelTok 1 ⊢ |={E}=> R ∗ raftLoanL R
theorem raftLoanL_giveBack (R : IProp GF) (E : CoPset) (HN : ↑raftPoolN ⊆ E) :
    raftLoanL R ∗ R ⊢ |={E}=> levelTok 1
```

`raftPool_init`, `raftPool_borrow` and `raftLoan_giveBack` keep their statements (`initL`;
`threadTokFrom_succ` at `0` and `1`, `1 < threadBound GF` from `ThreadGS.threadBound_gt`).

### E. `lease.runCfg` with `srvRevokeLevels` (and `lease.bootCfg`)

**E.1** `lease.runCfg` (`LeaseRun.lean`), old:

```lean
@[no_expose] def lease.runCfg (lm : lease.Mode) (m : lease.Mode) : Prop :=
  lm = m ∧ (m = .mono → lease.leasesNoExpiry) ∧ (m = .revocable → srvRevokeOpen (GF := GF) (hG := hG))
```

new:

```lean
@[no_expose] def lease.runCfg (lm : lease.Mode) (m : lease.Mode) : Prop :=
  lm = m ∧ (m = .mono → lease.leasesNoExpiry) ∧
    (m = .revocable → srvRevokeLevels (GF := GF) ∧ srvRevokeOpen (GF := GF) (hG := hG))
```

**E.2** `lease.runCfg_revocable`, old → new:

```lean
theorem lease.runCfg_revocable (hrev : srvRevokeOpen (GF := GF) (hG := hG)) :
    lease.runCfg (GF := GF) .revocable .revocable
```
```lean
theorem lease.runCfg_revocable (hlev : srvRevokeLevels (GF := GF))
    (hrev : srvRevokeOpen (GF := GF) (hG := hG)) :
    lease.runCfg (GF := GF) .revocable .revocable
```

**E.3** `lease.runCfg_revoke`, old → new:

```lean
theorem lease.runCfg_revoke {lm : lease.Mode} (h : lease.runCfg (GF := GF) lm .revocable) :
    srvRevokeOpen (GF := GF) (hG := hG)
```
```lean
theorem lease.runCfg_revoke {lm : lease.Mode} (h : lease.runCfg (GF := GF) lm .revocable) :
    srvRevokeLevels (GF := GF) ∧ srvRevokeOpen (GF := GF) (hG := hG)
```

**E.4** New (`LeaseRun.lean`; `srvRevokeOpen` is sealed, so `MainLinked` needs the intro law):

```lean
/-- The open case, from a proof of the spec (`leaseexpiry`'s `MainLinked`). -/
theorem srvRevokeOpen_intro (h : EtcdServer.revokeExpiredLeases.spec (GF := GF) (hG := hG)) :
    srvRevokeOpen (GF := GF) (hG := hG)
```

**E.5** **Δ** (not in the Scope's list) `lease.bootCfg` (`LeaseApi.lean`) has the same revocable arm,
and `lease.bootCfg_of_run` relates the two: its body's `(m = .revocable → srvRevokeOpen (GF := GF)
(hG := hG))` becomes `(m = .revocable → srvRevokeLevels (GF := GF) ∧ srvRevokeOpen (GF := GF) (hG :=
hG))`, and `lease.bootCfg_revocable` gains `(hlev : srvRevokeLevels (GF := GF))` before `hrev`.

### F. Further changes found in step A (the batch; not in the Scope)

**F.1 The read loop's reader slots reach a `Results.lean` statement. Needs a decision.** The outer
pool `B` takes `srvRevokePoolN` of `read.mux`'s `actualMaxReaders` reader slots in `start`, before
`go s.run()`; every one of those slots is in `srvStarted`'s `"Hrds"` today and flows on, by name of
the count, into:
- `start_gives_views` (`Proof/go_etcd_io/etcd/server/v3/etcdserver/Results.lean:2236`), whose post
  ends `[∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (), srvReadReader s
  γr`: an exported server result; the brief says no `Results.lean` statement may change;
- `etcdstart.memberUp` and `etcdstart.memberUpOn` (`etcdstart/Defs.lean:348,482`, hub step 7's;
  `interface/.../etcdstart/Defs.txt:167,240`), each `([∗list] _x ∈ List.replicate (Int.toNat
  sync.rwmutex.actualMaxReaders) (), srvReadReader s ρ.rd)`;
- `etcdstart.kvServeStocks` (`etcdstart/Served.lean:115`, `Served.txt:59`), the same count at `γr`.

The change, in all four: `Int.toNat sync.rwmutex.actualMaxReaders` →
`Int.toNat sync.rwmutex.actualMaxReaders - srvRevokePoolN` (805306368 slots; the gRPC slot takes 1,
`client.etcdGrpcSlots_of_started`'s count premises still hold). `start_gives_views`'s change is a
weakening (fewer slots returned). No closed (adequacy) theorem changes.
Alternatives considered: (b) carve `B` only in the revocable mode: the counts become a mode-dependent
expression, still a text change of the four; (c) drop `srvReadReader` from `ensureLeadership`'s
axiom (so `B` needs no read slot): unsound, since other holders of `read.mux`'s slots may assemble
all of them and conclude no reader, while the axiom's hidden reader exists (the `tickMu` argument
works only because no slot of `tickMu` is held by anyone); rejected. **Recommendation: (a), the
count change in the four**, `start_gives_views` included. If it is not accepted, step B cannot
proceed as designed.

**F.2** `srvRevokesLeases` moves from `LeaseRevoke.lean` to `RevokeCtx.lean` (text unchanged; C.0).

**F.3** `lease.bootCfg`/`lease.bootCfg_revocable` (E.5).

**F.4** `srvStarted`'s counts (C.3).

**F.5** `auth.toml`: `"authStore.WithRoot"` added to `translate` (the Scope's Goose configuration
item; regenerate with `etc/goose.py --project etcd`); `etcdserver.toml`/`etc/gen-init.py` `SPECIAL`
for `leaseExpired` (the Scope's preferred route). Both are pass-2 work but change generated files
other packages import; step B does them if the translation goes through, else records it.

### G. The auth store's post: unchanged (**Δ** from Q10)

Q10 proposed `isAuthRoot st RD M` in the construction's post and `srvWithRootOk`. Not needed:
`srvAuthAt s E` (from `isServerReq ∗ isServerRead`, `srvAuthAt_of_views`) holds
`apply.isAuthStore st E.γ P f E.RD E.authMode E.RW`, whose `IsAuthEnabled` clause (`{{ RD }}
IsAuthEnabled() {{ b, RD ∗ auth.enabledVerdict M b }}`, `enabledVerdict .off b = ⌜b = false⌝`) is what
`WithRoot`'s body needs; `WithRoot`'s spec (I.3) takes it as a premise, and the receiver's concrete
pointer is `srvRevokeBuilt`'s (from `authStoreKit`'s `⌜st = auth.authIface stl⌝`, already in its post).
So neither `auth.NewAuthStore.spec` (an axiom) nor `authStoreKit`'s post changes.

### H. backend `authRdN`/`rdStockN_val` (Q6 (a))

`Proof/go_etcd_io/etcd/server/v3/storage/backend/RdPool.lean`, old → new:

```lean
@[word_unfold] def authRdN : Nat := 2 ^ 7
```
```lean
@[word_unfold] def authRdN : Nat := 2 ^ 28 + 2 ^ 7
```

```lean
theorem rdStockN_val : rdStockN = 805306239 := by
```
```lean
theorem rdStockN_val : rdStockN = 536870783 := by
```

and `mvcc.nReaders_val` (`InvStore.lean:5040`): `nReaders = 805306239` → `nReaders = 536870783`;
`NewServer`'s `hAN : backend.authRdN = 128` → `= 2 ^ 28 + 128`. Docstrings: `authRdN` "(revoke-open
Q6, 2026-11-06: `2 ^ 28` more, the inner pool's `E.RD` copies)", `rdStockN_val`'s value
`2 ^ 30 - 1 - 2 ^ 28 - 2 ^ 28 - 2 ^ 7`. Interface `RdPool.txt` regenerated.

### I. The frozen `revokeExpiredLeases.spec`, leaseexpiry's `Main.spec`, and the callee specs

**I.1** `EtcdServer.revokeExpiredLeases.spec` (frozen at `lease-expiry-frozen`), old:

```lean
abbrev EtcdServer.revokeExpiredLeases.spec : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF)
    (ρ : ReqNames) (v : SrvFields) (γr : ReadNames) (γg : GoNames)
    (γcx : context.ContextNames) (rv : RunFields) (SP : IProp GF) (ls : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvFieldsAt s γ ci TM E ρ v ∗ srvRunFieldsAt s γr γg γcx rv SP ∗
      lease.expiredLeases (srvGrantGuard E.lg E.authMode.isOn) ls }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"revokeExpiredLeases")) (Val #ls))
  {{ RET #(); True }}
```

new:

```lean
abbrev EtcdServer.revokeExpiredLeases.spec : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF)
    (ρ : ReqNames) (v : SrvFields) (γr : ReadNames) (γg : GoNames)
    (γcx : context.ContextNames) (rv : RunFields) (SP : IProp GF) (ls : GoSlice),
  srvRevokesLeases E ρ → srvRevokeLevels (GF := GF) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvFieldsAt s γ ci TM E ρ v ∗ srvRunFieldsAt s γr γg γcx rv SP ∗
      lease.expiredLeases (srvGrantGuard E.lg E.authMode.isOn) ls ∗
      srvRevokeCtx s E ρ γr γg ∗ threadTok }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"revokeExpiredLeases")) (Val #ls))
  {{ RET #(); threadTok }}
```

The spec module's import becomes `RevokeCtx` (which imports `InvRunRes`). **Δ** The Scope's text had
a separate `ρq`; `run` is called with `{ ρ with wait := γw }` (`EtcdServer__start.lean:561`), so
`run`'s `ρ` is already the request names `Start` hands out: one `ρ` (Q8's "Draft check", resolved).
At `run`'s call site: `srvRevokesLeases E ρ` from `runCfg_lm` and `hCoff`; `srvRevokeLevels` and the
spec from `lease.runCfg_revoke`; `srvRevokeCtx` from `#Hrvk`; `threadTok` from `run`'s own.

**I.2** leaseexpiry's `Main.spec` (`Spec/.../examples/etcd/leaseexpiry/Main.lean`, frozen at
`lease-expiry-frozen`), old line:

```lean
  threadBound GF ≤ 2 ^ 28 → receiptBound GF ≤ 2 ^ 48 → receiptBound GF ≤ N + 1 →
```

new:

```lean
  threadBound GF ≤ 2 ^ 28 → srvRevokeLevels (GF := GF) → receiptBound GF ≤ 2 ^ 48 →
    receiptBound GF ≤ N + 1 →
```

`Main.wp_proof`: `hrev` stays; `lease.runCfg_revocable hrev` → `lease.runCfg_revocable Hlev hrev`.
`MainLinked`: `srvRevokeOpen_open` → `(srvRevokeOpen_intro (EtcdServer.revokeExpiredLeases.wp_proof
…callees…))`. `etcd_leaseexpiry_adequate` (statement unchanged) passes `(by unfold srvRevokeLevels;
rw [HT]; omega)`. Bounds: `spec-thread` +0 (named Prop).

**I.3** The callee specs the proof cites (new; cross-package or new):
- `auth.authStore.WithRoot.spec` (new, `Spec/go_etcd_io/etcd/server/v3/auth/authStore__WithRoot.lean`):

```lean
/-- **`as.WithRoot(ctx)`, auth off** (the only case a caller of the stage needs; `server.go`'s
revocation runs with auth off): given `IsAuthEnabled`'s contract answering `false` at the caller's
reader resource `RD`, it returns `ctx` itself (`if !as.IsAuthEnabled() { return ctx }`). -/
abbrev auth.authStore.WithRoot.spec : Prop :=
  ∀ (st : Loc) (RD : IProp GF) (ctx : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ RD ∗
      □ ({{ RD }} (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"IsAuthEnabled"))
          (Val #()))
        {{ (b : Bool), RET #b; RD ∗ ⌜b = false⌝ }}) }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"WithRoot")) (Val #ctx))
  {{ RET #ctx; RD }}
```

  **Δ** named `spec`, not `specOff` (one spec of the function; its scope in the docstring).
- `EtcdServer.ensureLeadership.spec` (the restated axiom, §J).
- Unchanged and cited: `GoAttach.spec` (D.1), `Logger.spec`, `LeaseRevoke.spec`,
  `zap.Logger.Warn`, `zap.Uint64`/`String`/`Error`, `MemberID`, `fmt.Sprintf`, `prometheus`'s
  `Counter.Inc` (through `leaseExpired`'s initializer, F.5).

### J. The trust items

**J.1** `EtcdServer.ensureLeadership.spec` (`Spec/.../EtcdServer__ensureLeadership.lean`; its proof
the axiom `EtcdServer.ensureLeadership.wp_proof`, text unchanged), old:

```lean
abbrev EtcdServer.ensureLeadership.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReqM E.authOn s E ρ ∗ isServerReadM E.authOn s E γr ∗ srvLgReader s ∗
      srvReadReader s γr ∗ threadTok ∗ ⌜threadBound GF ≤ 2 ^ 30 - 1⌝ }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"ensureLeadership")) (Val #()))
  {{ (b : Bool), RET #b; srvLgReader s ∗ srvReadReader s γr ∗ threadTok }}
```

new:

```lean
abbrev EtcdServer.ensureLeadership.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (l : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReqM E.authOn s E ρ ∗ isServerReadM E.authOn s E γr ∗ srvLgReader s ∗
      srvReadReader s γr ∗ levelTok l ∗ ⌜threadBound GF ≤ 2 ^ 30 - 1⌝ }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"ensureLeadership")) (Val #()))
  {{ (b : Bool), RET #b; srvLgReader s ∗ srvReadReader s γr ∗ levelTok l }}
```

Faithfulness paragraph: "the thread bound (a level token, `levelTok l`, any level: the caller is a
live goroutine; `threadBound GF ≤ 2 ^ 30 - 1`)" in place of "(`threadTok`, ...)". A restated axiom:
the `axiom` skill before the Freeze. `LeaseRenew`'s proof passes `l = 0` (`threadTok_level0`-style
split, `threadTokFrom 1` framed); its statement is unchanged.

**J.2** `authSchemaSrv` (`AuthSrv.lean`): text unchanged; its `([∗list] _x ∈ List.replicate
backend.authRdN (), R)` now counts `2 ^ 28 + 2 ^ 7` tickets (and takes as many slots, `authRdSlots`).
The `axiom` skill before the Freeze.

No other trust item: no new axiom, model or non-DRAFT `sorry` (G removes the Scope's fallback
`isAuthRoot` route entirely; `leaseExpired`'s fallback axiom only if F.5's translation fails, a stop).

### K. For the Freeze: the consumers of `read.mux`'s reader slots (2026-11-06, the coordinator's condition on F.1)

`read.mux` has `actualMaxReaders = 2 ^ 30 - 1` reader slots (`sync.init_RWMutex` in `start`). After
the stage: `srvRevokePoolN = 2 ^ 28 - 1` go to the outer pool `B` (`start`); the rest,
`actualMaxReaders - srvRevokePoolN = 805306368` (`3 * 2 ^ 28`), are `srvStarted`'s `"Hrds"` and flow
on unchanged in kind. Every split point, the count it splits off, and the check (`≤ 2 ^ 28`, so far
below the `805306368` available):

| consumer | where | what it splits off | check |
|---|---|---|---|
| `start` → `B` | `EtcdServer__start.lean` (pass 2) | `srvRevokePoolN = 2 ^ 28 - 1` (pool items) | `= 2 ^ 28 - 1 ≤ 2 ^ 28` ✓ |
| `start_gives_views` | server `Results.lean` | none: returns all `805306368` | — |
| `Start` → `srvStartReaders` | `EtcdServer__Start.lean` | none: passes all on | — |
| `etcdstart.Start` (`memberUp`) | `etcdstart/Start.lean:74` | none: keeps `Hrslots` whole | — |
| `auth/startServer` (`memberUpOn`) | `examples/etcd/auth/startServer.lean:189` | none | — |
| `etcdstart.kv_served` (`kvServeStocks`) | `etcdstart/Served.lean:136` | `1` (`etcdGrpcSlots_of_started … 1`, premise `N ≤ M`) | `1 ≤ 2 ^ 28` ✓ |
| `etcdstart` lease serving | `etcdstart/ServedLease.lean:177` | `1` (same lemma) | ✓ |
| `cluster3.StartMember` | `examples/lib/cluster3/StartMember.lean:260` | `1` | ✓ |
| `watch` `Main` | `examples/etcd/watch/Main.lean:242` | `1` | ✓ |
| `auth` `Main` | `examples/etcd/auth/Main.lean:197` | `1` | ✓ |
| `cache` `Main` | `examples/etcd/cache/Main.lean:317` | `1` | ✓ |
| `compactwatch` `Main` | `examples/etcd/compactwatch/Main.lean:218` | `1` | ✓ |
| `k8s/compactor` `Main` | `examples/k8s/compactor/Main.lean:186` | `1` | ✓ |
| `k8s/etcd3` `Main` (the k8s chain) | `examples/k8s/etcd3/Main.lean:170` | through `etcdstart.kv_served`: `1` | ✓ |
| the other examples (`putget`, `putget3`, `txnlin`, `lease`, `leasegrant`, `leaseexpiry`, `compacted`, `restart`) | their `Main`s | through `kv_served`/`ServedLease`: `1` each | ✓ |

Each split takes `1` slot (one gRPC slot, `N = 1`); the rest is dropped. No consumer needs more than
the new count: no stop. (The `cache` example's other `maxReaders` arithmetic, `Main.lean:462–477`, is
the cache's own lock, not `read.mux`.) Which of these proofs needed an edit, and whether only for
positional destructuring (N6's laws), is in §L.

### L. Step B: what was edited, and why (2026-11-06)

The statements of A–J are in the Lean files; the build is green with five `DRAFT revoke-open`
sorries (M). Proofs edited, by cause:

- **The count `actualMaxReaders − srvRevokePoolN` (F.1)**, one argument at each consumer of §K
  (`etcdGrpcSlots_of_started`'s `M`, and its `1 ≤ M` side condition, now `rw
  [actualMaxReaders_unseal]; simp only [srvRevokePoolN, backend.rdPoolN] <;> omega`):
  `etcdstart/Served.lean`, `etcdstart/ServedLease.lean`, `cluster3/StartMember.lean`, and the `Main`s
  of `watch`, `auth`, `cache`, `compactwatch`, `k8s/compactor`. **To redo over N6's laws at the
  merge** (they read `memberUp`'s/`kvServeStocks`'s stock directly). None of them broke for
  positional destructuring alone: the destructuring patterns of `memberUp` were unchanged (the count
  is inside a conjunct's type).
- **Positional destructuring of the server's rows** (`#Hrvkb` in the built rows, `#Hrvk` in the run
  rows; package-internal, not N6's): `BuildGap.lean` (`isServerBuilt_of_gap`), `StartOn.lean`
  (`isServerBuilt_of_gapOn`), `AuthCompRows.lean` (the four `isServerBuilt`↔`C` and four
  `isServerRun`↔`C` patterns), `ModeSpecs.lean` (`isServerBuilt_off`); and `InvBuild.lean`'s
  `srvBuilt` gains `#Hrvkb` (it is `srvBuiltG false` by `rfl`, **Δ**: not in C's list).
- **`goAttachInv` (D)**: `InvGoAttach.lean`'s lemmas re-proved over `levelToks 0 d ∗ levelToks 1 q`:
  `wp_goAttach_Add` deposits the token's level 0 (premise now `2 * threadBound GF ≤ 2 ^ 31`, **Δ**),
  `wp_goAttach_Done` returns `levelTok 0` (was `threadTok`, **Δ**), `goAttach_close` and
  `wp_goAttach_Wait` (the counter at `0` gives `d = q = 0`) unchanged in statement;
  `StopShutdown.lean`'s destructuring of the invariant. The `GoAttach` proof is pass 2's (M.1); its
  final lemma set (a pending `Add`, the fork's move from pending to started) is pass 2's design.
- **`run` (B)**: the thread token is in the loop's context (`wp_for` keeps the whole context) and
  returned at the stop; the revocable expiry arm is a DRAFT sorry (M.3).
- **`start` (C)**: `B`'s `srvRevokePoolN` items split off `Hwgs`/`Hrslots` (`replicate_takeN`,
  import `InvServe`), `#Hrvk` (M.4), `run` forked with `wp_fork_tok_body`.
- **`NewServer` (C, H)**: `leadTimeMu`'s rest kept (`HltRest`), `#Hrvkb` from it and the auth store's
  stock `HRDstock` (M.5).
- **`LeaseRenew` (Q5)**: `ensureLeadership` at level 0 (`threadTok_level0` split and rejoined).
- **`GoAttach` callers**: `wp_apply wp_GoAttach_tok hGA …` (`Start`, `sendMergedSnap`,
  `monitorLeader`); `goAttach_init` (round 2: `raftPool` premise, the doubled bound).

### M. The DRAFT sorries (pass 1) and their reach

1. `EtcdServer.GoAttach.wp_proof` (`EtcdServer__GoAttach.lean`): `GoAttach` by levels.
2. `wp_GoAttach_tok` (`GoAttachTok.lean`): the old triple from the new spec.
3. `run`'s revocable expiry arm (`EtcdServer__run.lean`).
4. `start`'s `#Hrvk` (`EtcdServer__start.lean`): the outer pool and the bundle.
5. `NewServer`'s `#Hrvkb` (`NewServer.lean`): the inner pool.

1, 2, 4 and 5 reach every result over the server (every `Start`/`GoAttach` user); 3 reaches the
revocable configuration only (leaseexpiry), which already rested on the sorry `srvRevokeOpen_open`.
`etc/tcb-report.py --check` (after the green build, 2026-11-06): exactly these five are new
(`sorry EtcdServer.GoAttach.wp_proof`, `EtcdServer.run.wp_proofG`, `EtcdServer.start.wp_proof`,
`NewServer.wp_proofG`, `wp_GoAttach_tok`); no axiom added or removed, no other change. The
baseline is not updated: pass 2 removes them. Every `Results.lean` and top-level `Adequacy`
statement is unchanged against `lean` (`aa4449beb6`) except the approved ones: the server's
`start_gives_views` (F.1) and the four etcd adequacy lemmas' `Hprog` (A, `max (n + 2) 4`).
Interfaces regenerated: `etcdstart` (`Adequacy`, `AdequacyMembers`, `Defs`, `Served`) and `backend`
(`RdPool`); `raft` unchanged. `etc/bounds-check.py --check`: ok (389).

### Δ against the Scope (for the Freeze package; consolidated)

1. `RevokeCtx.lean` holds `srvRevokesLeases` (moved from `LeaseRevoke.lean`), `srvRevokeLevels`,
   `srvRevokePoolN`, the pools and the bundles (the spec of `revokeExpiredLeases` names them and
   `LeaseRun.lean` imports that spec).
2. One `ρ` in `srvRevokeCtx` (no `ρq`): `run` is called with `{ ρ with wait := γw }`.
3. `run`'s token is in `run.spec` (pre and post), not in `isServerRun*` (Q8 (a)'s text).
4. `wp_GoAttach_tok` in its own module (`GoAttachTok.lean`), imported by the callers.
5. `auth.authStore.WithRoot.spec`'s name; no `isAuthRoot` and no kit change (G).
6. `lease.bootCfg`'s revocable arm carries `srvRevokeLevels` too (E).
7. `srvStarted`'s counts (`"Hrds"`, `"Hwgs"`) minus `srvRevokePoolN` (C).
8. F.1: the count `actualMaxReaders − srvRevokePoolN` in `start_gives_views`, `memberUp`,
   `memberUpOn`, `kvServeStocks` (accepted by etcd-grove-82).
9. `goAttach_init`: premise `2 * threadBound GF ≤ 2 ^ 31` and `raftPool (srvLgReader s)`.
10. `InvGoAttach.lean` imports `api.rafthttp.Net` (`raftPool` in `srvGoAttachOk`).
11. `raftPool` at level 1: `raftPool_borrowL`/`raftLoanL_giveBack` (proved).
12. `srvBuilt` (`InvBuild.lean`) gains `#Hrvkb` with `srvBuiltG` (L).
13. `wp_goAttach_Add`'s doubled bound, `wp_goAttach_Done`'s `levelTok 0` (L).
14. `EtcdServer__start.lean` imports `InvServe` (`replicate_takeN`).
15. F.5 (`WithRoot`'s translation, `leaseExpired`'s initializer) deferred to pass 2.

### N. Pass-2 work list

- **etcdserver, `GoAttach`** (`InvGoAttach.lean`, `EtcdServer__GoAttach.lean`, `GoAttachTok.lean`):
  the leveled lemmas (a pending `Add` depositing `levelTok 1`; the `go` statement with
  `wp_fork_tok_upd` moving the fresh token's level 0 into `d` and returning the pending level 1;
  `Done`), `GoAttach.wp_proof` (stopped branch: `raftPool_borrowL` with the caller's `levelTok 1`),
  `wp_GoAttach_tok` (split `threadTok` into level 1 for `GoAttach` and the rest for `f`).
- **etcdserver, `start`** (`EtcdServer__start.lean`): `#Hrvk`: `threadPool.initL srvRevokeOuterN 2`
  over `HwgB`/`HrdB` (`threadBound ≤ srvRevokePoolN + 1` from `%Hbound`), the off-mode views (from
  `start`'s `isServerReq`/`isServerRead`), `idCred`, `s.ctx`'s contract, `#Hrvkb`.
- **etcdserver, `NewServer`** (`NewServer.lean`): `#Hrvkb`: `initL srvRevokeInnerN 1` over
  `srvRevokePoolN` of `HltRest` and of `HRDstock` (`2 ^ 28 + 60` left), `HrPool`, the auth store's
  pointer.
- **etcdserver, `run`** (`EtcdServer__run.lean`): the revocable arm: `lease.runCfg_revoke Hmo` gives
  `⟨hlev, hrev⟩`, `srvRevokesLeases` from `Hmo` and `hCoff`, the call with `#Hrvk` and the token.
- **etcdserver, `revokeExpiredLeases`**: its `wp_proof` (new `Proof/…/EtcdServer__revokeExpiredLeases.lean`)
  over `GoAttach`, `ensureLeadership` (level 3), `WithRoot`, `LeaseRevoke`, `Logger`; `MainLinked`
  links `srvRevokeOpen_intro` and the sorry `srvRevokeOpen_open` goes; `gen-link` regenerated.
- **auth**: translate `WithRoot` (`auth.toml`) and prove `authStore__WithRoot.spec`; `leaseExpired`'s
  initializer (`etcdserver.toml`, `etc/gen-init.py` `SPECIAL`).
- **Reviews**: the `axiom` skill on `ensureLeadership.wp_proof` (`levelTok l`) and on
  `authSchemaSrv`'s count; the Go stats test (Q11).
- **At the merge with N6**: redo §L's first item over `memberUp`'s laws.

## Draft pass 2: auth (2026-11-06)

§N's item **auth**, both by the Scope's preferred route (Q10): no axiom, no `sorry`, no trust growth.

- **`WithRoot`'s translation.** `Code/go_etcd_io/etcd/server/v3/auth.toml`: `"authStore.WithRoot"`
  added to `translate`; `etc/goose.py --project etcd` regenerated `Code/.../auth.lean` (the body,
  `store.go:1175`, and `authStore.TypeAssumptions`' `ptr_WithRoot_unfold`). Goose's reach was already
  translated or names-only (`context.WithValue`, `metadata.New`/`NewIncomingContext`,
  `tokenSimple.genTokenPrefix`, `TokenProvider.assign`, `zap.Error`); `etc/goose.py --check` passes.
- **`authStore.WithRoot.wp_proof`** (`Proof/go_etcd_io/etcd/server/v3/auth/authStore__WithRoot.lean`,
  new): I.3's statement unchanged; the proof applies the precondition's `IsAuthEnabled` triple and
  takes the `return ctx` branch (the auth-on branch is unreachable under `b = false`). Not linked yet:
  `revokeExpiredLeases`' proof cites it (`gen-link` with that proof).
- **`leaseExpired`'s initializer** (F.5). `Code/.../etcdserver.toml`: `"leaseExpired"` added to
  `translate` (`etcdserver.lean`: `leaseExpired.init`'s axiom gone, the initializer is
  `prometheus.NewCounter(prometheus.CounterOpts{...})`, a `GlobalAlloc` of a `Counter`).
  `etc/gen-init.py`'s `SPECIAL[...etcdserver]`: `alloc_types` `GoInterface`, `before` its two steps
  (`EtcdGrove.prometheus.wp_counterOptsLit`, `NewCounter.wp_proof`: the read package's existing
  trust-boundary axioms, no new one), `ipersist HleaseExpired`, the import of `NewCounter`; the
  regenerated `etcdserver/Init.lean` drops `leaseExpired.init` from `opaqueInitsOk`'s list;
  `etc/gen-init.py --check` passes.
- **The fact** (an exported definition, applied as DRAFT): `srvApplyLoopInit` (`BaseApply.lean`)
  gains a last conjunct, old → new:

  ```lean
  -- old (last conjunct)
      (∃ g : GoInterfaceOk, globalAddr applySnapshotInProgress ↦□ GoInterface.ok g ∗
        go_etcd_io.etcd.server.v3.storage.mvcc.gaugeSpec g))
  -- new
      (∃ g : GoInterfaceOk, globalAddr applySnapshotInProgress ↦□ GoInterface.ok g ∗
        go_etcd_io.etcd.server.v3.storage.mvcc.gaugeSpec g) ∗
      (∃ c : GoInterfaceOk, globalAddr leaseExpired ↦□ GoInterface.ok c ∗
        go_etcd_io.etcd.server.v3.storage.mvcc.counterSpec c))
  ```

  `revokeExpiredLeases`' proof takes the counter from `isPkgInit` (`icases Hinit with ⟨-, -, -, -, -,
  ⟨%c, #Hc, #Hcs⟩⟩`). The only pattern it broke: `SnapApplyWalk.lean`'s `⟨-, -, -, -, ⟨%gg, #Hgg,
  #Hggs⟩⟩` → `⟨…, ⟨%gg, #Hgg, #Hggs⟩, -⟩`.

## After merging N6 (2026-11-06)

`lean` (with N6, "`memberUp` through laws", `572b213a8d`) merged into `revoke-open` at `87eed67c20`:
no textual conflict, and the merge built green as it stood. What §L's first item ("to redo over
N6's laws at the merge") became:

- **The count is named** (DRAFT, an etcdstart addition): `etcdstart.memberReadN : Nat :=
  Int.toNat sync.rwmutex.actualMaxReaders - srvRevokePoolN` (`Defs.lean`), with the law
  `one_le_memberReadN : 1 ≤ memberReadN`. `memberUp`, `memberUpOn` and `kvServeStocks` write the
  read loop's stock at `memberReadN`; the eight consumers of §L (`kv_served`, `ServedLease`,
  `cluster3/StartMember`, the `watch`, `auth`, `cache`, `compactwatch`, `k8s/compactor` `Main`s)
  pass `memberReadN` as `etcdGrpcSlots_of_started`'s `M` and `one_le_memberReadN` as its `1 ≤ M`,
  instead of the literal count and its `actualMaxReaders_unseal` arithmetic. A later change of the
  count changes `memberReadN` and its law's proof only. The server side (`srvStartReaders`,
  `srvStarted`, `start_gives_views`) keeps F.1's literal text; `etcdstart.Start` and authkv's
  `startServer` pass `start`'s stock on by unfolding (`memberReadN` is a plain `def`, defeq).
- **The laws' statements, old → new (DRAFT):** `memberUp_served`, `memberUpOn_served` and
  `memberUpOn_intro` are unchanged in text (they name `kvServeStocks`). Their content changes by
  F.1's count only, through `kvServeStocks`:

  ```lean
  -- lean (N6)
      ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
        srvReadReader s γr) ∗
  -- revoke-open
      ([∗list] _x ∈ List.replicate memberReadN (), srvReadReader s γr) ∗
  ```

  and the same in `memberUp` and `memberUpOn` (`srvReadReader s ρ.rd`). Nothing else in the laws.
- **No consumer unfolds `memberUp`/`memberUpOn`** outside etcdstart: `grep -rn "unfold.*memberUp\b\|
  memberUp at\|memberUpOn at" Proof | grep -v /etcdstart/` is empty.
- **Closed theorems**: against `lean`, every `Results.lean` and `Adequacy*` differs only by the
  approved changes (`start_gives_views`, F.1; the four etcd adequacy lemmas' `Hprog` at
  `max (n + 2) 4`, A); leaseexpiry's `Adequacy.lean` differs in a proof only.
- **The partition's docstrings** (`backend/RdPool.lean`: the header, `rdPoolN_add_rdStockN`) now say
  what the `actualMaxReaders` slots count: the `readTx.mu` read locks taken with an `rdTok`, not
  `monitorStorageVersion`'s, which takes one without (`notes/axiom-review/authrdn-count.md`,
  attack 6; harmless: Go's readers are live goroutines, at most the thread bound).
- **Checks** (after the merge, green build): `etc/tcb-report.py --check` reports exactly the five
  DRAFT sorries of §M as new and nothing else (no axiom added or removed). `leaseExpired.init`'s
  axiom is gone from `Code/.../etcdserver.lean` (pass 2's translation), but `etc/tcb-baseline.txt`
  never listed it, so the check shows no removal. Interfaces: etcdstart's `Defs`/`Served` (the
  count's name, `memberReadN` and its law added), backend's unchanged; `etc/api-check.py` and the
  layout checks pass for both; `etc/bounds-check.py --check`: ok (389).
