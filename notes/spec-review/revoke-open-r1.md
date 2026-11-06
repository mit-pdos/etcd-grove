# Spec review: revoke-open, round 1

Reviewer: independent subagent, 2026-11-06. Branch `revoke-open` at `abe33cf212` (worktree
`/shared/etcd-grove-leaseexp`). That commit adds only a note to `7bb0859c28`, the commit the brief
named. Diffs are against `git diff lean...HEAD`. The Go code is the pinned fork
(`.lake/go-src/etcd`, `249d76bea7`): `server.go:860-905` `revokeExpiredLeases`, `:917-944`
`ensureLeadership`, `:2435-2452` `GoAttach`, `auth/store.go:1175` `WithRoot`. The only file I
wrote is this one.

Commands run, none of which builds:
- `etc/tcb-report.py --check --reuse` (on `.lake/tcb.json`, computed at `7bb0859c28`), main baseline
  and `--collection etc/tcb-collections/leaseexpiry.txt`;
- `etc/bounds-check.py --check` (ok, 389 = baseline);
- `etc/api-check.py etc/api/etcdstart.txt --check` (no new error).

**Verdict: no BLOCKER.** Each frozen statement is still a true triple of its Go function. Each
change to them is needed, and the closed theorems keep their text. `etcd_leaseexpiry_safe` has no
`sorry` and every premise is discharged (`.lake/tcb.json`: `sorries = []` for
`etcd_leaseexpiry_safe`, `leaseexpiry_Main` and `EtcdServer.wp_revokeExpiredLeases`). There are
four SHOULD-FIXes:
- the revocation's sealed bundles are opened by laws that restate their bodies, and one conjunct is
  a tautology;
- a server-internal pool size, `srvRevokePoolN`, is written into etcdstart's hub definitions and
  into the exported `start_gives_views`;
- `WithRoot.spec` is stated as its implementation's call to `IsAuthEnabled`, which costs its one
  caller about 20 lines of glue;
- the literal `4` appears both in `srvRevokeLevels` and in the four adequacy lemmas' `max (n + 2) 4`.

There is also one process item: the trust baselines are stale (P1). I found no Go bug, so nothing
goes to `issues/`.

## 1. The frozen statements

### `EtcdServer.revokeExpiredLeases.spec` (`Spec/.../EtcdServer__revokeExpiredLeases.lean:42-52`)

**Good.**
- It is true of `server.go:860-905`. It is proved (`EtcdServer__revokeExpiredLeases.lean`, no
  `sorry` in `.lake/tcb.json`) from callee specs only.
- The changes are what the Go code needs. The `threadTok` is lent at level 1 to the outer `GoAttach`,
  and level 2 borrows `B`'s `wgMu` slot for it. `srvRevokeLevels` is needed because the outer
  goroutine holds levels 1–3 at once at `ensureLeadership`. `srvRevokeCtx` supplies the reader
  slots that unbounded overlapping rounds need.
- The post gives the token back, and `run` needs it again on its next expiry.
- `run` discharges both pure premises at its call site (`EtcdServer__run.lean:1319-1328`):
  `srvRevokesLeases` from `runCfg_lm` and `Hg.2`, `srvRevokeLevels` from `lease.runCfg_revoke`.
- The plan's open question of `ρ` versus `ρq` is settled: the spec is at `run`'s `ρ`, the one
  `isServerRunC`'s `#Hrvk` carries.

**NIT 1.1: the pure premises are Lean implications** (`:46`), not `⌜…⌝` conjuncts of the
precondition. PRINCIPLES "Pure premises go in the precondition" says to convert a spec's premises
when the spec changes, and this one changed. The fix is
`{{ … ∗ ⌜srvRevokesLeases E ρ ∧ srvRevokeLevels⌝ ∗ … }}`. Its one caller, `run`, changes
`hRL hlev` to an `ipureintro`.

**NIT 1.2: half of `srvRevokesLeases` follows from the precondition.**
- `lease.expiredLeases (srvGrantGuard E.lg E.authMode.isOn) ls` has a non-empty list
  (`LessorBackend.lean:156`). Each element meets `⌜lg = true ∧ on = false⌝`
  (`InvApplier.lean:495-496`), and `E.authOn` is `E.authMode.isOn` (`apply/Chain.lean:706`). So
  `E.authOn = false` already follows.
- Only `ρ.rd.kv.lm = .revocable` is new information.
- This is harmless, since `srvRevokesLeases` is an existing named pair that `LeaseRevoke.spec`
  takes. The docstring could say the auth half is implied.

### leaseexpiry's `Main.spec` (`Spec/.../leaseexpiry/Main.lean:54-56`)

**Good.**
- The one new premise, `srvRevokeLevels`, is necessary. `Main` builds `lease.runCfg .revocable`
  (`Main.lean:119`), and no point of the proof holds enough tokens to derive `4 ≤ threadBound` (the
  plan's Q1 (c4)).
- The closed theorem discharges it from `HT`:
  `leaseexpiry/Adequacy.lean:161`, `(by show 4 ≤ threadBound _; rw [HT]; omega)`.
- `etcd_leaseexpiry_adequate`'s statement is unchanged.

**NIT 1.3:**
- That discharge goes through `show`, which unfolds `srvRevokeLevels` by definitional equality: the
  client unfolds the owner's definition.
- Fix: add an intro law next to the definition, `srvRevokeLevels_of (h : 4 ≤ threadBound GF)`. With
  S4 below, it becomes `srvRevokeLevels_of_max : threadBound GF = max m srvRevokeK → srvRevokeLevels`.

### `EtcdServer.run.spec` (`Spec/.../EtcdServer__run.lean:57-66`)

**Good.**
- The change is minimal: `threadTok` in the pre and in the post.
- It is true: `start` forks `run` with `wp_fork_tok_body`, and Go's `run` returns at stop.
- It is necessary (Q8: the expiry arm's `GoAttach` and `B`'s loan come from this token).
- It touches nothing else in the statement. The `#Hrvk` conjunct is inside `isServerRunC`'s body.

**NIT 1.4:**
- The docstring (`:53-55`) names levels 1 and 2 and the outer pool. Those are the proof's layout,
  and they will go stale if the layout moves.
- Suggested wording: "`run` holds a thread token, which it returns: its expiry arm starts goroutines
  whose reader slots are backed by it."

## 2. The hub statements

### The four etcd adequacy lemmas (`etcdstart/Adequacy.lean:155,164,204,212`, `AdequacyMembers.lean:60,87`)

**Good.**
- `realThreadsBelow_mono` (`Proof/runtime/Threads.lean:68-72`) is a correct, pure monotonicity
  lemma.
- `T = max (n + 2) 4` is a sound choice for `goose_adequacy_start`.
- The 15 closed theorems' `Hn : n + 2 ≤ 2 ^ 28` still give `threadBound ≤ 2 ^ 28`.
- The interfaces (`interface/.../etcdstart/Adequacy.txt`, `AdequacyMembers.txt`) were regenerated.
  They differ only in `Hprog`.

**SHOULD-FIX S4: the literal `4` appears in two places.**
- They are `srvRevokeLevels := 4 ≤ threadBound GF` (`RevokeCtx.lean:55`) and the adequacy lemmas'
  `max (n + 2) 4`. The only link between them is a docstring (`Adequacy.lean:191-192`).
- PRINCIPLES "A size bound shared between specs is written with its named constant, not the number":
  if the layout gains a level, both must change and nothing checks that they agree.
- Fix: define `@[word_unfold] def srvRevokeK : Nat := 4` beside `srvRevokeLevels`, with
  `srvRevokeLevels := srvRevokeK ≤ threadBound GF`, and write `max (n + 2) srvRevokeK` in the four
  `Hprog`s. The closed proofs' `omega` still go through (`word_unfold`).

**NIT 2.1:** `Adequacy.lean:8`, the file header, still says the lemmas run "at … the thread bound
`n + 2`". That is now true only of `init_adequate`.

### `etcdstart.memberReadN` (`etcdstart/Defs.lean:335-341`), in `memberUp`, `memberUpOn` and `kvServeStocks`

**Good.**
- Naming the count, with the law `one_le_memberReadN`, keeps eight consumers from restating the
  arithmetic. Each now passes `memberReadN … one_le_memberReadN` (for example
  `etcd/auth/Main.lean:194-196`), and none unfolds it.

**SHOULD-FIX S2: the count is the server's, but it is defined in the hub over a server-internal
constant.**
- The body is `Int.toNat sync.rwmutex.actualMaxReaders - srvRevokePoolN`, and it is exported
  (`interface/.../etcdstart/Defs.txt`, `def etcdstart.memberReadN … - srvRevokePoolN`).
  `srvRevokePoolN` is the size of the revocation's outer pool (`RevokeCtx.lean:59`), an internal of
  etcdserver.
- The same expression is also written out in the exported `start_gives_views`
  (`etcdserver/Results.lean:2252`), in `srvStarted` and in `srvStartReaders` (`InvStart.lean`).
- `one_le_memberReadN`'s proof unfolds `srvRevokePoolN`, `backend.rdPoolN` and the
  `actualMaxReaders` seal in etcdstart (`Defs.lean:341`). That is a client unfolding another
  package's definitions (PRINCIPLES "A client does not unfold…").
- The owner of the read loop's slot count is the server's `start`. Under PRINCIPLES "A bound is
  reasoned about where it is owned" and "Name the abstraction", that name belongs in etcdserver.
- Fix:
  - Define `srvStartReadN : Nat := Int.toNat actualMaxReaders - srvRevokePoolN` in `InvStart.lean`
    beside `srvStartReaders`, with `one_le_srvStartReadN`.
  - Write it in `srvStarted`, `srvStartReaders` and `start_gives_views`.
  - Make `etcdstart.memberReadN` either that name or an abbreviation of it, with its law proved by
    citing the server's.
  - A later change of the revocation's pool then changes one body in etcdserver and no exported
    text.

**NIT 2.2:** `start_gives_views`'s docstring (`Results.lean:2236-2244`) still describes the slots as
"the read loop's lock's reader slots", with no word on the slots `start` now keeps for the
revocation.

## 3. Exported statements

### `GoAttach.spec` (`Spec/.../EtcdServer__GoAttach.lean:40-47`) and `wp_GoAttach_tok` (`GoAttachTok.lean:35-71`)

**Good.**
- It is true of `server.go:2435-2452`, and it is proved:
  - `Add` deposits the caller's `levelTok 1` as a pending add (`goPending`), and the `go` statement
    returns it (`goAttach_fork`, `InvGoAttach.lean:313-344`).
  - The counter is `d + q < 2T`.
  - The stopped branch borrows `lgMu` from `raftPool` with the idle level 1.
- It is stronger than the old spec: the old triple follows as the corollary `wp_GoAttach_tok`, so
  this is one spec with one lemma, not a second spec.
- It drops a premise (`srvLgReader`).
- No caller outside etcdserver sees levels: v3rpc's `monitorLeader` uses `wp_GoAttach_tok`.

**NIT 3.1: `wp_GoAttach_tok` keeps an unneeded premise.**
- It takes `srvLgReader s` and returns it untouched (`GoAttachTok.lean:38`, `iframe Hlr` at the end).
  That premise only reproduces the old triple's text, and PRINCIPLES "After a change, drop what
  existed only for what it changed" applies.
- Fix: drop it. Each of the six callers (`Start`, `applyEntryNormal` ×3, `sendMergedSnap`,
  `monitorLeader`) keeps its slot in its frame, about a one-token edit each.

**NIT 3.2:** the spec fixes level 1 because `raftPool` is at level 1 (Q3). The docstring says so in
passing. One sentence saying that the level must be `raftPool`'s would stop a future layout change
from moving one without the other.

### `srvGoAttachOk` (`InvGoAttach.lean:127-132`)

**Good.**
- `2 * threadBound GF ≤ 2 ^ 31` is exactly what `wp_goAttach_Add`'s counter needs (started plus
  pending), and `isServer`'s `≤ 2 ^ 28` gives it.
- `raftPool (srvLgReader s)` is the persistent handle of the stopped branch.
- The bound sits inside the owner's protocol, as `notes/bounds-plan.md` asks.

### `srvRevokeBuilt`, `srvRevokeCtx`, `srvRevokeLevels` and their laws (`RevokeCtx.lean`)

**Good.**
- The two pools are bundled by role (`B` for the outer goroutine, `I` for the inner) and leveled by
  the table in the file header. Both pools are persistent.
- `srvRevokeBuilt_raftPool` is the right kind of law: a narrow elimination for `start`'s consumer.
- `srvRevokeLevels` lives in the owner and is carried only by the revocable arm of the sealed
  `lease.runCfg`. So no spec between the adequacy theorem and the owner spells `threadBound` (bounds
  check unchanged at 389).

**SHOULD-FIX S1: the sealed bundles are opened by laws that restate their bodies, and the consumer
unfolds the rest.**
- `srvRevokeBuilt_parts` (`:123-128`) and `srvRevokeCtx_parts` (`:161-171`) state the whole body,
  and `_intro` (`:111-121`, `:149-159`) restates it again. PRINCIPLES (the slot convention) says
  elimination laws "give what their consumer takes, never the slot's body restated, or the hub's
  proof changes with the body".
- With these laws, adding a conjunct changes four statements and every caller's destructuring
  pattern. The seal saves nothing.
- The one consumer, `revokeExpiredLeases.wp_proof`, then unfolds:
  - `srvRevokeLevels`, `backend.rdPoolN`, `srvRevokeOuterPool` and `srvRevokeInnerPool`
    (`EtcdServer__revokeExpiredLeases.lean:66-79`);
  - `srvGoAttachOk` (`:85`);
  - `srvAuthAt`, `apply.isAuthStore` and `auth.enabledVerdict` (`:102-116`; the last two are other
    packages');
  - `lease.expiredLeases` (`:197`) and `mvcc.counterSpec` (`:274`).
- Fix:
  - Replace `_parts` by one narrow elimination per use:
    - `srvRevokeCtx_outerBorrow`: `levelTok 2` gives a loan and `srvWgReaderAt s γg ∗
      srvReadReader s γr`, with its give-back;
    - `srvRevokeCtx_innerBorrow`: `levelTok 1` gives a loan and `srvLeadTimeReader s ∗ E.RD`;
    - `srvRevokeCtx_bound`: `threadBound GF ≤ 2 ^ 30 - 1`, which is all `ensureLeadership` needs;
    - `srvRevokeCtx_views`: auth off gives `isServerReq ∗ isServerRead`;
    - `srvRevokeCtx_ctx`.
  - Make `_intro` take the pieces `start` has.
  - Make the pool definitions `@[no_expose]` with their borrow laws.

**NIT 3.3: a tautological conjunct.**
- `⌜E.authOn = false → E.authMode = auth.AuthMode.off⌝` (`RevokeCtx.lean:138`, repeated at
  `:152` and `:165`) holds of every `E`. `AuthMode.isOn` is `false` only at `.off`
  (`auth/Model.lean:381-383`), and `AEnv.authOn` is `authMode.isOn`.
- PRINCIPLES "No constant or conjunct whose reason you do not know: a fact that holds of every
  reachable state is one law of the vocabulary". Make it a lemma, `AEnv.authMode_off_of_authOn`, and
  remove it from the bundle.

**NIT 3.4: a duplicated bound.**
- `srvRevokeBuilt` also carries `⌜threadBound GF ≤ backend.rdPoolN⌝` (`:95`). That bound already
  sits beside it as `%Hbound` in each of `isServerBuilt`, `isServerBuiltC`, `isServerBuiltOn` and
  `srvBuiltG`.
- It is needed in `isServerRun`, which has no `%Hbound`, so it is not wrong. But
  `ensureLeadership` needs only `threadBound ≤ 2 ^ 30 - 1`. With S1's `srvRevokeCtx_bound`, the
  body could hold that consumer-shaped fact instead.

### `lease.runCfg` and `lease.bootCfg` (`LeaseRun.lean:84-86`, `LeaseApi.lean:65-68`)

**Good.**
- Both are sealed (`@[no_expose]`). The revocable arm is `srvRevokeLevels ∧ srvRevokeOpen`.
- `runCfg_revocable` and `runCfg_revoke` are the intro and the elimination, and `run` and `Main`
  use only those. cluster3 (`lm ≠ .revocable`) is untouched.
- The `max (n + 2) 4` ↔ `srvRevokeLevels` pair is confined to leaseexpiry, as the Scope intended.

**NIT 3.5:** `lease.bootCfg_revocable` (`LeaseApi.lean:89`) has no caller in the tree, and its
statement changed. That is a candidate for removal, or at least worth checking that it is still
wanted.

### backend `authRdN` / `rdStockN_val` (`RdPool.lean:56,76`)

**Good.**
- The partition arithmetic is right: `2 ^ 28 + (2 ^ 28 + 2 ^ 7) + 536870783 = 2 ^ 30 - 1`, by
  `decide` in `rdPoolN_add_rdStockN`.
- The new header paragraph is an honest margin. It says the slots count the `rdTok` holders, with
  one uncounted reader (`monitorStorageVersion`), and that Go's limit is still not reached.

**NIT 3.6:**
- `2 ^ 28 + 2 ^ 7` is a number whose reason is the revocation's inner pool,
  `srvRevokePoolN = rdPoolN - 1` copies.
- Writing it `rdPoolN + 2 ^ 7` says why (the revocation needs one pool's worth) and keeps the two in
  step if `rdPoolN` moves. `rdStockN_val`'s statement is then unchanged.
- Coupling note: a backend constant is now sized by a consumer two packages up. The docstring says
  so, which is the minimum.

### `srvApplyLoopInit`'s `leaseExpired` conjunct (`BaseApply.lean:448-450`)

**Good.** It is true of the translated initializer (`prometheus.NewCounter`, through existing
trust-boundary specs), and no axiom was added for it.

**NIT 3.7:**
- The counter belongs to the revocation, not to the apply loop.
- `srvApplyLoopInit` is an `abbrev` that callers destructure by position. Adding a conjunct broke
  `SnapApplyWalk.lean`'s pattern, and the revocation proof destructures `srvInit` by position too.
- A named conjunct (`srvRevokeInit`) with a law would avoid both.
- The proof unfolds `mvcc.counterSpec` (`:274`), so mvcc is missing an `Inc` law.

### `authStore.WithRoot.spec` (`Spec/.../auth/authStore__WithRoot.lean:30-37`)

**Good.**
- It is true of `store.go:1175-1178`: with `IsAuthEnabled` false, it returns `ctx`. It is proved
  with no axiom.
- Its restriction to auth off is stated as a scope restriction, and only the auth-off branch is
  claimed.

**SHOULD-FIX S3: the premise is the implementation's call, not the store's state.**
- The spec takes `□ {{ RD }} st.IsAuthEnabled() {{ b, RD ∗ ⌜b = false⌝ }}`. That premise says how
  `WithRoot` is written, not what holds of the store. Another `WithRoot` that read `as.enabled` under
  `enabledMu` would not be provable from this spec (PRINCIPLES "The spec of an API, not of an
  implementation").
- It also does not fit its one caller:
  - `revokeExpiredLeases.wp_proof` spends about 20 lines (`:96-117`) building the premise from
    `apply.isAuthStore`'s clause.
  - That clause is stated over interface dispatch (`methods ai.ty …`, `apply/Contracts.lean:232`)
    and `auth.enabledVerdict M b`.
  - To build it, the proof unfolds `srvAuthAt`, `apply.isAuthStore` and `auth.enabledVerdict`, all
    three from outside the package.
- Two fixes, in order of preference:
  - (a) State it in the auth package's own vocabulary, as `IsAuthEnabled.spec` is (`authInv st R M ∗
    enabledRd st M ∗ ⌜M = .off⌝`, slot returned). Then add the law on the server side that gets
    those pieces from `srvAuthAt`.
  - (b) If the server cannot reach `authInv`, keep the contract form but at the shape the caller
    holds: `enabledVerdict M b` with `⌜M = .off⌝`. Also put the converted contract in
    `srvRevokeCtx`, built once in `start` (the plan's Q7 `srvWithRootOk`, which pass 1's G dropped),
    so that the revocation's call is one `wp_apply`.
- Either way, the auth-on case later extends this spec in place and does not need a second spec.
- (Separate, recorded in `notes/perennial-changes.md`: `wp_apply hWR …` gave up silently with a
  `sorry` here. The proof works around it with an explicit `wp_bind` (`:125`), and `.lake/tcb.json`
  confirms no `sorry` remains.)

### `start_gives_views`'s count

See S2. The exported result names `srvRevokePoolN`.

## 4. The two trust-boundary restatements

### `ensureLeadership.spec` (`Spec/.../EtcdServer__ensureLeadership.lean:46-53`)

**Good.**
- `threadTok` becomes `levelTok l` with `l` caller-chosen, taken and returned. So no counted
  resource comes out of nothing (PRINCIPLES "A trusted statement never gives out a counted resource
  it did not take").
- The faithfulness argument never used the token's identity: `tickMu` readers are at most the live
  goroutines, fewer than `threadBound ≤ 2 ^ 30 - 1`.
- Taking a level token weakens the precondition, and the claim stays true of `server.go:917-944`.
- The docstring was updated with both callers (`LeaseRenew` at level 0, the outer goroutine at
  level 3).
- Expected TCB effect: the leaseexpiry collection now rests on this axiom (P1).

### `authSchemaSrv`'s count (`AuthSrv.lean:81-106`, through `backend.authRdN`)

**Good.**
- The text is unchanged. The premise trades `authRdN` `rdTok`s (`authRdSlots`) for `authRdN`
  tickets, one for one, so it mints nothing.
- The new count stays inside the backend's partition (§3, `authRdN`).
- The `IsAuthEnabled` route the revocation uses needs auth off (`srvRevokesLeases`), where `E.RD` is
  `NewAuthStore`'s `enabledMu` slot. I did not re-derive the auth-on supply of 2^28+127 `authRd`
  copies against the store's own locks. It is built (so proved), but **uncertain** as to intent.

## 5. Closed theorems

- `git diff lean...HEAD -- '*Results.lean' '*Adequacy*'` touches four files:
  - `etcdserver/Results.lean`, only `start_gives_views`'s count (`:2252`);
  - `etcdstart/Adequacy.lean` and `AdequacyMembers.lean`, the four `Hprog`s plus docstrings and
    proofs;
  - `leaseexpiry/Adequacy.lean`, one line in the proof (`:161`), none in the statement.
  This is as the brief allows.
- `etcd_leaseexpiry_adequate`/`_safe` is still a meaningful no-panic claim: the main thread returns
  `#()`, no thread is stuck, and no value is a panic.
- Every premise of `Main.spec` is discharged in its Adequacy:
  - `threadBound ≤ 2 ^ 28` and `srvRevokeLevels`, from `HT` and `Hn`;
  - `receiptBound`'s two, from `HN`;
  - the write budget;
  - the named workload and boot premises, unchanged from `lean`.
- `srvRevokeOpen` is now `srvRevokeOpen_intro EtcdServer.wp_revokeExpiredLeases`
  (`MainLinked.lean:54`), so the `sorry` is gone from this result.

## Process

**P1: the trust baselines are stale.**
- `etc/tcb-report.py --check --reuse` reports "gone from the trust base: sorry srvRevokeOpen_open"
  for the main baseline (`etc/tcb-baseline.txt:795`).
- For the `leaseexpiry` collection it reports that `sorry` gone and "NEW: axiom
  `EtcdServer.ensureLeadership.wp_proof`". That axiom is expected, but it should be listed in the
  Freeze package as a collection that now rests on the restated axiom.
- Run `--check --update` for both before landing.

## Go code

No bug found.
- Nothing in `revokeExpiredLeases` can panic for the non-nil leases `expiredC` delivers.
- When `GoAttach` is skipped while the server stops, `c` stays full, and the outer loop's `select`
  then leaves on `stopping`.
- `GoAttach` adds to the wait group only under `wgMu`'s read lock, after it has checked that the
  server is not stopping.

Nothing for `issues/`.

## Ranking (most in need of revision first)

1. `RevokeCtx.lean` (`srvRevokeCtx`/`srvRevokeBuilt`): S1 (body-restating laws and the consumer's
   unfolds), NIT 3.3, NIT 3.4.
2. `etcdstart.memberReadN` / `start_gives_views` / `srvStartReaders`: S2 (a server-internal
   constant in hub and exported text).
3. `authStore.WithRoot.spec`: S3 (an implementation-shaped premise, about 20 lines of caller glue).
4. The adequacy lemmas and `srvRevokeLevels`: S4 (literal `4` in two places), NIT 2.1, NIT 1.3.
5. `revokeExpiredLeases.spec`: NIT 1.1, NIT 1.2.
6. `GoAttach.spec` / `wp_GoAttach_tok`: NIT 3.1, NIT 3.2.
7. backend `authRdN`: NIT 3.6. `srvApplyLoopInit`: NIT 3.7. `lease.bootCfg_revocable`: NIT 3.5.
8. `run.spec` (NIT 1.4, its docstring), `Main.spec`, `srvGoAttachOk`, `lease.runCfg`, the
   `ensureLeadership` restatement, and `authSchemaSrv`'s count: good as they are.
