# Review: mvccfull F1 Draft, the tester's specs and invariants (round 1)

Reviewer: independent subagent, 2026-11-09, at `d89ff215b4` (the specs are those of `a4c071c7dd`;
`d89ff215b4` only adds notes). Judged by `.claude/skills/spec/PRINCIPLES.md`. The targets are mostly
internal specs of one program, so the focus is on four questions. Is each spec true of the Go code?
Can each caller establish the precondition and get what it needs from the postcondition? Can every
`check(...)` be proved from the invariants and mvcc's contracts (`Api.lean`, `ApiState.lean`, the
candidates `ApiWatchR`/`ApiErrVars2`/`ApiNewRestoring`)? Is each invariant strong enough for that?
I formed my view before reading `notes/mvccfull-proof-plan.md`, and read it afterwards to check
stated decisions ("Found" 2 there is the notified-log bound, which F1 below shows is still not enough).

No bug was found in etcd's Go code; nothing goes to `issues/`. The tester's own Go has one weakness
(S5, a restriction it does not actually enforce). It belongs in `notes/`, not `issues/`.

## First tier (a false spec, or a check that cannot be proved as drafted)

### F1. `receive`'s `resp.Revision <= m.revHi` is not provable when the response is at the pending revision

- **Principle:** completeness. The invariants must prove every check.
- **Code:** `mvccfull.go:1403`. mvcc notifies a revision before it commits it: in
  `watchableStoreTxnWrite.End`, `notify` comes before `TxnWrite.End`. So a response can carry
  `σ.rev + 1` while that revision is still pending. `wsRecvOk` clause 1
  (`ApiState.lean:181`) gives only `r.rev < σ.notifiedLog.length`.
- **What the draft gives:** the receiver learns `σ` at time t1 (`recv_facts`, `Streams.lean:319`)
  and loads `revHi` at a later t2. What carries over from t1 to t2 is `readQ`
  (`Readers.lean:214`), which holds only `monoNatLbOwn m.rev σ.rev`, a lower bound on the
  *committed* revision. `revHi_acc` (`Readers.lean:272`) turns that into `σ.rev ≤ revHi(t2)`.
- **The gap:** the case that matters is `r.rev = σ.rev + 1`. `memberState`'s
  `|σ.notifiedLog| ≤ revHi + 1` (`Members.lean:279`) holds at each instant. Using it at t2 would
  need `|notifiedLog(t2)| ≥ |notifiedLog(t1)|`, and no ghost state records that `|notifiedLog|`
  only grows. `revHi` itself is not monotone: `end` stores `p.rev - 1` after a transaction without
  changes (`mvccfull.go:851-858`).
- **The check is true in Go:** once revision `r` has been notified, `revHi ≥ r` from then on. So
  this is a missing invariant, not a bug.
- **Affects:** `stream.receive.spec`, its header's "clause 1, against `revHi` loaded after".
- **Fix:**
  - Add a second monotone counter `m.nrev` to `MemberNames`, at `|σ.notifiedLog|`, kept in
    `memberState` and carried in `memberCarry`.
  - `readQ` (or `recv_facts`) exports `monoNatLbOwn m.nrev |σ.notifiedLog|`.
  - Add a law `nrevHi_acc`: `incLive ∗ monoNatLbOwn m.nrev n ⊢ … ⌜n ≤ revHi + 1⌝`.
  - `|notifiedLog|` only grows within an incarnation: a notify adds one; a commit or a compaction
    keeps the length; `Restore` runs with nothing pending and `σ.log <+: σ'.log`. Across a restart
    it is unchanged.
  - Keep `m.rev` on the committed revision: `revLo ≤ σ.rev` needs it.

### F2. `memberState` lacks the bounds that `watch`'s floating window and `watcherOk` need

- **Principle:** completeness: the invariant is too weak for `stream.watch.spec`.
- **Code:** `mvccfull.go:1297`, `1311-1319`. `watch` sets `w.floatLo = revLo + 1`,
  `w.rev = revHi + 1` and `w.start = 1 + choose(revHi + 2)`. Two of the obligations that follow
  have no source:
  - **(a) `revLo ≥ 0`.** `wPosOk'` (`Streams.lean:126`) takes the floating branch only when
    `0 < floatLo`, which needs `revLo ≥ 0`. `memberState` (`Members.lean:278-281`) bounds `revLo`
    only from above (`revLo ≤ σ.rev`). If `floatLo ≤ 0`, the other branch asks
    `posOk Hl mt lo (hi+1) 0 0`, i.e. no expected change in `[σ.rev+1, hi+1)`. That is false in
    general, because `hi` is loaded after `Watch`. The Go code agrees with the invariant here: its
    anchoring is gated on `w.floatLo > 0` (`mvccfull.go:1447`).
  - **(b) An upper bound on `revHi`.** `watcherOk` (`Streams.lean:136-144`) needs
    `start < 2^63 - 1`, and `wPosOk'` needs `rev < 2^63 - 1`. Nothing bounds `revHi` from above:
    `revHi_acc` gives only lower bounds, and `readQ`'s `|σ.log| + 3 ≤ 2^63` is about `σ`, not
    `revHi`. `revHi ≤ σ.rev + 1` is no fix either: it is false during `restore`, which stores
    `revHi = b.rev` before `Restore` (`mvccfull.go:555`).
- **Fix:** add `1 ≤ sint.Z b.1` and an absolute ceiling such as `sint.Z b.2.1 < 2^62` to
  `memberState`/`memberCarry`. The writer can keep it: revisions ≤ 2 + `Ops` < 2^39. Then
  `revLo_acc` returns `1 ≤ v`, and a `revHi_acc` variant returns the ceiling.

### F3. `MainConfig.spec` is false: the read weights are stale

- **Principle:** soundness.
- **Code:** `MainConfig.lean:173`'s `mainMixOwn` says `mx.Read' ↦* […, W64 2]`. Since
  `a4c071c7dd`, `config.go:99` is `Read: []int{1, 1, 2, 1, 1, 0}`, so the postcondition names the
  wrong slice contents.
- **Affects:**
  - `Main.spec`'s proof, through `Run.spec`'s `runCfgOk`: with the true weights `readMixOk` holds
    (`w[5] = 0`, a positive weight exists, the sum is 6), so `Main.spec` is now provable in F1.
  - `Main.lean`'s header ("Not provable in F1 … `[1, 1, 2, 1, 1, 2]`") is now wrong.
- **Fix:** set the last read weight in `mainMixOwn` to `W64 0`. Rewrite `Main.lean`'s header to say
  `Main.spec` follows from `Run.spec` at `mainConfigM` (check `runCfgOk`'s other conjuncts there:
  threads 4 + 8 + 3, `limOf = 3`, `cblOf = 2`, 120 keys, `Ops = 12000`).

### F4. `Run` now calls `hashing`, which has no spec, and `Run`'s proof outline still has the old unconditional `hashes()`

- **Principle:** completeness (callees' specs) and the layout (one spec file per Go function).
- **Code:** `mvccfull.go:1566`: `if hashing(x.cfg.Mix.Read) { x.hashes() }`. Under `readMixOk`,
  `hashing` returns false (`config.go:153-161`), so the F1 proof needs exactly that fact. But:
  - there is no `Spec/.../mvccfull/hashing.lean`;
  - `etc/link-lean-first-mvccfull.txt`'s `Run:` line does not list `hashing`;
  - `Run.wp_proof` (`Proof/.../mvccfull/Run.lean`) takes no `wp_hashing`, and its outline still
    says "`x.hashes()`: no spec (F2)".
- **Stale text:** `Run.lean`'s header, "Not provable in F1 as the Go stands … unconditionally", is
  no longer true.
- **Fix:**
  - Add `hashing.spec`: pure, returning `!(∃ i < 6, 0 < w[i]) || (len w > 5 ∧ w[5] > 0)`, or
    directly `readMixOk (ws.map sint.Z) → false`.
  - Add it to `Run:`'s callees and `Run.wp_proof`'s hypotheses.
  - Rewrite the two texts.

### F5. `writerOwn` does not give the writer a reader token, yet `apply` and `endEpoch` need one

- **Principle:** completeness: the callers cannot establish the callee's precondition.
- **Specs:**
  - `runner.apply.spec` takes `1 ≤ nw` (`runner__apply.lean`).
  - `runner.endEpoch.spec` takes `mvccReaders E.ι.kv 1`.
  - `writerOwn` (`Writer.lean:574-604`) holds `nw` only through `lentOk`'s equation
    `nw + 2·Readers + 2·Streams = mvccReaderN` (`Writer.lean:563-566`).
- **The gap:** `write.spec`, `restart.spec` and `restore.spec` take no bound on `cfg.Readers` or
  `cfg.Streams`. `ThreadBoundLe GF 2^28` bounds the model's threads, not the configuration. So
  `nw = 0` is consistent with the precondition, and `write` cannot call `apply`, nor `restart`
  call `endEpoch`.
- **Fix:** add `1 ≤ nw` to `writerOwn`'s two member conjuncts. `Run` establishes it from `runCfgOk`:
  `2R + 4S + 3 ≤ 2^28` together with `mvccReaderN = rdStockN - 7`, which I take to be about `2^30`.
  I did not verify `rdStockN`'s value (`RdPool.lean:63`).

## Second tier

- **S1. Stale headers** (the Go changes of `a4c071c7dd`):
  - `runner__restore.lean`: "A Go change this needs (reported, not made): … capturing the store".
    It was made (`mvccfull.go:558`).
  - `Run.lean` and `Main.lean`: see F3 and F4.
  - The `Run` proof outline: see F4.
- **S2. `pick` has two spec files** (`pick.lean`, `pickW.lean`). The header says `pick.spec` will be
  a corollary of `pick.specW`, which is the principle's "a variant as a corollary". Keep a single
  `wp_proof`, and make sure `etc/gen-interface.py --layout` accepts `pickW.lean` (a spec file
  exposing only `<F>.spec`) or list it as a known violation.
- **S3. `checkStoreRange.spec`'s `ErrCompacted` branch** takes its `cmpHi` ceiling from `readQ`'s
  `crev` lower bound. That is fine. Its other branch, `checkRangeAt(…, cur = res.Rev, cmp = clo)`,
  relies on the `rev < clo` case being unreachable once mvcc did not return `ErrCompacted`
  (`rangeOutcomeC_lower`). This is sound: `clo ≤ σ.crev` is a premise. The header could say so in
  one line, since a reader of `mvccfull.go:1063` may think `clo` makes the check weaker.
- **S4. `recv_facts` and the -1 coverage.** `receive` covers watchers that are `stamped ∧
  ¬cancelled`, including ones already compacted (`mvccfull.go:1417`). The proof rests on
  `wsRecvOk` clause 3 holding of a live compacted watcher. That is vacuous under `onceUpToAll`, so
  it is fine, but only because `memberState` keeps `onceUpToAll`. Keep the dependency stated in
  `receive`'s header: the check would be unprovable if `onceUpToAll` were weakened.
- **S5. The watcher-count restriction is not enforced by the Go code.**
  - `watch` checks `regs.Load() >= Watchers`, then `regs.Add(1)` (`mvccfull.go:1286-1289`). The
    check and the increment are separate, and the member's streams run their registrars
    concurrently.
  - So a member can end up with `Watchers - 1 + Streams` watchers: over 512 when `Watchers = 511`
    (`normalize`) and `Streams ≥ 3`.
  - That reaches `issues/etcd-watch-compacted-resent.md`, which the package doc lists as excluded
    ("Fewer than 512 watchers per member").
  - The proof does not see this (`ctrInv` carries no value), and the resent compaction responses
    seem to pass `receive`'s checks. But the exclusion that `mvccfull.go:96` claims does not hold.
  - **Fix:** a CAS loop, or clamp `Watchers` to `512 - Streams` in `normalize`. Record it in
    `notes/`: a bug of this repository's tester, not of etcd.
- **S6. `endEpoch`, `complete` and `changesAt`.** `complete(m.rev)` calls `expect`, whose
  `changesAt` panics unless `r < len(h.changes)` (`mvccfull.go:222`). `endEpoch.spec` and
  `complete.spec` take `rv < Hlb.length`, and the writer has `histW`, so this is fine. The same
  check in `receive`'s `covered`/`expect` is discharged by `histOkM` (`P < |notifiedLog| ≤ |Hl|`).
  It is worth one line in `receive`'s header, since it is a panic and not a `check`.
- **S7. `open.spec`'s ghost halves.** It takes `memberCarry … σ b Hl ∗ ghostVar m.σ ½ σ ∗
  ghostVar m.bnd ½ b`, but `memberCarry` already contains one half of each, so the precondition
  holds both halves. That is intended (the invariant's half and the writer's), but say so: as
  written it reads like a duplicated conjunct.

## Checks: provable from the specs?

| Site | Check | Verdict |
|---|---|---|
| `receive` 1403 | revision ≤ `revHi` | **No as drafted** (F1) |
| `receive` 1407 | eventless revisions never decrease | yes: clause 5 with `eventlessOk` |
| `receive` 1413, 1418 | `-1` is progress; covers stamped, unmarked watchers | yes: clause 1; clause 3 with `k ≤ j` from the stamp; unmarked ⇒ `id ∉ C` ⇒ live (`regOk'`) |
| `receive` 1424 | watcher known | yes: clause 1 with `regOk'`'s first conjunct |
| `receive` 1426-1427 | compaction response | yes: clause 1 and `cmpHi_acc` |
| `receive` 1440-1441 | watcher's progress | yes: clause 4 with `floatLo ≤ lo`; clause 3 with `posOk` or the floating window; needs F2(a) for the floating window to exist |
| `receive` 1446-1463 | event order and fields | yes: clause 2 with `watchEvents_filtered_eq_expChs`, `posOk_advW`; re-anchoring at `r < w.rev` and keeping `hi+1` at `r ≥ w.rev` are both consistent with `expChs lo r = []` |
| `receive` 1476 | `checkStoreRange` | yes: `Rev = r - 1 ≥ 1` |
| `readOne` | `inBounds` ×2 per case | yes: `revLo_acc`/`cmpLo_acc`, `reader_au`, `revHi_acc`/`cmpHi_acc` (committed revisions: no F1 issue) |
| `readOne` | `checkRangeAt` | yes: exact `crev` from `Txn.FirstRev` |
| `readOne` | `Changes == 0` | yes |
| `checkStoreRange` | all | yes (S3) |
| `apply` and helpers | `checkHook` | yes: `hookPre`/`hookPost`; the hook runs in `Write`, `Grant`, `Revoke`'s deleter `Write`, `Compact` |
| `apply` and helpers | `tw.Rev`, `Put` / `DeleteRange` revisions | yes: `writeRev` |
| `apply` and helpers | `Changes` agreement | yes |
| `apply` and helpers | `end`'s history length and `Rev` | yes |
| `apply` and helpers | `compact`'s three outcomes | yes |
| `apply` and helpers | grant, revoke, `Lookup` | yes, through the lessor's specs: not re-verified here, `lessorW` |
| `act` | `Rev` in bounds (case 4) | yes |
| `act` | empty watch | yes, with `contractR` |
| `watch` | `err == nil`, fresh id | yes: open stream from the registrar's half of `cl`; `regOk'` |
| `watch` | the struct's invariant | **not** without F2 |
| `cancel` | first `Cancel` nil, second nil or `ErrWatcherNotExist` | yes |
| `endEpoch` | `Watch`/`Cancel` on a closed stream fail | yes: `S.closed`; error variables distinct (`errVars2.law`) |

## What is good

- **The incarnation and retirement design** (`memberInv` as `memberState ∨ ghostVar ret 1`,
  `incLive`, `incRd`, `memberCarry`) cleanly separates what survives a restart from the store.
  `memberInv_live`, `inc_retire` and `inc_alloc` are true as stated.
- **The registry with cancel marks** (`regOk'`, mark under `s.mu` before `Cancel`, `C` for the
  cancels issued) gives exactly the `w.live` that clause 3 needs.
- **The stamp argument** (`maxK_attained`, `stamp_ok`, registration only under `s.mu`) is right.
- **The floating window** (`wPosOk'`) handles a watcher from 0 in both re-anchoring cases, once F2
  is added.
- **The `restore` chain** checks out against `KV.Restore.contract`:
  - a prefix log and a `crev` that does not decrease (`runM_mono`);
  - a nil hook during `Restore`, then frozen;
  - the census for the old backend;
  - `revHi`/`cmpHi` raised before the call, so `memberState` holds throughout while readers and
    streams run.
- **`endCb`** abstracts `tw.End` and the revoke closure into one shape for `end`.
- **`readMixOk` with `pick.specW`** is a precise F1 scope premise. Its sum bound is exactly what
  keeps `pick`'s `total` from wrapping, and that is needed.

## Ranked by need of revision

1. **`memberState` / `readQ` / `memberCarry`** (`Members.lean`, `Readers.lean`, `Writer.lean`):
   F1 (the notified counter) and F2 (the `revLo`/`revHi` bounds). These block `receive` and
   `watch`.
2. **`MainConfig.spec`**: F3, false.
3. **`Run.spec` / `Run.wp_proof` / the link list**: F4 (the `hashing` spec, stale texts).
4. **`writerOwn`**: F5 (`1 ≤ nw`).
5. **`stream.receive.spec`, `stream.watch.spec`**: inherit F1/F2; headers to update (S4, S6).
6. **`runner.restore.spec`, `Main.spec`**: stale headers (S1, F3).
7. **`pick`/`pickW`** (S2); **`open.spec`** (S7); the `regs` race in the Go (S5).
8. Sound and complete as drafted, with only the inherited issues:
   - `runner.apply`, `begin`, `end`, `compact`
   - `runner.restart`, `runner.shut`, `runner.open` (but S7)
   - `runner.readOne`, `runner.checkStoreRange`
   - `stream.recvOne`, `stream.cancel`
   - `runner.startEpoch`/`endEpoch`, `runner.startReaders`/`stopReaders`
   - `streamInv`, `smuInv`, `watcherOk`, `regOk'`, `lentOk`, `leaseRecsOk`

## Uncertain (not verified)

- **The lessor's specs** (`lessorW`, `NewLessorR`, `Recover`) against `Grant`/`Revoke`'s
  hook runs and write-back tokens: taken on trust from the link list.
- **`rdStockN`'s value**, which F5's fix relies on.
- **Whether `KV.Compact.contract`'s `X`/`Y`** are instantiable to `True` for the tester's backend.
