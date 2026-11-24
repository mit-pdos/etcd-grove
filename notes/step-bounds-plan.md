# Robust step bounds: the plan (claim issue mit-pdos/etcd-grove#30)

Lean-first. The etcd examples' `Robust` statements bound the run at `2^40 - 11` Goose steps (about 18
minutes at 10^9 steps/s); every addition is a step. This plan raises them as far as the Go code
allows. Steps, as in #30:

1. **Done** (branch `step-bounds-mechanical`, enqueued 2026-11-22): `logkvrw` (`2^63`), `mvccrand`,
   `mvccfull` (`2^38`), `k8s/all` (`2^40 - 11`) off the thread-induced step bound.
   1b. **Done** (branch `step-bounds-bboltfs`, 2026-11-24): `bboltfs` at `2^63` steps, `2^30` threads,
   over Perennial's crash adequacy along the execution (perennial#690, `goose_crash_adequacy_below`,
   with the distributed forms the dsverify kits use).
2. **Done** (landed `0f20102d32`): the backend's buffered entries paid by time receipts; the etcd
   statements at `2^48`. 2b. `OpenBackend`'s receipt premise (Q2): landed `5d6a6e3f4e`.
3. **`K` time receipts per request id** (its Scope below, 2026-11-22: a hard stop for the user).
4. **The ceiling recorded**: `nonissues/etcd-request-id-suffix-wrap-dup-panic.md` (done), and
   `notes/robustness.md` once 2-3 land.

## Step 2: Scope (2026-11-22; a hard stop: the user's approval)

### What limits the etcd statements today

Two constants of the backend's proof, both internal to it:

- the write-back budget, `backend.wbInit = 2^40 - 1` tokens (`InvNew.lean:36`), with `bgOk`
  (`Model2.lean:407`): `ver + n + k < 2^40`, `e ≤ hookMax · (2^40 + 2)`;
- the hooks' cap in `BParams.Wf` (`Model2.lean:71`): `hookMax ≤ 2^16`.

`bgOk_bufBound` (`BatchLemmas.lean:315`) needs the buffers below `bufBound = 2^60`: `pend (< 2^58) +
hookMax · (budget + 2) + …`, so `budget · hookMax ≲ 2^58`. `bootstrapContract` (`InvBoot.lean:551`)
asks `N + 7 + bootWB ≤ wbInit` (`bootWB = 4`), and the adequacy proofs take `N = n` (`receiptBound =
n + 1`): hence `n + 12 ≤ 2^40` in `etcd_robust`, `k8s_robust`, `leaseexpiryN`; the `mvcc*` testers'
`receiptBound ≤ 2^38` comes from the same budget (`runner__open.lean:101`).

Behind it, `receiptBound GF ≤ 2^48` (`NewServer.spec`, the id generator: step 3) caps every etcd
statement at `2^48` whatever the budget.

### The change (options; decided: D, below)

**A.** Budget `2^56` (`wbInit = 2^56 - 1`, `bgOk`'s `2^40` → `2^56`), cap `hookMax ≤ 4`:
`4 · (2^56 + 2) + 2^58 + 2^58 < 2^60`. The server's hooks need `3 ≤ hookMax` (`hooksParams`,
`InvHooks.lean:52`: the consistent index's two puts and the `confState`'s); the testers use `0`.

- Proofs: `bgOk_bufBound`'s arithmetic redone (the one place with the literals `2^16`, `2^40`); every
  other `2^40` in the backend is the budget, a constant change (`CommitLemmas.lean:322,331`,
  `WritebackLemmas.lean:162-168`, `InvCommit.lean:82`, `NewAlloc.lean:77-80`, `InvNew.lean:105`,
  `NewKLaws.lean:25`); the clients' `pend + hookMax < 2^58` room arguments only get easier
  (`BackendBridge.lean`, `AuthRealWr.lean:1516`, `LessorApplyReal.lean:201`,
  `lessor__initAndRecover.lean:159`); the clients' `wbInit` inequalities hold for the larger budget
  (`unfold … ; omega`).
- **Trusted text whose meaning changes**: `storage.OpenBackend.wp_proof` (axiom), whose pre takes
  `P.Wf` and `bFresh` and whose post gives `newPostK` (`wbInit` tokens). Its soundness argument is
  unchanged: its post is exactly `backend.New`'s proved post, re-proved at the new constants.
- **Top-level statements**:
  - premise strengthened: `bootstrapContract`'s `bootOk` holds `∃ d, … d.P.Wf …`, so with A it
    requires a backend parameter with `hookMax ≤ 4` (still satisfiable: `3 ≤ hookMax` is all the
    server needs);
  - bounds raised, to the receipt bound: `etcd_robust`, `k8s_robust`, `leaseexpiryN` from
    `2^40 - 11` to `2^48` steps (`n + 1 ≤ 2^48`; their per-`n` boot premises then range over
    `n + 1 ≤ 2^48`), `mvccrand_robust`/`mvccfull_robust` from `2^38` to `2^48` (their `ReceiptBoundLe`
    raised to mvcc's own `2^48`, if nothing else in their proofs needs it lower: to check in Draft).

**B.** Keep the cap `2^16`: the budget can only reach about `2^42` (`2^16 · 2^42 = 2^58`). No
premise strengthened; etcd's bounds to about `2^42`, and step 3 would hit the backend again.

**C.** Make the budget depend on the parameter (`wbInit P = 2^58 / (hookMax + 1)`): no cap change,
but `bootOk`'s `d` is existential, so the examples could not discharge `N + 7 + bootWB ≤ wbInit d.P`
without a cap on `d.P.hookMax` in `bootOk` anyway: A in another form.

**D.** (2026-11-22, the user's question) One time receipt per buffered entry, inside the backend:
`putInternal`/`putSeq` (behind `UnsafePut`/`UnsafeSeqPut`, the hook's puts included) take a receipt at
one of their own Go steps (`wp_go_step_receipt`) and deposit it in the batch lock's invariant with the
entry (the put holds the lock); `bgOk` holds `⧗ m` for the buffers' `m` entries, so `m < receiptBound`
whatever `hookMax` and the commits since the last write-back; the write-back drops them. No caller
changes: the backend's specs gain an instance premise (`[ReceiptBoundLe GF (2^59)]`, met by every
caller, `≤ 2^48` today). The budget then bounds only the read buffer's `uint64` version and the commit
counters: about `2^62`. `hookMax`'s cap stays `2^16`; `bootstrapContract` unchanged; `OpenBackend`'s
text unchanged (its `wbInit` tokens more numerous). More proof work than A (the put/write-back proofs
and `bgOk` reworked), all backend-internal.

**Decision: D, approved by the user, 2026-11-22, via the jtassarotti session** (`notes/step-bounds-questions.md`, Q1).
Draft starts with one put proved with its receipt (that the receipt can be deposited with the entry),
before the rest.

### Draft (after approval)

Design as text first (`notes/spec-first-plan.md`, "Design before plumbing"): the old → new
statements above, then the backend's constants, `bgOk_bufBound`, the backend's build, the clients,
the examples' statements. Glue: none (constants). Review: a `spec-reviewer` on the changed trusted
text and the top-level statements; the `axiom` skill on `OpenBackend` (its meaning changed).

## Step 3 (outline; its Scope after step 2)

Each id costs its caller `K` receipts instead of one (`idutil.Generator.Next`'s spec takes `⧗ K`; its
three translated callers, `processInternalRaftRequestOnce`, `LeaseGrant`, `read.requestCurrentIndex`,
collect them from their own preceding Go instructions with `wp_go_step_receipt`), and
`receiptBound ≤ 2^48` becomes `≤ K · 2^48` where it comes from the generator (other `2^48` users are
conventions: `auth/Fuel.lean`, about `2^61`; mvcc's `2^48`, to check). `K` from a static count over the
translations: request path about 100-150 instructions before `Next`, `LeaseGrant` about 50-75 per id
(two ids), the read-index retry loop about 100-150 per iteration: `K = 2^6` safe. Then step 2's budget
must exceed `2^54`, which A gives. The lessor's receipt premises (#20 item 7, left to us by proving
session 2) are in this chain.

### Step 2: Draft and proof (2026-11-22, option D; freeze approved in advance by the user)

- **The check** (the first put with its receipt): `batchTxBuffered.UnsafePut` raises the buffers'
  receipt at its own write-buffer `put` resolution (`wp_apply +noauto` on `batchTx.UnsafePut`, then
  `wp_raise_receipt`). Passed; the rest followed without a stop.
- **Design as built**: `bufFit st m` (each bucket's read plus write buffer at most `m`) and the
  persistent `bufRc st` (`∃ m, ⧖ m ∗ ⌜bufFit st m ∧ receiptBound GF ≤ 2 ^ 60⌝`) in `batchGhostAt` and
  `batchGhostW` (`InvBackend.lean`, `InvBatch.lean`). The four step lemmas take the new state's
  `bufRc` (`batchGhost_step` restated as a wand); `UnsafePut`/`UnsafeSeqPut` raise it
  (`bufRc_grow`), `UnsafeDelete`/`UnsafeCreateBucket`/`UnsafeDeleteBucket` carry it (`bufRc_congr`),
  a commit (`bufRc_commitSt`, read buffer dropped) and a write-back (`bufRc_wbSt`, merge) keep it;
  `bufRc_bufBound` replaces `bgOk_bufBound` (deleted); `backend_init` allocates `⧖ 0`
  (`preceipt_zero`). `New`/`newBackend` take `[ReceiptBoundLe GF (2 ^ 60)]` (was `2 ^ 62`; bbolt's
  `Open` still gets its `2 ^ 62`). Budget: `wbInit = 2 ^ 62 - 1`, `bgOk`'s `ver + n + k < 2 ^ 62`.
  `hookMax`'s cap unchanged; `bootstrapContract` unchanged.
- **Statements**: `etcd_robust`, `k8s_robust`, `leaseexpiryN`'s at `2 ^ 48` steps (was `2 ^ 40 - 11`),
  their closed theorems at `n + 1 ≤ 2 ^ 48` (the receipt bound `NewServer` needs; the budget no
  longer binds), per-`n` premises over the same range.
- **Raised after step 2** (2026-11-23, branch `step-bounds-mvcc`): `mvccrand`/`mvccfull` at `2 ^ 48`
  steps: their `2 ^ 38` was a convention passed along their own specs (`ReceiptBoundLe GF (2 ^ 38)`,
  `Hn`), the limit being mvcc's `ReceiptBoundLe GF (2 ^ 48)`; `Ops < 2 ^ 38` (the program's
  operation count, `12000`) unchanged. Past `2 ^ 48` needs mvcc's specs (about 130 files). Before:
  `mvccrand`/`mvccfull` stayed at `2 ^ 38`: their own operation count is
  tied to `2 ^ 38` across about 30 spec files (`Ops < 2 ^ 38`, the store's receipt-paid supply); the
  budget no longer limits them.
- **Finding (trusted text, for the user)**: `storage.OpenBackend.wp_proof`'s spec takes no
  `ReceiptBoundLe` premise, though the `backend.New` its post stands for requires one (`2 ^ 62`
  before this change, `2 ^ 60` now). Harmless in every closed theorem (`receiptBound ≤ 2 ^ 48`), but
  the axiom claims `New`'s post for any receipt bound. Fix: add `[ReceiptBoundLe GF (2 ^ 60)]` to its
  spec (only weakens the axiom). Not done in this step: its caller, the server's `applySnapshot`
  walk, has no receipt bound in scope (follow-up; Q2). Done after it (2b, the user's request,
  2026-11-22, branch `openbackend-receipt`): `srvSnapRO`'s receipt conjunct, which the walk's write
  stock used (`receiptBound ≤ wbInit - 6`), is now `receiptBound ≤ 2 ^ 60` (its builders in
  `NewServer`/`NewServerR` prove it from `2 ^ 48`; it implies the old one), so is `applySnapshot`'s
  `hrbw`, and the walk passes it to `OpenSnapshotBackend` as the instance.
- **Build fix**: `mvcc/BackendBridge.lean`'s `batchLocked_dls` names the new `bufRc` conjunct.

## Step 3: Scope (2026-11-22; a hard stop: the user's approval)

### What changed since the outline

- **The statements it would raise are retiring.** kaashoek's coordinator (#30, 2026-11-22):
  `etcd_safe`, `k8s_safe` and `leaseexpiryN`'s closed theorem retire at the `net` swap (tagged for the
  paper), replaced by `etcd_dist_safe`/`k8s_dist_safe` (#24/#28: stated as drafts, not proved; their
  bound to be `2^48`, matching step 2). No new work on the retiring three. So step 3 has no proved
  top-level statement to raise today: its gain lands in the dist theorems once they are proved.
- **Hot files.** Proving session 2 (#18) is working in the request path's neighbourhood (members,
  `succ`, `bridge` after the swap).

### What limits the bound

`idutil.Generator.Next` (`Spec/.../idutil/Generator__Next.lean`) takes `idCred γi 1`, which is the pure
fact `receiptBound GF ≤ 2 ^ 48` (`Defs.lean:284`): the generator's invariant holds `⧗ k` for the `k`
ids issued and `Next` adds one from its own `AddUint64` step, so `k < receiptBound ≤ 2^48` and the
48-bit suffix does not wrap (the wrap is a real `dup id` panic: `nonissues/etcd-request-id-suffix-wrap-dup-panic.md`).
131 Spec/Proof files state `receiptBound GF ≤ 2 ^ 48` or `ReceiptBoundLe GF (2 ^ 48)`: the server and
its examples carry the generator's fact; some (mvcc, apply, auth's fuel) may use it for their own
counters, to audit.

### The change (options)

**A. `K` exclusive receipts per id** (the outline). `idCred γi n` becomes `⧗ (K · n)` (exclusive;
`K = 2^6`); the generator's invariant holds `⧗ (K · k)`, so `K · k < receiptBound ≤ K · 2^48`.
Every caller of `Next` (`processInternalRaftRequestOnce`, `LeaseGrant` (two ids), the read loop's
`requestCurrentIndex`) collects `K` tokens from its own counted Go steps since its last id
(`wp_go_step_receipt`, one per step), instead of the unbounded supply `□ |==> idCred ρ.ids 1` it uses
now (`InvStart`, `InvBuild`, `AuthCompRows`: `#HNR`). The static count (#30) says each path has
100-150 Go steps before `Next` (`LeaseGrant` 50-75 per id). Then every other `2^48` premise is
audited: raised to `K · 2^48` where it is the generator's, kept (with a separate argument) where it is
a counter of its own. Cost: the three callers' proofs (long: the request path's), a token-collecting
idiom (each harvested step is a tactic step), the 131 files' premises; trusted text: none, top-level
statements: the dist theorems' bound (kaashoek's files).

**B. Defer A until `etcd_dist_safe` is proved** (and the swap has landed): same work, done against
the statements that will exist, after the request path's current work settles. Nothing is lost
meanwhile: no closed theorem would show the gain before then.

**C. A only below the theorems now** (idutil and the three callers, the premises as they are): the
generator's proof and callers ready, the `2^48` premises raised later with the dist theorems.

**Decision: B, the user's (2026-11-22): "let's defer and do other things first".** The agent's
recommendation was B: A's gain (about `2^54` steps, 200+ days at 10^9 steps/s) appears in no proved
statement until the dist theorems are proved, and its proof work sits in files others are changing
now; C pays most of A's cost early and collides with them. In the meantime: the `mvcc*` follow-up
(`2^38`, step 2's note) and `bboltfs` (1b, Perennial) are independent of the swap.
