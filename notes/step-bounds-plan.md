# Robust step bounds: the plan (claim issue mit-pdos/etcd-grove#30)

Lean-first. The etcd examples' `Robust` statements bound the run at `2^40 - 11` Goose steps (about 18
minutes at 10^9 steps/s); every addition is a step. This plan raises them as far as the Go code
allows. Steps, as in #30:

1. **Done** (branch `step-bounds-mechanical`, enqueued 2026-11-22): `logkvrw` (`2^63`), `mvccrand`,
   `mvccfull` (`2^38`), `k8s/all` (`2^40 - 11`) off the thread-induced step bound.
   1b. `bboltfs`: needs crash adequacy along the execution (Perennial; open).
2. **The backend's write-back budget** (this Scope, below).
3. **`K` time receipts per request id** (after 2; its Scope later).
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
- **Not raised (follow-up)**: `mvccrand`/`mvccfull` stay at `2 ^ 38`: their own operation count is
  tied to `2 ^ 38` across about 30 spec files (`Ops < 2 ^ 38`, the store's receipt-paid supply); the
  budget no longer limits them.
- **Finding (trusted text, for the user)**: `storage.OpenBackend.wp_proof`'s spec takes no
  `ReceiptBoundLe` premise, though the `backend.New` its post stands for requires one (`2 ^ 62`
  before this change, `2 ^ 60` now). Harmless in every closed theorem (`receiptBound ≤ 2 ^ 48`), but
  the axiom claims `New`'s post for any receipt bound. Fix: add `[ReceiptBoundLe GF (2 ^ 60)]` to its
  spec (only weakens the axiom). Not done in this step: its caller, the server's `applySnapshot`
  walk, has no receipt bound in scope (follow-up; Q2).
- **Build fix**: `mvcc/BackendBridge.lean`'s `batchLocked_dls` names the new `bufRc` conjunct.
