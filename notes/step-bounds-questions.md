# Questions for the user: the step-bound work (branch `step-bounds-backend`, claim issue #30)

## Q1 (hard stop: Scope of step 2; trusted text and top-level statements) — 2026-11-22

The backend's write-back budget limits every etcd statement to `2^40 - 11` steps. Raise it to `2^56`
and lower the hooks' cap `hookMax` from `2^16` to `4` (option A of `notes/step-bounds-plan.md`,
"Step 2: Scope")?

- What changes: `storage.OpenBackend`'s axiom keeps its text but its `P.Wf`/`wbInit` mean the new
  constants (its soundness argument, "post = `New`'s proved post", unchanged); `bootstrapContract`'s
  `∃ d, … d.P.Wf` asks `hookMax ≤ 4` (the server needs `≥ 3`); `etcd_robust`, `k8s_robust`,
  `leaseexpiryN` go to `2^48` steps, `mvccrand`/`mvccfull` likely to `2^48`.
- Options: A (recommended), B (keep the cap: the budget only reaches about `2^42`), C (budget per
  parameter: needs the same cap in `bootOk`).
- Recommendation: **A**. Depends on it: all of step 2's Draft. Not blocked meanwhile: nothing else
  (step 3's Scope comes after step 2).

**Answer (2026-11-22): option D** (one receipt per buffered entry, backend-internal; added to the plan
after the user's question why the per-put receipts had to come from callers: they need not, the put's
own steps provide them). **Approved by the user, 2026-11-22, via the jtassarotti session.** The cap
stays `2^16`; no top-level premise strengthened.

**Freeze for step 2 (2026-11-22): approved in advance by the user, via the jtassarotti session**: "If the
draft works, please proceed, do not wait for me." The first put proved with its receipt is the check;
if it works, Draft, Review and Prove go on without a stop. A trust-base growth (a new axiom) would
still stop.

## Q2 (trusted text: a false axiom weakened) — 2026-11-22, decided by the agent, pending the user

`storage.OpenBackend.wp_proof` gives `backend.New`'s post without `New`'s receipt-bound premise, so it
is false at a receipt bound above `2 ^ 62` (since 2026-11-17) and, after step 2, above `2 ^ 60`
(ledger 2026-11-22). The fix: its spec takes `[ReceiptBoundLe GF (2 ^ 60)]` (and so does
`OpenSnapshotBackend`'s). This only weakens the axiom; no closed theorem changes (they fix
`receiptBound ≤ 2 ^ 48`). **Deferred, not in step 2**: its caller, the server's `applySnapshot` walk
(`SnapApplyWalk.lean:338`), has no receipt bound in scope, so the fix threads one into the server's
proof (from `isServerM`, beside its thread bound, or a premise of `applySnapshot`'s spec), outside
step 2's backend-internal scope. Proposed as a follow-up of #30. Until then the axiom stays false
above `2 ^ 60` (it was above `2 ^ 62` before step 2), where no closed theorem reaches.
