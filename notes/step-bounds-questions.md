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

## Q2 (trusted text: a false axiom weakened) — 2026-11-22, approved by the user (applied before step 3)

`storage.OpenBackend.wp_proof` gives `backend.New`'s post without `New`'s receipt-bound premise, so it
is false at a receipt bound above `2 ^ 62` (since 2026-11-17) and, after step 2, above `2 ^ 60`
(ledger 2026-11-22). The fix: its spec takes `[ReceiptBoundLe GF (2 ^ 60)]` (and so does
`OpenSnapshotBackend`'s). This only weakens the axiom; no closed theorem changes (they fix
`receiptBound ≤ 2 ^ 48`). **Deferred from step 2, then applied** at the user's request (2026-11-22: "Please do that before step
3"), branch `openbackend-receipt`: the server's `srvSnapRO` and `applySnapshot` carry
`receiptBound ≤ 2 ^ 60` (in place of `wbInit - 6`, which it implies), and the walk passes it to
`OpenSnapshotBackend`.
## Q3 (step 3's Scope) — 2026-11-22, decided by the user: B (defer)

Step 3 (`K` receipts per request id) is deferred until the `net` swap has landed and
`etcd_dist_safe` is proved: the statements it would raise (`etcd_safe`, `k8s_safe`, leaseexpiryN's)
retire at the swap, and its proof work is in request-path files proving session 2 is changing
(`notes/step-bounds-plan.md`, step 3's Scope). Meanwhile: the `mvcc*` follow-up and `bboltfs` (1b).
