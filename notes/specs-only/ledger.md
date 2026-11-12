# The spec plan's change ledger

A spec defect that a proof (or a review, a test, a user's critique) finds in a spec of the spec plan
(`SpecPlan/Spec/`), or a divergence between a real spec (`Spec/`) and the plan's, is recorded here
**before** either spec is edited (CLAUDE.md, "The spec plan and convergence"). The ledger is how the
plan stays the target the real proofs converge toward: no silent edits.

One entry per defect, newest first, in this format:

```
## <date>: <spec> -- <one-line defect>

- **Spec.** The file and the declaration (`SpecPlan/Spec/<pkg>/<fn>.lean`, `<fn>.spec`; or a law,
  `<pred>_<law>.spec`), and the real spec it corresponds to (`Spec/<pkg>/<fn>.lean`), if any.
- **Defect.** What is wrong: unprovable (false of the Go code), too weak for a user, too strong (a
  premise no caller can meet), not local, vacuous, ...
- **Evidence.** What shows it: the proof step that fails (file:line, the goal), the Go path (a
  panic, an error the post omits), the user or snippet (`examples/specreq/<alias>/`) it breaks, a
  failing test.
- **Proposed change.** The new statement (or its delta), and what else it moves: the snippets, the
  callers' and callees' specs and proof sketches, the open questions it touches.
- **Decision.** Pending / accepted (by whom, date; the commit that applied it) / rejected (why).
```

A change that needs the user's approval (a spec's statement at the client boundary, new
client-visible ghost state, a trust-boundary spec) says so in **Decision** and waits for it.

## 2026-11-12: backend's concurrent read -- an absent key may read as any entry

- **Spec.** `SpecPlan/Spec/go_etcd_io/etcd/server/v3/storage/backend/Api.lean`, `lingerSingle`
  (used by `concurrentReadTx.UnsafeRange.spec`); no real spec yet.
- **Defect.** Too weak for a user. `lingerSingle L k l` constrains `l` only when `L k = some v`; when
  the view has no `k`, the read may return one entry `(k, v')` with any `v'`, also for a key no image
  ever held. The lingering it models is narrower: the concurrent read's buffer copy may predate the
  last commit, so it may still hold a key that commit *deleted*, with the value the key had.
- **Evidence.** The snippet `backend/backend` (`examples/specreq/backend/backend.go`, `ReqBackend`'s
  readers): a `ConcurrentReadTx` visits the keys the writer's sessions put in pairs, and panics if it
  sees one key of a pair (first written as `session-atomic`, folded into `ReqBackend` the same day). Its "both present" half is provable (one `V` read atomically), its "both
  absent" half is not: either fresh key may read as present. mvcc's real read path (fresh revision
  keys, `kvstore_txn.go:126`) has the same need. The over-approximation's source:
  `nonissues/etcd-backend-read-buffer-cache-stale-after-commit.md`.
- **Proposed change.** Bound the lingering by the history: `l = []` or `l = [(k, v)]` with
  `I.ents b k = some v` for an image `I` of the backend's history no older than the copy (for
  example, the view's predecessor images since the last `bufVersion` bump), so a key no image held
  reads absent. Moves: `concurrentReadTx.UnsafeRange.spec`, `rdOrderL` (the same over ranges), and
  mvcc's range proof sketch (batch 4d), which may rely on today's weaker form only by not reading
  fresh keys.
- **Decision.** Pending (found by the backend snippets' rework; the user, 2026-11-12, asked for the
  snippets, not this change).
