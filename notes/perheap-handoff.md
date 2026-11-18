# perheap handoff

## START HERE (2026-11-18, Scope written; HARD STOP for the independent review)

- Branch `perheap-scope` off `lean` `49bd7924e6`, worktree `/shared/etcd-grove-incomingof` (shared with
  the landed `incomingof-scope`). Pin 6d365ee1a: `--packages=/shared/tmp/manifest-6d3.json`;
  `.lake/package-overrides.json` is that manifest's copy. Notes only: no Lean in the tree changed.
- Done: `notes/perheap-scope.md` (inventory §1, vocabulary §2, old → new §3, statements §4, Go §5,
  steps §6, risks §7, Q1-Q10 §8); STATUS entry; session row.
- Probe (not in the tree): `/shared/tmp/perheap/Probe.lean` proves both refuted `incomingOf` axioms'
  replacements as theorems over a defined `incomingIs`; check with
  `cd /shared/etcd-grove-incomingof && lake --packages=/shared/tmp/manifest-6d3.json env lean /shared/tmp/perheap/Probe.lean`
  (13 s, no errors). Declaration scan: `/shared/tmp/perheap/decls.py incomingOf outgoingOf errDesc statusCode`.
- Next (after the review and the user's decisions on Q1-Q10): step 0 (vocabulary), step 1 (incoming),
  checkpoint C1, land; then errors (C2a first: the server Range error path), outgoing, rest (§6).
- Open decisions: Q1 order (rec. incoming, errors, outgoing, rest), Q2 no agreement laws, Q3 `incomingIs`
  defined, Q4 one `errStatusIs`, Q5 delete `errDesc_etcdError`, Q6 derive `WithTimeoutBackgroundMd`,
  Q7 secondary family split, Q8 F1 record now / fix in step 2, Q9 exported text changes, Q10 review
  `clusterImageOk_restModel` separately.
- Pitfalls: proofs that rewrite `errDesc` of one value from two sources (R1) must carry `m` from the
  producer's `∃ m` to a call; if one truly needs agreement, stop (R2). The vocabulary sits under
  `InvGrpc`/`cache/v3/Base`: every phase rebuilds most of the tree (use the build slot).
