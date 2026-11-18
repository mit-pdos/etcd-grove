# perheap handoff

## START HERE (2026-11-18, Scope revision 2 after review 1; HARD STOP for the second independent review)

- Branch `perheap-scope` off `lean` `49bd7924e6`, worktree `/shared/etcd-grove-incomingof`. Pin 6d365ee1a:
  `--packages=/shared/tmp/manifest-6d3.json`; `.lake/package-overrides.json` is that manifest's copy. Notes only.
- Done: Scope revision 1 (`dda8f5f7d8`); review 1 (`/shared/tmp/perheap/review-1.md`: B1, B2, M1, M2, SpecPlan,
  minors); **revision 2** (this commit): `notes/perheap-scope.md` answers every item (§9 maps item → answer):
  SpecPlan names (§2.0), the value pin in `descIs` (§2.2), B1/B2 texts (§3.3), restated chains (§3.3),
  `ctxBound` by token + C1a and one source of `ctxInMD` (§3.1), §4 completed, H0 hot fix (§5a), estimate
  8–10.5 weeks (§6), Q1–Q16 (§8); two Pending ledger entries (`notes/specs-only/ledger.md`, 2026-11-18:
  `ctxInMD_agree`, `errView`).
- Probes (not in the tree; `cd /shared/etcd-grove-incomingof && lake --packages=/shared/tmp/manifest-6d3.json env
  lean <file>`, no errors): `/shared/tmp/perheap/Probe.lean` (incoming, 13 s), `/shared/tmp/perheap/ProbeErr.lean`
  (errors: `descIsP_etcdError`, `errorfWrap_descIsP`, `IsStatusErrP.spec`, `listRead_step`; ~1 min).
- Next (after review 2 and the user's decisions): H0 on `lean` (§5a; its own branch; trusted text: stop before
  land), then step 0, step 1 (C1a first), … (§6).
- Open decisions: Q1–Q16 (§8); the user-level ones: Q2 (SpecPlan law), Q4/Q16 (SpecPlan vocabulary), Q8 (H0),
  Q9 (exported statements), Q11 (B1 text), Q12 (value pin).
- Pitfalls: `wp_start` strips `isPkgInit` conjuncts from the pattern, and unfolds the function when the
  triple is about the call itself (probe: use `iintro %Φ ⟨…⟩ HΦ`); `go.IntoValInj EtcdError` is not an
  instance today (R8); `status-history.md` append-only.

## History

- Revision 1 (2026-11-18, `dda8f5f7d8`): Scope written; Q1–Q10.
