# perheap handoff

## START HERE (2026-11-18, Scope revision 3 after review 2; HARD STOP for a short independent check, then implementation)

- Branch `perheap-scope` off `lean` `49bd7924e6`, worktree `/shared/etcd-grove-incomingof` (do NOT touch its
  `.lake/build`: another agent copies it). Pin 6d365ee1a: `--packages=/shared/tmp/manifest-6d3.json`;
  `.lake/package-overrides.json` is that manifest's copy. Notes only so far.
- User decisions 2026-11-18: H0 is out (a separate fmt-soundness branch proves `ErrorfWrap`); **incoming first**:
  step 0 + the incoming part only, errors/outgoing back to the user afterwards.
- Done: revision 1 `dda8f5f7d8`, revision 2 `3b10ff2b93`, review 2 (`/shared/tmp/perheap/review-2.md`),
  **revision 3** (this commit): `notes/perheap-scope.md` Part I (step 0 + incoming, detailed), Part II (outline
  with review 2's MAJOR 1/3, m3 directions), H0 withdrawn, §12 maps review 2 item → answer; ledger entry 1
  reworded (`notes/specs-only/ledger.md`).
- Key revision-3 finding (§3): the auth-off theorems need the mode gate AND `libCtxOk` must keep an anonymous
  incoming part (`incomingCtxOk = ∃ md, ctxInMD ctx md`): the server's TLS fallback reads incoming metadata in
  every mode (`v3_server.go:1206-1216`, `store.go:1044`), and `NewAuthStore`'s trusted `isReqAuth` is stated under
  `libCtxOk` alone. Revision 2's removal would have made that trusted post false in Go.
- Probes (not in the tree; `cd /shared/etcd-grove-incomingof && lake --packages=/shared/tmp/manifest-6d3.json env
  lean <file>`, no errors, no sorry): `/shared/tmp/perheap/Probe.lean` (the two axioms as theorems),
  **`/shared/tmp/perheap/ProbeAuth.lean`** (store `AuthInfoFromCtx`: one spec by token with the gate, proved;
  the old form a corollary; auth-off instance needs no metadata), `ProbeErr.lean` (errors, Part II).
- Next, after the check and the coordinator's go: step 0 (§9), then C1a (the auth chain by token, 66 files:
  copy the probe's proof into `FreshCtx.lean`, delete the old `.spec` proof), then 1b, then C1 (land).
- Open decisions (§11): Q2 (SpecPlan agreement law), Q3 (`HasLC.hasLC` move), Q9 (three exported text
  changes), Q13, Q14 (changed), Q17 (new: the mode gate), Q15.
- Pitfalls: `wp_start` strips `isPkgInit` conjuncts and unfolds the call (use `iintro %Φ ⟨…⟩ HΦ` for
  corollaries); `ctxValue` is at `HasLC.hasLC` (the auth store's files are `{hlc}` today); in the probe, the `true`
  verdict excludes `.off` by `cases M` + `iunfold enabledVerdictFrom`; `status-history.md` append-only.
- Scan scripts: `/shared/tmp/perheap/scan4.py "<names>"` (exported statements naming them),
  `/shared/tmp/perheap/inc-defs.txt` (definitions mentioning the incoming vocabulary),
  `/shared/tmp/perheap/incoming-files.txt` (the 122 files).

## History

- Revision 2 (2026-11-18, `3b10ff2b93`): answered review 1 (B1, B2, M1, M2, SpecPlan names, H0 hot fix, Q1–Q16);
  errors probe `ProbeErr.lean`; two Pending ledger entries.
- Revision 1 (2026-11-18, `dda8f5f7d8`): Scope written; Q1–Q10.
