# perheap handoff

## START HERE (2026-11-18, step 0 done (C0): `be6b6ca8c6`, lean merged `cd350b3c75`)

- Branch `perheap-scope` (worktree `/shared/etcd-grove-incomingof`), off `lean` `49bd7924e6`. Pin 6d365ee1a:
  `--packages=/shared/tmp/manifest-6d3.json`, `.lake/package-overrides.json` its copy. Builds only via
  `/shared/tmp/build-slot.sh` (`LEAN_NUM_THREADS=4`); lean-check `--max-open 2`, `--stop` before builds.
- Done: Scope revision 4 `43fe1dd94d` (review 3 folded in; decisions in `notes/perheap-questions.md`);
  **step 0** (this commit series): `metadata.transportMDRaw` (leaf, `hG`), `incomingHeld`, `ctxInMD`,
  `incomingCtxOk := ∃ md, ctxInMD`, `libCtxOk`/`libCtxOkC` at `HasLC.hasLC` (`Proof/context/LibKeys*.lean`);
  laws proved (`ctxInMD_{background,todo,from,cancel,timer,valueCtx,raw,valueAt}`, `v3rpc.ctxInMD_cc` in
  `SrvCtxWeakLaws.lean`); producers re-proved (`_of_nil` takes `hty`, `_of_valueWand` takes WithValue's
  transfer); `WithValue.spec` post gained the transfer (trusted text: independent attack
  `/shared/tmp/perheap/attack-step0.md`); `{hlc}`→`HasLC.hasLC` for FromIncomingContext, AuthInfoFromCtx/TLS,
  FreshCtx, FromIncomingWeak (Link files regenerated); SpecPlan `ctxInMD_agree` deleted (ledger entry 1
  accepted); Go test `examples/axiomcx/perheap` (passes).
- Still there until 1b (by design): `incomingOf`, its two axioms, `FromIncomingContext`'s `incomingOf` post,
  `WithValue`'s `incomingOf` equation. `auth.ctxToken` and `ctxBound` by token: C1a (moved from step 0).
- Verified at `be6b6ca8c6`: full build green (20480 jobs), all `etc/api` interfaces unchanged, `tcb-report --check`
  matches (892 axioms, 4 sorries). Post-merge full build (`cd350b3c75`): log `/shared/tmp/perheap/s/full-m1.log`.
- Next: C1a (Scope §4.2 incl. the second ring, §1 list; ~90 files, ~53k lines touched: several sessions), then 1b.
- Pitfalls: `ctxValue_other` needs `context.Assumptions`; `keyEqOk_of_ty_ne` is defined mid-`LibKeysChain`;
  WithValue's post patterns gained one slot after the `incomingOf` one (`#Hmd`).
- Scans: `/shared/tmp/perheap/closure2.py` (transitive closure; output `closure2.txt`), `scan4.py`,
  `scan-text.txt`/`scan-meaning.txt` (exported statements).

## History

- Scope revision 3 (2026-11-18, `a822edbc16`), START HERE then: probes `/shared/tmp/perheap/Probe.lean`,
  `ProbeAuth.lean` (the auth chain by token, proved), `ProbeErr.lean`.

- Revision 2 (2026-11-18, `3b10ff2b93`): answered review 1 (B1, B2, M1, M2, SpecPlan names, H0 hot fix, Q1–Q16);
  errors probe `ProbeErr.lean`; two Pending ledger entries.
- Revision 1 (2026-11-18, `dda8f5f7d8`): Scope written; Q1–Q10.
