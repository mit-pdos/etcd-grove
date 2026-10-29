# Axiom soundness reviews

One report per review by the `axiom` skill (`.claude/skills/axiom/`): the axioms attacked, the
verdict, the counterexample (a Go program that panics and a Lean proof that it does not, from the
axioms) or every attack tried. The verdicts are also in `notes/audit.md`'s table.

| report | axioms | verdict |
|---|---|---|
| [bbolt](bbolt.md) | bbolt's key-value triples (`Spec/go_etcd_io/bbolt/*_kv.lean`), the predicate model (`InvBbolt.lean`), the `Options` rules, the package initializers | **refuted**: `ownWTxG_fill` (counterexample proved, 2026-10-29); `Put_kv` with `Commit_kv`/the cursor specs (by two earlier `issues/` reproductions) |
| [openbackend](openbackend.md) | `storage.OpenBackend` (and `OpenSnapshotBackend` through it), as restated on `backend-cmp` (`2e49ff1aa9`) | **refuted as documented** (counterexample proved, 2026-10-29): `dbOpensOk` is documented as an environment fact, but a `QuotaBackendBytes` above bbolt's `MaxMapSize` makes `Open` fail and `newBackend` panic in any environment; the restated `fkOwn γ (fkInit D)` (from `New`'s proved post) survives; **fixed** by `openMmapOk` in `openPre` (2026-10-29; on `lean` before the rest of `backend-cmp`) |
| [nocmpread](nocmpread.md) | `mvcc.kbNoCmp_metaNone` (`Proof/go_etcd_io/etcd/server/v3/storage/mvcc/NoCmpRead.lean`) | **refuted** (counterexample proved, 2026-10-29, on branch `axiom/kbnocmp-metanone`): the premise does not tie the reader to the backend (`L := False`), so one backend's no-compaction token says every reader finds no compaction, for good; Go's backend finds one after the store compacts. Its first proposed restatement is false too (direct `Meta` puts); **fixed on `backend-cmp`** by the compaction keys' tracked absence (the axiom deleted, `2e49ff1aa9`), not yet on `lean` |
| [etcd-noOtherRefusal](etcd-noOtherRefusal.md) | `etcd_noOtherRefusal` (F-S2 part 1; added 2026-10-29) | **survives** under the voter condition (as `etcd_noRefusal`); no auth-on path yields the three descriptions (2026-10-29) |
| [withtimeout-md](withtimeout-md.md) | `context.WithTimeoutBackgroundMd` (auth-5b, `189a0bfae4`): `WithTimeoutBackground` plus `outgoingOf ctx' = none` | **survives** every attack tried; caveat: `outgoingOf` is a function of values under nondeterministic allocation (shared with `AppendToOutgoingContext`) (2026-10-29) |
