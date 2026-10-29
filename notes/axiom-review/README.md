# Axiom soundness reviews

One report per review by the `axiom` skill (`.claude/skills/axiom/`): the axioms attacked, the
verdict, the counterexample (a Go program that panics and a Lean proof that it does not, from the
axioms) or every attack tried. The verdicts are also in `notes/audit.md`'s table.

| report | axioms | verdict |
|---|---|---|
| [bbolt](bbolt.md) | bbolt's key-value triples (`Spec/go_etcd_io/bbolt/*_kv.lean`), the predicate model (`InvBbolt.lean`), the `Options` rules, the package initializers | **refuted**: `ownWTxG_fill` (counterexample proved, 2026-10-29); `Put_kv` with `Commit_kv`/the cursor specs (by two earlier `issues/` reproductions) |
| [openbackend](openbackend.md) | `storage.OpenBackend` (and `OpenSnapshotBackend` through it), as restated on `backend-cmp` (`2e49ff1aa9`) | **refuted as documented** (counterexample proved, 2026-10-29): `dbOpensOk` is documented as an environment fact, but a `QuotaBackendBytes` above bbolt's `MaxMapSize` makes `Open` fail and `newBackend` panic in any environment; the restated `fkOwn γ (fkInit D)` (from `New`'s proved post) survives; **fixed** by `openMmapOk` in `openPre` (2026-10-29, `backend-cmp`) |
