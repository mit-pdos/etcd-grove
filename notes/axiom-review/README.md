# Axiom soundness reviews

One report per review by the `axiom` skill (`.claude/skills/axiom/`): the axioms attacked, the
verdict, the counterexample (a Go program that panics and a Lean proof that it does not, from the
axioms) or every attack tried. The verdicts are also in `notes/audit.md`'s table.

| report | axioms | verdict |
|---|---|---|
| [bbolt](bbolt.md) | bbolt's key-value triples (`Spec/go_etcd_io/bbolt/*_kv.lean`), the predicate model (`InvBbolt.lean`), the `Options` rules, the package initializers | **refuted**: `ownWTxG_fill` (counterexample proved, 2026-10-29); `Put_kv` with `Commit_kv`/the cursor specs (by two earlier `issues/` reproductions) |
| [etcd-noOtherRefusal](etcd-noOtherRefusal.md) | `etcd_noOtherRefusal` (draft, F-S2 part 1) | **survives** under the voter condition (as `etcd_noRefusal`); no auth-on path yields the three descriptions (2026-10-29) |
